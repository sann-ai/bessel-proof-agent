"""Generate a restricted proof plan with an authenticated Codex CLI, then verify it."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

from .core import NeedsConditions, load_json, validate_request, verify

ROOT = Path(__file__).resolve().parents[1]


def obj(properties: dict) -> dict:
    return {"type": "object", "properties": properties,
            "required": list(properties), "additionalProperties": False}


def output_schema(route: str) -> dict:
    """Structured generation is separate from the verifier's strict parser."""
    recipe = {"type": "string", "enum": ["bessel", "ring"]}
    if route == "direct":
        return obj({"mode": {"type": "string", "enum": ["direct"]}, "recipe": recipe})
    ref = {"$ref": "#/$defs/expr"}
    expr = {"anyOf": [
        obj({"op": {"const": "int"}, "value": {"type": "integer"}}),
        obj({"op": {"const": "var"}, "name": {"type": "string", "enum": ["n", "x"]}}),
        obj({"op": {"const": "neg"}, "arg": ref}),
        obj({"op": {"type": "string", "enum": ["add", "sub", "mul"]},
             "args": {"type": "array", "items": ref, "minItems": 2, "maxItems": 2}}),
        obj({"op": {"const": "bessel_j"}, "order": ref, "arg": ref}),
        obj({"op": {"const": "zpow"}, "base": ref, "exponent": ref}),
    ]}
    step = obj({"before": ref, "after": ref, "reason": {"type": "string"},
                "conditions": {"type": "array", "items": {"type": "string", "enum": ["x > 0"]}},
                "recipe": recipe})
    result = obj({"mode": {"type": "string", "enum": ["steps"]},
                  "steps": {"type": "array", "items": step, "minItems": 1, "maxItems": 12}})
    result["$defs"] = {"expr": expr}
    return result


def make_prompt(target: dict, route: str, previous_error: str = "") -> str:
    # Only a validated expression tree, never a proposed theorem or Lean source, is sent.
    prompt = """Return one JSON proof plan matching the response schema. Do not use tools or edit files.
The program, not you, fixes the theorem: for every integer n and real x > 0,
the input lhs equals rhs, interpreted in Complex with Complex.besselJ.
Allowed recipes: bessel (integer Bessel argument/order sign lemmas, simplification,
then commutative-ring normalization), ring (commutative-ring normalization).
Allowed syntax: int, var x (expressions), var n (integer orders/exponents), neg,
add/sub/mul with two args, bessel_j with integer order and real arg,
zpow with a complex base and integer exponent. No arbitrary Lean source.
Known identities for integer n and real x: J_n(-x)=(-1)^n J_n(x),
J_{-n}(x)=(-1)^n J_n(x), J_{-n}(-x)=J_n(x).
The bessel recipe can normalize signs of Bessel order and argument.
For steps, start exactly at input lhs, finish exactly at input rhs, preserve
adjacent endpoints, and give each individual equality a valid recipe.
Use at least two meaningful equality steps when the expression has multiple
sign transformations. Give a concise Japanese reason for each step and only
conditions [\"x > 0\"]. State conditions directly without unnecessary negations.
"""
    prompt += f"Requested route: {route}\nFixed target JSON:\n{json.dumps(target, ensure_ascii=False, sort_keys=True)}\n"
    if previous_error:
        prompt += "Previous plan failed verification. Correct only the plan for the same target.\n" + previous_error[:5000]
    return prompt


def generate(target: dict, route: str, output_dir: Path, *, model: str | None = None,
             timeout: float = 240, attempts: int = 1) -> dict:
    validate_request(target, require_proof=False)
    target = dict(target)
    target.pop("proof", None)
    validate_request(target, require_proof=False)
    if shutil.which("codex") is None:
        raise ValueError("Codex CLI が見つかりません。保存された候補は verify で検査できます。")
    if output_dir.exists():
        raise ValueError("出力先が既に存在します。別のディレクトリを指定してください。")
    output_dir.mkdir(parents=True)
    (output_dir / "target.json").write_text(json.dumps(target, ensure_ascii=False, indent=2) + "\n")
    schema = output_schema(route)
    target_hash = hashlib.sha256(json.dumps(target, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    prior_error = ""
    result = {"status": "unresolved"}
    for attempt in range(1, attempts + 1):
        attempt_dir = output_dir / f"attempt-{attempt}"
        attempt_dir.mkdir()
        schema_path = attempt_dir / "schema.json"
        response_path = attempt_dir / "candidate.json"
        schema_path.write_text(json.dumps(schema, ensure_ascii=False, indent=2) + "\n")
        prompt = make_prompt(target, route, prior_error)
        (attempt_dir / "prompt.txt").write_text(prompt)
        cmd = ["codex", "exec", "--sandbox", "read-only", "--ephemeral", "--color", "never",
               "-c", 'model_reasoning_effort="ultra"', "--output-schema", str(schema_path.resolve()),
               "--output-last-message", str(response_path.resolve()), "-"]
        if model:
            cmd[2:2] = ["--model", model]
        started = time.monotonic()
        # A fresh empty cwd prevents accidental adoption of repository instructions.
        # CLI authentication and configured model remain owned by the installed CLI.
        with tempfile.TemporaryDirectory(prefix="bessel-generator-") as temp:
            cmd[2:2] = ["--skip-git-repo-check", "--cd", temp]
            process = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, text=True, cwd=ROOT,
                                       start_new_session=True)
            try:
                process.communicate(input=prompt, timeout=timeout)
            except subprocess.TimeoutExpired as exc:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
                meta = {"status": "unresolved", "reason": "AI generation timed out",
                        "target_sha256": target_hash, "route": route, "attempt": attempt}
                (attempt_dir / "generation.json").write_text(json.dumps(meta, indent=2) + "\n")
                raise ValueError("AI 生成が制限時間に達しました。") from exc
        metadata = {"provider": "codex-cli", "model_override": model, "reasoning_effort": "ultra",
                    "route": route, "target_sha256": target_hash, "attempt": attempt,
                    "returncode": process.returncode, "elapsed_seconds": round(time.monotonic() - started, 2)}
        # No raw CLI diagnostics are persisted: they may contain local account metadata.
        (attempt_dir / "generation.json").write_text(json.dumps(metadata, indent=2) + "\n")
        if process.returncode != 0 or not response_path.exists():
            raise ValueError("Codex CLI の生成が完了しませんでした。codex login status と利用可能なモデルを確認してください。")
        try:
            proof = load_json(response_path)
        except (OSError, json.JSONDecodeError) as exc:
            raise ValueError("AI の候補JSONを読み取れませんでした。") from exc
        if not isinstance(proof, dict) or proof.get("mode") != route:
            raise ValueError("AI の候補経路が指定と一致しません。")
        request = {**target, "proof": proof}
        # This is the exact original target plus an untrusted, validated plan.
        validate_request(request)
        (attempt_dir / "request.json").write_text(json.dumps(request, ensure_ascii=False, indent=2) + "\n")
        result = verify(request, attempt_dir / "verification", timeout=60)
        if result.get("status") in {"proved", "refuted"}:
            break
        prior_error = json.dumps(result, ensure_ascii=False)
    (output_dir / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description="既存Codex認証で候補を生成し、固定した命題をLeanで検証")
    parser.add_argument("input", type=Path)
    parser.add_argument("--route", choices=["direct", "steps"], required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--model")
    parser.add_argument("--timeout", type=float, default=240)
    parser.add_argument("--attempts", type=int, choices=range(1, 4), default=1)
    args = parser.parse_args()
    if not 0 < args.timeout <= 600:
        parser.error("--timeout must be positive and at most 600 seconds")
    try:
        result = generate(load_json(args.input), args.route, args.output,
                          model=args.model, timeout=args.timeout, attempts=args.attempts)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result.get("status") in {"proved", "refuted"} else 2
    except NeedsConditions as exc:
        print(json.dumps({"status": "needs_conditions", "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2
    except (ValueError, OSError) as exc:
        print(json.dumps({"status": "unresolved", "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
