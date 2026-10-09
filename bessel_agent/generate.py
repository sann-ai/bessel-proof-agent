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

from .core import RECIPES, NeedsConditions, condition_labels, load_json, validate_request, verify

ROOT = Path(__file__).resolve().parents[1]


def obj(properties: dict) -> dict:
    return {"type": "object", "properties": properties,
            "required": list(properties), "additionalProperties": False}


def output_schema(route: str, target: dict | None = None) -> dict:
    """Structured generation is separate from the verifier's strict parser."""
    conditions = condition_labels(target or {})
    recipe = {"type": "string", "enum": list(RECIPES)}
    if route == "direct":
        return obj({"mode": {"type": "string", "enum": ["direct"]}, "recipe": recipe})
    ref = {"$ref": "#/$defs/expr"}
    expr = {"anyOf": [
        obj({"op": {"const": "int"}, "value": {"type": "integer"}}),
        obj({"op": {"const": "var"}, "name": {"type": "string", "enum": ["n", "x"]}}),
        obj({"op": {"const": "neg"}, "arg": ref}),
        obj({"op": {"type": "string", "enum": ["add", "sub", "mul", "div"]},
             "args": {"type": "array", "items": ref, "minItems": 2, "maxItems": 2}}),
        obj({"op": {"const": "bessel_j"}, "order": ref, "arg": ref}),
        obj({"op": {"const": "zpow"}, "base": ref, "exponent": ref}),
        obj({"op": {"const": "pow"}, "base": ref, "exponent": {"type": "integer", "minimum": 0, "maximum": 12}}),
        obj({"op": {"const": "int_cast"}, "arg": ref}),
        obj({"op": {"const": "rational"}, "numerator": {"type": "integer"}, "denominator": {"type": "integer", "minimum": 1}}),
        obj({"op": {"const": "real_rpow"}, "base": ref, "exponent": ref}),
        obj({"op": {"const": "sqrt"}, "arg": ref}),
        obj({"op": {"const": "deriv"}, "arg": ref}),
        obj({"op": {"const": "integral"}, "arg": ref, "lower": ref, "upper": ref}),
    ]}
    step = obj({"before": ref, "after": ref, "reason": {"type": "string"},
                "conditions": {"type": "array", "items": {"type": "string", "enum": conditions}},
                "recipe": recipe})
    result = obj({"mode": {"type": "string", "enum": ["steps"]},
                  "steps": {"type": "array", "items": step, "minItems": 1, "maxItems": 12}})
    result["$defs"] = {"expr": expr}
    return result


def make_prompt(target: dict, route: str, previous_error: str = "") -> str:
    # Only a validated expression tree, never a proposed theorem or Lean source, is sent.
    prompt = """Return one JSON proof plan matching the response schema. Do not use tools or edit files.
The program fixes the theorem: for every integer n and real x satisfying the
exact input assumptions and extra_conditions, lhs equals rhs in Complex with
Complex.besselJ. Do not add, remove, or strengthen conditions.
Allowed recipes: bessel (integer Bessel argument/order sign lemmas, simplification,
then commutative-ring normalization), ring (commutative-ring normalization),
field (rational algebra using the verified nonzero denominator conditions),
recurrence (the three-term Bessel recurrence and field algebra),
calculus (verified Bessel derivative/integral formulas and field algebra),
power (positive-real rational powers and square-root identities),
conditions (use the explicitly supplied scalar comparisons/equalities).
Only select a recipe listed in the response schema.
Allowed syntax: int, var x (expressions), var n (integer orders/exponents), neg,
add/sub/mul/div with two args, bessel_j with integer or fixed rational order and real arg,
int_cast embeds an integer expression as a complex coefficient. pow has integer
exponent 0..12; zpow has integer-expression exponent and a statically nonzero base.
Division likewise requires a statically nonzero denominator, such as positive x.
rational has numerator and positive denominator, in lowest terms, and is allowed
only in a Bessel order or real_rpow exponent. Write fractional coefficients as
div of int expressions (for example 1/2 uses int 1 divided by int 2). Noninteger
Bessel orders require a positive argument. deriv(arg) differentiates with respect
to x; integral(arg,lower,upper) binds x inside arg. No arbitrary Lean source.
Known identities for integer n and real x: J_n(-x)=(-1)^n J_n(x),
J_{-n}(x)=(-1)^n J_n(x), J_{-n}(-x)=J_n(x).
For x>0: J_{n-1}(x)+J_{n+1}(x)=(2n/x)J_n(x).
This recurrence also holds for a fixed rational order.
Derivative/integral order reflection follows the same (-1)^n factor.
The integral of the derivative of integer-order J_n from a to b is J_n(b)-J_n(a).
For positive x, D(J_n(x))=(n/x)*J_n(x)-J_{n+1}(x)
=(J_{n-1}(x)-J_{n+1}(x))/2, and integral(t*J_0(t),0,x)=x*J_1(x).
The adjacent-order derivative formula also holds for any fixed rational order a.
For a rational-order derivative, use (a/x)*J_a(x)-J_(a+1)(x) directly: this is
the supported calculus rewrite. When the target adds a derivative and an integral,
rewrite the derivative in one step and the integral in a separate step.
For x>0, integral(t^(-1/2),0,x)=2*sqrt(x), and the calculus recipe proves it.
The calculus recipe also proves the integrable Bessel singularity
integral(t^(1/4)*J_(-3/4)(t),0,x)=x^(1/4)*J_(1/4)(x).
For sums of an integral and algebraic terms, evaluate the integral in one step
and collect the terms in a separate ring step.
For positive endpoints l,u, the integral of (a/t)*J_a(t)-J_(a+1)(t) is J_a(u)-J_a(l).
real_rpow(base, exponent) means Real.rpow on a positive real base, cast to Complex;
its exponent is an int or reduced rational AST. sqrt(arg) is the positive real square root.
extra_conditions entries {op: "x_gt", value: k} mean x > k. The compare form
has variable n or x, relation gt/ge/lt/le/eq/ne, and value {numerator:p,denominator:q}.
These are exact comparisons with a rational constant; retain every given condition.
These outer conditions never apply to the bound variable inside an integral.
The bessel recipe can normalize signs of Bessel order and argument.
For steps, start exactly at input lhs, finish exactly at input rhs, preserve
adjacent endpoints, and give each individual equality a valid recipe.
Use at least two meaningful equality steps when the expression has multiple
sign transformations. Give a concise Japanese reason for each step and only
conditions drawn from the exact target assumptions, such as [\"x > 0\", \"x > 1\"].
State conditions directly without unnecessary negations.
"""
    prompt += f"Requested route: {route}\nFixed target JSON:\n{json.dumps(target, ensure_ascii=False, sort_keys=True)}\n"
    if previous_error:
        prompt += "Previous plan failed verification. Correct only the plan for the same target.\n" + previous_error[:5000]
    return prompt


def generate(target: dict, route: str, output_dir: Path, *, model: str | None = None,
             timeout: float = 240, attempts: int = 1, archive: bool = False,
             archive_dir: Path | None = None, original_input: str | None = None) -> dict:
    """Optionally search and append to the user's separate proof archive."""
    if archive_dir is not None and not archive:
        raise ValueError("--archive-dir requires --archive.")
    context: dict = {}
    original_input = original_input if original_input is not None else json.dumps(target, ensure_ascii=False)
    archive_root = None
    if archive:
        from .archive import resolve_archive_root
        archive_root = resolve_archive_root(archive_dir)
    try:
        return _generate(target, route, Path(output_dir), model=model, timeout=timeout,
                         attempts=attempts, archive_root=archive_root, context=context,
                         original_input=original_input)
    except (ValueError, OSError) as exc:
        if archive_root is not None:
            from .archive import register_failure
            failure = {"status": "needs_conditions" if isinstance(exc, NeedsConditions) else "unresolved",
                       "reason": "generation_or_input_error", "detail": str(exc)}
            fixed_target = dict(target) if isinstance(target, dict) else target
            if isinstance(fixed_target, dict):
                fixed_target.pop("proof", None)
            register_failure(failure, archive_root, original_input=original_input,
                             request=fixed_target, candidate=context.get("candidate"))
        raise


def _generate(target: dict, route: str, output_dir: Path, *, model: str | None,
              timeout: float, attempts: int, archive_root: Path | None, context: dict,
              original_input: str) -> dict:
    validate_request(target, require_proof=False)
    target = dict(target)
    target.pop("proof", None)
    validate_request(target, require_proof=False)
    if output_dir.exists():
        raise ValueError("出力先が既に存在します。別のディレクトリを指定してください。")
    output_dir.mkdir(parents=True)
    (output_dir / "target.json").write_text(json.dumps(target, ensure_ascii=False, indent=2) + "\n")
    if target["schema_version"] == 2:
        request = {**target, "proof": {"mode": "diagnostic"}}
        result = verify(request, output_dir / "verification", timeout=min(timeout, 60))
        result = {**result, "generation": {"ai_called": False, "requested_route": route,
                   "reason": "version_2_uses_scoped_diagnostics"}}
        if archive_root is not None:
            from .archive import register_verification
            record = register_verification(output_dir / "verification", archive_root,
                                           original_input=original_input, request=request,
                                           provenance={"provider": "diagnostic", "ai_called": False,
                                                       "requested_route": route})
            result["archive_id"] = record["id"]
        (output_dir / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
        return result
    if archive_root is not None:
        from .archive import find_exact, register_verification, replay_record
        skipped = []
        for record in find_exact(target, archive_root):
            candidate = record.get("candidate")
            if record["status"] not in {"proved", "refuted"} or not isinstance(candidate, dict) or candidate.get("mode") != route:
                continue
            try:
                checked = replay_record(record["id"], archive_root, timeout=60)
            except (ValueError, OSError) as exc:
                skipped.append({"record_id": record["id"], "reason": str(exc)})
                continue
            if not checked.get("replayed"):
                skipped.append({"record_id": record["id"], "reason": "Replay did not accept the certificate."})
                continue
            request = {**target, "proof": candidate}
            result = verify(request, output_dir / "reuse" / "verification", timeout=60)
            provenance = {"provider": "archive", "reused_record_id": record["id"],
                          "route": route, "ai_called": False}
            registered = register_verification(output_dir / "reuse" / "verification", archive_root,
                                               original_input=original_input,
                                               provenance=provenance)
            result["archive_record_id"] = registered["id"]
            result["reuse"] = provenance
            (output_dir / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
            return result
        if skipped:
            (output_dir / "archive-reuse-skipped.json").write_text(json.dumps(skipped, ensure_ascii=False, indent=2) + "\n")
    if shutil.which("codex") is None:
        raise ValueError("Codex CLI が見つかりません。保存された候補は verify で検査できます。")
    schema = output_schema(route, target)
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
        context["candidate"] = proof
        if not isinstance(proof, dict) or proof.get("mode") != route:
            raise ValueError("AI の候補経路が指定と一致しません。")
        request = {**target, "proof": proof}
        # This is the exact original target plus an untrusted, validated plan.
        validate_request(request)
        (attempt_dir / "request.json").write_text(json.dumps(request, ensure_ascii=False, indent=2) + "\n")
        result = verify(request, attempt_dir / "verification", timeout=60)
        if archive_root is not None:
            registered = register_verification(attempt_dir / "verification", archive_root,
                                               original_input=original_input,
                                               provenance=metadata)
            result["archive_record_id"] = registered["id"]
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
    parser.add_argument("--archive", action="store_true", help="Search exact verified results, then append this attempt to your archive.")
    parser.add_argument("--archive-dir", type=Path, help="Override the separate user archive directory; requires --archive.")
    args = parser.parse_args()
    if not 0 < args.timeout <= 600:
        parser.error("--timeout must be positive and at most 600 seconds")
    if args.archive_dir is not None and not args.archive:
        parser.error("--archive-dir requires --archive")
    original_input = None
    started_generation = False
    try:
        original_input = args.input.read_text(encoding="utf-8")
        target = load_json(args.input)
        started_generation = True
        result = generate(target, args.route, args.output,
                          model=args.model, timeout=args.timeout, attempts=args.attempts,
                          archive=args.archive, archive_dir=args.archive_dir,
                          original_input=original_input)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result.get("status") in {"proved", "refuted"} else 2
    except NeedsConditions as exc:
        print(json.dumps({"status": "needs_conditions", "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2
    except (ValueError, OSError) as exc:
        if args.archive and not started_generation:
            from .archive import register_failure
            try:
                register_failure({"status": "unresolved", "reason": "input_error", "detail": str(exc)},
                                 args.archive_dir, original_input=original_input)
            except (ValueError, OSError) as archive_error:
                print(json.dumps({"archive_error": str(archive_error)}, ensure_ascii=False), file=sys.stderr)
        print(json.dumps({"status": "unresolved", "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
