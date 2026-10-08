"""Validate structured candidates and check generated declarations with Lean.

User and model text never becomes Lean source. Only the closed AST and recipe
allowlists below can affect the generated theorem.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ASSUMPTIONS = ["x > 0"]
RECIPES = {
    "bessel": "(try simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg, ← mul_assoc, BesselProofAgent.sign_cancel, BesselProofAgent.sign_mul_self, one_mul, neg_neg]) <;> ring",
    "ring": "ring",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREM = "BesselAgentCandidate.target"


class InputError(ValueError):
    """The input is outside the explicitly supported grammar."""


class NeedsConditions(InputError):
    """The supported domain needs to be stated explicitly."""


def _keys(value: Any, required: set[str], optional: set[str] | None = None) -> None:
    if not isinstance(value, dict):
        raise InputError("Expected a JSON object.")
    actual = set(value)
    if not required <= actual or actual - required - (optional or set()):
        raise InputError(f"Expected keys {sorted(required)}; got {sorted(actual)}.")


def _expr(node: Any, sort: str, depth: int = 0, budget: list[int] | None = None) -> None:
    if budget is None:
        budget = [500]
    budget[0] -= 1
    if depth > 20 or budget[0] < 0:
        raise InputError("Expression exceeds the supported size or depth.")
    if not isinstance(node, dict) or not isinstance(node.get("op"), str):
        raise InputError("Every expression must have an op field.")
    op = node["op"]
    if op == "int":
        _keys(node, {"op", "value"})
        if type(node["value"]) is not int or abs(node["value"]) > 1000:
            raise InputError("Integer literals must be between -1000 and 1000.")
    elif op == "var":
        _keys(node, {"op", "name"})
        expected = "n" if sort == "int" else "x"
        if node["name"] != expected:
            raise InputError(f"Expected variable {expected} in a {sort} expression.")
    elif op == "neg":
        _keys(node, {"op", "arg"})
        _expr(node["arg"], sort, depth + 1, budget)
    elif op in {"add", "sub", "mul"}:
        _keys(node, {"op", "args"})
        if not isinstance(node["args"], list) or len(node["args"]) != 2:
            raise InputError("Binary operations require exactly two arguments.")
        for arg in node["args"]:
            _expr(arg, sort, depth + 1, budget)
    elif op == "bessel_j" and sort == "complex":
        _keys(node, {"op", "order", "arg"})
        _expr(node["order"], "int", depth + 1, budget)
        _expr(node["arg"], "real", depth + 1, budget)
    elif op == "zpow" and sort == "complex":
        _keys(node, {"op", "base", "exponent"})
        _expr(node["base"], "complex", depth + 1, budget)
        _expr(node["exponent"], "int", depth + 1, budget)
    else:
        raise InputError(f"Unsupported operation {op!r} in a {sort} expression.")


def validate_request(data: Any, require_proof: bool = True) -> dict[str, Any]:
    required = {"schema_version", "assumptions", "lhs", "rhs"}
    _keys(data, required | ({"proof"} if require_proof else set()),
          set() if require_proof else {"proof"})
    if type(data["schema_version"]) is not int or data["schema_version"] != 1:
        raise InputError("schema_version must be 1.")
    if data["assumptions"] == []:
        raise NeedsConditions("State the supported assumption explicitly: x > 0.")
    if data["assumptions"] != ASSUMPTIONS:
        raise InputError('The only supported assumptions are ["x > 0"].')
    for name in ("lhs", "rhs"):
        _expr(data[name], "complex")
    if "proof" not in data:
        return data
    proof = data["proof"]
    if not isinstance(proof, dict):
        raise InputError("proof must be a JSON object.")
    if proof.get("mode") == "direct":
        _keys(proof, {"mode", "recipe"})
        _recipe(proof["recipe"])
    elif proof.get("mode") == "steps":
        _keys(proof, {"mode", "steps"})
        steps = proof["steps"]
        if not isinstance(steps, list) or not 1 <= len(steps) <= 20:
            raise InputError("A step proof requires 1 to 20 steps.")
        previous = data["lhs"]
        for step in steps:
            _keys(step, {"before", "after", "reason", "conditions", "recipe"})
            for name in ("before", "after"):
                _expr(step[name], "complex")
            if step["before"] != previous:
                raise InputError("Step endpoints must form one exact AST chain.")
            previous = step["after"]
            if not isinstance(step["reason"], str) or not 1 <= len(step["reason"]) <= 2000:
                raise InputError("Each proposed reason must be 1 to 2000 characters.")
            if step["conditions"] not in ([], ASSUMPTIONS):
                raise InputError("Steps can only use the fixed theorem assumptions.")
            _recipe(step["recipe"])
        if previous != data["rhs"]:
            raise InputError("The last step must end at the original target RHS.")
    else:
        raise InputError("proof.mode must be direct or steps.")
    return data


def _recipe(recipe: Any) -> None:
    if not isinstance(recipe, str) or recipe not in RECIPES:
        raise InputError(f"recipe must be one of {sorted(RECIPES)}.")


def lean_expr(node: dict[str, Any], sort: str = "complex") -> str:
    op = node["op"]
    if op == "int":
        return f"({node['value']} : { {'int': 'ℤ', 'real': 'ℝ', 'complex': 'ℂ'}[sort]})"
    if op == "var":
        return "(x : ℂ)" if sort == "complex" else node["name"]
    if op == "neg":
        return f"(-{lean_expr(node['arg'], sort)})"
    if op in {"add", "sub", "mul"}:
        left, right = (lean_expr(arg, sort) for arg in node["args"])
        return f"({left} { {'add': '+', 'sub': '-', 'mul': '*'}[op]} {right})"
    if op == "bessel_j":
        return f"(BesselProofAgent.J {lean_expr(node['order'], 'int')} {lean_expr(node['arg'], 'real')})"
    return f"({lean_expr(node['base'])} ^ {lean_expr(node['exponent'], 'int')})"


def display_expr(node: dict[str, Any]) -> str:
    op = node["op"]
    if op == "int":
        return str(node["value"])
    if op == "var":
        return node["name"]
    if op == "neg":
        return f"(-{display_expr(node['arg'])})"
    if op in {"add", "sub", "mul"}:
        left, right = (display_expr(arg) for arg in node["args"])
        return f"({left} { {'add': '+', 'sub': '-', 'mul': '·'}[op]} {right})"
    if op == "bessel_j":
        return f"J_{{{display_expr(node['order'])}}}({display_expr(node['arg'])})"
    return f"({display_expr(node['base'])})^({display_expr(node['exponent'])})"


def theorem_statement(data: dict[str, Any]) -> str:
    return f"∀ (n : ℤ) (x : ℝ), 0 < x → {lean_expr(data['lhs'])} = {lean_expr(data['rhs'])}"


def render_lean(data: dict[str, Any], kind: str = "proof") -> str:
    validate_request(data)
    if kind not in {"proof", "refutation"}:
        raise InputError("Unknown certificate kind.")
    lines = ["import BesselProofAgent", "", "namespace BesselAgentCandidate", ""]
    statement = theorem_statement(data)
    if kind == "refutation":
        lines += [f"theorem target : ¬ ({statement}) := by", "  intro h",
                  "  have hbad := h 0 1 (by norm_num)", "  first",
                  "  | have bad : (0 : ℂ) = 1 := by linear_combination hbad",
                  "    norm_num at bad",
                  "  | have bad : (0 : ℂ) = 1 := by linear_combination -hbad",
                  "    norm_num at bad", "  | norm_num at hbad"]
    elif data["proof"]["mode"] == "direct":
        lines += [f"theorem target : {statement} := by", "  intro n x hx",
                  "  " + RECIPES[data["proof"]["recipe"]]]
    else:
        steps = data["proof"]["steps"]
        for index, step in enumerate(steps):
            lines += [f"theorem step_{index + 1} (n : ℤ) (x : ℝ) (hx : 0 < x) :",
                      f"    {lean_expr(step['before'])} = {lean_expr(step['after'])} := by",
                      "  " + RECIPES[step["recipe"]], ""]
        lines += [f"theorem target : {statement} := by", "  intro n x hx", "  calc"]
        for index, step in enumerate(steps):
            left = lean_expr(step["before"]) if index == 0 else "_"
            lines += [f"    {left} = {lean_expr(step['after'])} := step_{index + 1} n x hx"]
    lines += ["", "end BesselAgentCandidate", "",
              '#eval IO.println "BESSEL_AUDIT_BEGIN"',
              f"#print axioms {THEOREM}",
              '#eval IO.println "BESSEL_AUDIT_END"', ""]
    return "\n".join(lines)


def audit_axioms(stdout: str) -> list[str]:
    if stdout.count("BESSEL_AUDIT_BEGIN") != 1 or stdout.count("BESSEL_AUDIT_END") != 1:
        raise InputError("Lean did not emit one complete dependency audit.")
    audit = stdout.split("BESSEL_AUDIT_BEGIN", 1)[1].split("BESSEL_AUDIT_END", 1)[0].strip()
    empty = f"'{THEOREM}' does not depend on any axioms"
    if audit == empty:
        return []
    match = re.fullmatch(r"'" + re.escape(THEOREM) + r"' depends on axioms:\s*\[([^\]]*)\]", audit)
    if not match:
        raise InputError("Lean's dependency audit had an unexpected format.")
    axioms = [item.strip() for item in match.group(1).split(",") if item.strip()]
    forbidden = set(axioms) - ALLOWED_AXIOMS
    if forbidden:
        raise InputError(f"Unapproved dependencies: {sorted(forbidden)}")
    return sorted(set(axioms))


def _sha(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def environment() -> dict[str, Any]:
    files = [ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "lakefile.lean",
             ROOT / "lakefile.toml", ROOT / "BesselProofAgent.lean"]
    files += sorted((ROOT / "BesselProofAgent").glob("**/*.lean"))
    return {str(path.relative_to(ROOT)): _sha(path.read_bytes()) for path in files if path.is_file()}


def _run_lean(path: Path, timeout: float) -> dict[str, Any]:
    try:
        process = subprocess.Popen(["lake", "env", "lean", str(path.resolve())], cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                   start_new_session=True)
    except OSError as exc:
        return {"accepted": False, "reason": "lean_unavailable", "stdout": "", "stderr": str(exc)}
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        return {"accepted": False, "reason": "timeout", "stdout": stdout, "stderr": stderr}
    outcome = {"accepted": False, "stdout": stdout, "stderr": stderr, "exit_code": process.returncode}
    if process.returncode != 0:
        return dict(outcome, reason="lean_rejected")
    try:
        axioms = audit_axioms(stdout)
    except InputError as exc:
        return dict(outcome, reason="audit_rejected", audit_error=str(exc))
    return dict(outcome, accepted=True, axioms=axioms)


def _save_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _report(data: dict[str, Any], result: dict[str, Any]) -> str:
    states = {"proved": "証明済み", "refuted": "反証済み", "unresolved": "未解決",
              "needs_conditions": "入力条件の確認待ち"}
    lines = [f"# {states[result['status']]}", "",
             "対象：すべての整数 n と正の実数 x に対する次の等式。", "",
             f"`{display_expr(data['lhs'])} = {display_expr(data['rhs'])}`", ""]
    if result["status"] == "proved":
        lines += ["固定した命題の証明と依存公理の監査が完了しました。", ""]
        if data["proof"]["mode"] == "steps":
            for index, step in enumerate(data["proof"]["steps"], 1):
                method = ("整数次数の符号関係と代数式の整理" if step["recipe"] == "bessel"
                          else "代数式の整理")
                lines += [f"{index}. `{display_expr(step['before'])} = {display_expr(step['after'])}`",
                          f"   {method}により、この等式をLeanで検査しました。対応する証明は `step_{index}` です。", ""]
            lines += ["以上の等式を連結し、元の左辺から右辺への証明を検査しました。", "",
                      "AIが提案した自由記述の理由は request.json に保存しています。上の説明は検査した構造化手順から生成しています。", ""]
    elif result["status"] == "refuted":
        lines += ["n = 0、x = 1 を用いて、元の全称命題の否定をLeanで証明しました。", ""]
    else:
        lines += ["今回の手順と制限時間で証明・反証を確定できませんでした。", "",
                  "詳細は result.json の各試行に記録しています。", ""]
    return "\n".join(lines)


def verify(data: Any, output_dir: Path, timeout: float = 60) -> dict[str, Any]:
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    if any(output_dir.iterdir()):
        raise InputError("Use an empty output directory to preserve earlier evidence.")
    try:
        validate_request(data)
    except NeedsConditions as exc:
        result = {"status": "needs_conditions", "reason": str(exc)}
        _save_json(output_dir / "result.json", result)
        return result
    except InputError as exc:
        result = {"status": "unresolved", "reason": "invalid_input", "detail": str(exc)}
        _save_json(output_dir / "result.json", result)
        return result
    _save_json(output_dir / "request.json", data)
    result: dict[str, Any] = {"status": "unresolved", "statement": theorem_statement(data),
                              "environment": environment(), "attempts": []}
    for kind in ("proof", "refutation"):
        source = render_lean(data, kind)
        path = output_dir / f"{kind}_attempt.lean"
        path.write_text(source, encoding="utf-8")
        attempt = _run_lean(path, timeout)
        result["attempts"].append(dict(attempt, kind=kind))
        if attempt["accepted"]:
            (output_dir / "certificate.lean").write_text(source, encoding="utf-8")
            result.update(status="proved" if kind == "proof" else "refuted",
                          certificate_kind=kind, certificate_sha256=_sha(source.encode()),
                          request_sha256=_sha((output_dir / "request.json").read_bytes()))
            break
        if attempt.get("reason") in {"lean_unavailable", "timeout", "audit_rejected"}:
            break
    _save_json(output_dir / "result.json", result)
    (output_dir / "report.md").write_text(_report(data, result), encoding="utf-8")
    return result


def replay(output_dir: Path, timeout: float = 60) -> dict[str, Any]:
    output_dir = Path(output_dir)
    data = load_json(output_dir / "request.json")
    result = load_json(output_dir / "result.json")
    validate_request(data)
    if result.get("status") not in {"proved", "refuted"}:
        raise InputError("This run has no accepted certificate to replay.")
    kind = "proof" if result["status"] == "proved" else "refutation"
    if result.get("certificate_kind") != kind:
        raise InputError("Certificate kind and recorded status disagree.")
    source = render_lean(data, kind)
    certificate = output_dir / "certificate.lean"
    if certificate.read_text(encoding="utf-8") != source:
        raise InputError("Saved certificate differs from the fixed AST/recipe translation.")
    if result.get("request_sha256") != _sha((output_dir / "request.json").read_bytes()):
        raise InputError("The saved request changed after verification.")
    if result.get("certificate_sha256") != _sha(source.encode()):
        raise InputError("The saved certificate digest changed.")
    if result.get("environment") != environment():
        raise InputError("The Lean configuration or local mathematical foundation changed.")
    attempt = _run_lean(certificate, timeout)
    return {"status": result["status"] if attempt["accepted"] else "unresolved",
            "replayed": attempt["accepted"], "verification": attempt}


def load_json(path: Path) -> Any:
    raw = Path(path).read_bytes()
    if len(raw) > 262144:
        raise InputError("Input JSON exceeds 256 KiB.")

    def unique_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise InputError(f"Duplicate JSON key: {key}")
            result[key] = value
        return result

    try:
        return json.loads(raw, object_pairs_hook=unique_keys)
    except (json.JSONDecodeError, UnicodeDecodeError, RecursionError) as exc:
        raise InputError(f"Invalid JSON: {exc}") from exc
