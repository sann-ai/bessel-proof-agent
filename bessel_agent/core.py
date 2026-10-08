"""Validate structured candidates and check generated declarations with Lean.

User and model text never becomes Lean source. Only the closed AST and recipe
allowlists below can affect the generated theorem.
"""

from __future__ import annotations

import hashlib
from fractions import Fraction
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
    "conditions": "first | simp_all | (norm_cast <;> (first | omega | linarith))",
    "bessel": "(try simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg, ← mul_assoc, BesselProofAgent.sign_cancel, BesselProofAgent.sign_mul_self, one_mul, neg_neg]) <;> ring",
    "ring": "ring",
    "power": "norm_num",
    "field": "have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)\nfield_simp [hxC] <;> ring",
    "recurrence": "have hrec := BesselProofAgent.recurrence n x hx\nfirst\n| linear_combination hrec\n| linear_combination -hrec\n| (try simp only [hrec]) <;> ring",
    "calculus": "have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)\nsolve\n| (try simp only [BesselProofAgent.deriv_order_neg, BesselProofAgent.integral_order_neg_raw, BesselProofAgent.integral_deriv_J, BesselProofAgent.deriv_J_symmetric n x hx, BesselProofAgent.integral_mul_J_zero x hx]) <;> (first | ring | (field_simp [hxC] <;> ring))\n| (try simp only [BesselProofAgent.deriv_order_neg, BesselProofAgent.integral_order_neg_raw, BesselProofAgent.integral_deriv_J, BesselProofAgent.deriv_J n x hx, BesselProofAgent.integral_mul_J_zero x hx]) <;> (first | ring | (field_simp [hxC] <;> ring))",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREM = "BesselAgentCandidate.target"


class InputError(ValueError):
    """The input is outside the explicitly supported grammar."""


class NeedsConditions(InputError):
    """The supported domain needs to be stated explicitly."""


def _constant(node: dict[str, Any]) -> Fraction | None:
    """Evaluate a small literal-only expression for domain checks."""
    op = node["op"]
    if op == "int":
        return Fraction(node["value"])
    if op == "int_cast":
        return _constant(node["arg"])
    if op == "neg":
        value = _constant(node["arg"])
        return -value if value is not None else None
    if op in {"add", "sub", "mul", "div"}:
        a, b = (_constant(arg) for arg in node["args"])
        if a is None or b is None or (op == "div" and b == 0):
            return None
        return {"add": lambda: a + b, "sub": lambda: a - b,
                "mul": lambda: a * b, "div": lambda: a / b}[op]()
    return None


def _affine(node: dict[str, Any], variable: str = "x") -> tuple[Fraction, Fraction] | None:
    value = _constant(node)
    if value is not None:
        return Fraction(0), value
    op = node["op"]
    if op == "var" and node["name"] == variable:
        return Fraction(1), Fraction(0)
    if op == "int_cast":
        return _affine(node["arg"], variable)
    if op == "pow" and node["exponent"] in {0, 1}:
        return (Fraction(0), Fraction(1)) if node["exponent"] == 0 else _affine(node["base"], variable)
    if op == "zpow" and node["exponent"] in ({"op": "int", "value": 0}, {"op": "int", "value": 1}):
        return (Fraction(0), Fraction(1)) if node["exponent"]["value"] == 0 else _affine(node["base"], variable)
    if op == "neg":
        value = _affine(node["arg"], variable)
        return (-value[0], -value[1]) if value is not None else None
    if op in {"add", "sub", "mul", "div"}:
        left, right = (_affine(arg, variable) for arg in node["args"])
        if left is None or right is None:
            return None
        a, b = left
        c, d = right
        if op == "add":
            return a + c, b + d
        if op == "sub":
            return a - c, b - d
        if op == "mul" and a * c == 0:
            return a * d + b * c, b * d
        if op == "div" and c == 0 and d != 0:
            return a / d, b / d
    return None


def _positive(node: dict[str, Any], lower_bound: Any = 0) -> bool:
    value = _constant(node)
    if value is not None:
        return value > 0
    if isinstance(lower_bound, dict):
        for variable in ("x", "n"):
            affine = _affine(node, variable)
            if affine is not None:
                a, b = affine
                lower, upper, excluded = lower_bound[variable]
                edge = lower if a > 0 else upper
                if a == 0:
                    return b > 0
                if edge is not None:
                    value = a * edge[0] + b
                    if value > 0 or (value == 0 and (edge[1] or edge[0] in excluded)):
                        return True
    else:
        affine = _affine(node)
        if affine is not None:
            a, b = affine
            return (a > 0 and a * lower_bound + b >= 0) or (a == 0 and b > 0)
    op = node["op"]
    if op == "var":
        return node["name"] == "x"
    if op in {"add", "mul", "div"}:
        return all(_positive(arg, lower_bound) for arg in node["args"])
    if op in {"pow", "zpow", "real_rpow"}:
        return _positive(node["base"], lower_bound)
    if op == "sqrt":
        return _positive(node["arg"], lower_bound)
    return False


def _nonzero(node: dict[str, Any], lower_bound: Any = 0) -> bool:
    value = _constant(node)
    if value is not None:
        return value != 0
    if _positive(node, lower_bound) or _positive({"op": "neg", "arg": node}, lower_bound):
        return True
    if isinstance(lower_bound, dict):
        for variable in ("x", "n"):
            affine = _affine(node, variable)
            if affine is not None and affine[0] != 0 and -affine[1] / affine[0] in lower_bound[variable][2]:
                return True
    op = node["op"]
    if op == "neg":
        return _nonzero(node["arg"], lower_bound)
    if op in {"mul", "div"}:
        return all(_nonzero(arg, lower_bound) for arg in node["args"])
    if op in {"pow", "zpow", "real_rpow"}:
        return _nonzero(node["base"], lower_bound) or (op == "pow" and node["exponent"] == 0)
    if op == "sqrt":
        return _positive(node["arg"], lower_bound)
    return False


def _entire_integrand(node: dict[str, Any]) -> bool:
    """The initial integral grammar has no singularities on any real interval."""
    op = node["op"]
    if op in {"int", "var", "int_cast"}:
        return True
    if op in {"neg", "deriv"}:
        return _entire_integrand(node["arg"])
    if op in {"add", "sub", "mul"}:
        return all(_entire_integrand(arg) for arg in node["args"])
    if op == "div":
        denominator = _constant(node["args"][1])
        return denominator is not None and denominator != 0 and _entire_integrand(node["args"][0])
    if op == "pow":
        return _entire_integrand(node["base"])
    if op == "zpow":
        base = _constant(node["base"])
        return base is not None and base != 0
    if op == "bessel_j":
        return node["order"]["op"] != "rational" and _entire_integrand(node["arg"])
    return False


def _keys(value: Any, required: set[str], optional: set[str] | None = None) -> None:
    if not isinstance(value, dict):
        raise InputError("Expected a JSON object.")
    actual = set(value)
    if not required <= actual or actual - required - (optional or set()):
        raise InputError(f"Expected keys {sorted(required)}; got {sorted(actual)}.")


def _fixed_exponent(node: Any) -> None:
    if isinstance(node, dict) and node.get("op") == "int":
        _expr(node, "int")
        return
    _keys(node, {"op", "numerator", "denominator"})
    if node["op"] != "rational":
        raise InputError("A real power requires a fixed integer or rational exponent.")
    p, q = node["numerator"], node["denominator"]
    if type(p) is not int or type(q) is not int or abs(p) > 1000 or not 2 <= q <= 1000:
        raise InputError("Use exact integer fields for a fixed rational exponent.")
    reduced = Fraction(p, q)
    if reduced.numerator != p or reduced.denominator != q:
        raise InputError("A rational exponent must be reduced and noninteger.")


def _singular_half_integral(node: dict[str, Any]) -> bool:
    return (node["lower"] == {"op": "int", "value": 0}
            and node["upper"] == {"op": "var", "name": "x"}
            and node["arg"] == {"op": "real_rpow", "base": {"op": "var", "name": "x"},
                                "exponent": {"op": "rational", "numerator": -1, "denominator": 2}})


def _singular_origin_integral(node: dict[str, Any]) -> bool:
    variable = {"op": "var", "name": "x"}
    return (node["lower"] == {"op": "int", "value": 0} and node["upper"] == variable
            and node["arg"] == {"op": "mul", "args": [
                {"op": "real_rpow", "base": variable,
                 "exponent": {"op": "rational", "numerator": 1, "denominator": 4}},
                {"op": "bessel_j", "order": {"op": "rational", "numerator": -3, "denominator": 4},
                 "arg": variable}]})


def _has_integral(node: Any) -> bool:
    if isinstance(node, dict):
        return node.get("op") == "integral" or any(_has_integral(value) for value in node.values())
    return isinstance(node, list) and any(_has_integral(value) for value in node)


def _expr(node: Any, sort: str, depth: int = 0, budget: list[int] | None = None,
          lower_bound: int = 0) -> None:
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
        _expr(node["arg"], sort, depth + 1, budget, lower_bound)
    elif op in {"add", "sub", "mul"}:
        _keys(node, {"op", "args"})
        if not isinstance(node["args"], list) or len(node["args"]) != 2:
            raise InputError("Binary operations require exactly two arguments.")
        for arg in node["args"]:
            _expr(arg, sort, depth + 1, budget, lower_bound)
    elif op == "int_cast" and sort in {"real", "complex"}:
        _keys(node, {"op", "arg"})
        _expr(node["arg"], "int", depth + 1, budget, lower_bound)
    elif op == "div" and sort in {"real", "complex"}:
        _keys(node, {"op", "args"})
        if not isinstance(node["args"], list) or len(node["args"]) != 2:
            raise InputError("Division requires a numerator and denominator.")
        for arg in node["args"]:
            _expr(arg, sort, depth + 1, budget, lower_bound)
        if not _nonzero(node["args"][1], lower_bound):
            raise NeedsConditions("The denominator needs a nonzero condition; supported denominators follow from x > 0 and nonzero constants.")
    elif op == "pow":
        _keys(node, {"op", "base", "exponent"})
        _expr(node["base"], sort, depth + 1, budget, lower_bound)
        if type(node["exponent"]) is not int or not 0 <= node["exponent"] <= 12:
            raise InputError("Natural powers support integer exponents from 0 to 12.")
    elif op == "bessel_j" and sort == "complex":
        _keys(node, {"op", "order", "arg"})
        _expr(node["arg"], "real", depth + 1, budget, lower_bound)
        if isinstance(node["order"], dict) and node["order"].get("op") == "rational":
            order = node["order"]
            _keys(order, {"op", "numerator", "denominator"})
            p, q = order["numerator"], order["denominator"]
            if type(p) is not int or type(q) is not int or abs(p) > 1000 or not 2 <= q <= 1000:
                raise InputError("A rational order requires integer numerator and positive denominator between 2 and 1000.")
            reduced = Fraction(p, q)
            if reduced.numerator != p or reduced.denominator != q:
                raise InputError("Rational orders must be reduced and noninteger.")
            if not _positive(node["arg"], lower_bound):
                raise NeedsConditions("Noninteger orders currently require an argument proven positive from x > 0.")
        else:
            _expr(node["order"], "int", depth + 1, budget, lower_bound)
    elif op == "zpow" and sort in {"real", "complex"}:
        _keys(node, {"op", "base", "exponent"})
        _expr(node["base"], sort, depth + 1, budget, lower_bound)
        _expr(node["exponent"], "int", depth + 1, budget, lower_bound)
        if not _nonzero(node["base"], lower_bound):
            raise NeedsConditions("An integer power requires a nonzero base under the fixed assumptions.")
    elif op in {"real_rpow", "sqrt"} and sort in {"real", "complex"}:
        _keys(node, {"op", "arg"} if op == "sqrt" else {"op", "base", "exponent"})
        base = node["arg"] if op == "sqrt" else node["base"]
        _expr(base, "real", depth + 1, budget, lower_bound)
        if op == "real_rpow":
            _fixed_exponent(node["exponent"])
        if not _positive(base, lower_bound):
            raise NeedsConditions("State conditions ensuring a strictly positive real base for the real power or square root.")
    elif op == "deriv" and sort == "complex":
        _keys(node, {"op", "arg"})
        _expr(node["arg"], sort, depth + 1, budget, lower_bound)
    elif op == "integral" and sort == "complex":
        _keys(node, {"op", "arg", "lower", "upper"})
        for name in ("lower", "upper"):
            _expr(node[name], "real", depth + 1, budget, lower_bound)
        # x inside the integrand is its own bound variable; outer x > k cannot leak in.
        _expr(node["arg"], sort, depth + 1, budget, 0)
        positive_interval = all(_positive(node[name], lower_bound) for name in ("lower", "upper"))
        if _has_integral(node["arg"]):
            raise NeedsConditions("Nested integrals need an explicit supported binding and regularity check.")
        if not (_entire_integrand(node["arg"]) or positive_interval or _singular_half_integral(node) or _singular_origin_integral(node)):
            if (node["lower"] == {"op": "int", "value": 0}
                    and node["upper"] == {"op": "var", "name": "x"}
                    and node["arg"] == {"op": "div", "args": [{"op": "int", "value": 1}, {"op": "var", "name": "x"}]}):
                raise NeedsConditions("x > 0 の区間 [0,x] における 1/t の非可積分性をLean補題 not_intervalIntegrable_inv で確認しています。通常の積分として扱う範囲を指定してください。")
            raise NeedsConditions("Integral regularity needs checking: the supported integrands use integer-order J, polynomials, derivatives, and constant nonzero denominators.")
    else:
        raise InputError(f"Unsupported operation {op!r} in a {sort} expression.")


def validate_request(data: Any, require_proof: bool = True) -> dict[str, Any]:
    required = {"schema_version", "assumptions", "lhs", "rhs"}
    _keys(data, required | ({"proof"} if require_proof else set()),
          {"extra_conditions"} if require_proof else {"proof", "extra_conditions"})
    if type(data["schema_version"]) is not int or data["schema_version"] != 1:
        raise InputError("schema_version must be 1.")
    if data["assumptions"] == []:
        raise NeedsConditions("State the supported assumption explicitly: x > 0.")
    if data["assumptions"] != ASSUMPTIONS:
        raise InputError('The only supported assumptions are ["x > 0"].')
    lower_bound = _condition_domains(data)
    for name in ("lhs", "rhs"):
        _expr(data[name], "complex", lower_bound=lower_bound)
    difference = {"op": "sub", "args": [data["lhs"], data["rhs"]]}
    for atom in normalized_conditions(data):
        affine = _affine(difference, atom["variable"])
        value = Fraction(atom["value"]["numerator"], atom["value"]["denominator"])
        if atom["relation"] == "eq" and affine is not None and affine[0] != 0 and -affine[1] / affine[0] == value:
            raise NeedsConditions("入力した一次等式が等値条件そのものです。検証対象と独立した条件を指定してください。")
    for variable, (lower, upper, _) in lower_bound.items():
        affine = _affine(difference, variable)
        if (lower is not None and upper is not None and lower[0] == upper[0]
                and affine is not None and affine[0] != 0 and -affine[1] / affine[0] == lower[0]):
            raise NeedsConditions("入力した一次等式が条件の等値制約そのものです。検証対象を区別してください。")
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
                _expr(step[name], "complex", lower_bound=lower_bound)
            if step["before"] != previous:
                raise InputError("Step endpoints must form one exact AST chain.")
            previous = step["after"]
            if not isinstance(step["reason"], str) or not 1 <= len(step["reason"]) <= 2000:
                raise InputError("Each proposed reason must be 1 to 2000 characters.")
            available = set(condition_labels(data))
            if (not isinstance(step["conditions"], list)
                    or any(not isinstance(item, str) or item not in available for item in step["conditions"])):
                raise InputError("Steps can only use the fixed theorem assumptions.")
            _recipe(step["recipe"])
        if previous != data["rhs"]:
            raise InputError("The last step must end at the original target RHS.")
    else:
        raise InputError("proof.mode must be direct or steps.")
    return data


def normalized_conditions(data: dict[str, Any]) -> list[dict[str, Any]]:
    """Validate closed comparisons; retain the old x_gt representation on disk."""
    conditions = data.get("extra_conditions", [])
    if not isinstance(conditions, list) or len(conditions) > 8:
        raise InputError("Use at most eight structured extra conditions.")
    normalized = []
    for condition in conditions:
        if isinstance(condition, dict) and condition.get("op") == "x_gt":
            _keys(condition, {"op", "value"})
            value = condition["value"]
            if type(value) is not int or not 1 <= value <= 1000:
                raise NeedsConditions("Legacy x_gt requires an integer from 1 to 1000.")
            atom = {"op": "compare", "variable": "x", "relation": "gt",
                    "value": {"numerator": value, "denominator": 1}}
        else:
            _keys(condition, {"op", "variable", "relation", "value"})
            if (condition["op"] != "compare" or not isinstance(condition["variable"], str)
                    or not isinstance(condition["relation"], str) or condition["variable"] not in {"n", "x"}
                    or condition["relation"] not in {"gt", "ge", "lt", "le", "eq", "ne"}):
                raise NeedsConditions("Conditions compare x or n with an exact rational constant.")
            _keys(condition["value"], {"numerator", "denominator"})
            p, q = condition["value"]["numerator"], condition["value"]["denominator"]
            if type(p) is not int or type(q) is not int or abs(p) > 1000 or not 1 <= q <= 1000:
                raise InputError("A condition requires bounded exact integer rational fields.")
            value = Fraction(p, q)
            if (value.numerator, value.denominator) != (p, q):
                raise InputError("Condition rational constants must be reduced.")
            atom = condition
        if atom in normalized:
            raise InputError("Extra conditions must be distinct.")
        normalized.append(atom)
    return normalized


def condition_holds(condition: dict[str, Any], n: Any, x: Any) -> bool:
    value = Fraction(condition["value"]["numerator"], condition["value"]["denominator"])
    actual = n if condition["variable"] == "n" else x
    return {"gt": actual > value, "ge": actual >= value, "lt": actual < value,
            "le": actual <= value, "eq": actual == value, "ne": actual != value}[condition["relation"]]


def condition_labels(data: dict[str, Any]) -> list[str]:
    symbols = {"gt": ">", "ge": ">=", "lt": "<", "le": "<=", "eq": "=", "ne": "!="}
    return ASSUMPTIONS + [f"{atom['variable']} {symbols[atom['relation']]} "
                          f"{Fraction(atom['value']['numerator'], atom['value']['denominator'])}"
                          for atom in normalized_conditions(data)]


def condition_bounds(data: dict[str, Any]) -> list[int]:
    """Legacy integer lower bounds. New callers should use normalized_conditions."""
    return [atom["value"]["numerator"] for atom in normalized_conditions(data)
            if atom["variable"] == "x" and atom["relation"] == "gt" and atom["value"]["denominator"] == 1]


def _condition_domains(data: dict[str, Any]) -> dict:
    # Edges are (value, strict); exclusions cannot contradict a singleton interval.
    domains = {"x": [(Fraction(0), True), None, set()], "n": [None, None, set()]}
    for atom in normalized_conditions(data):
        variable, relation = atom["variable"], atom["relation"]
        value = Fraction(atom["value"]["numerator"], atom["value"]["denominator"])
        domain = domains[variable]
        if relation == "ne":
            domain[2].add(value)
        if relation in {"gt", "ge", "eq"}:
            edge = (value, relation == "gt")
            if domain[0] is None or edge > domain[0]:
                domain[0] = edge
        if relation in {"lt", "le", "eq"}:
            edge = (value, relation == "lt")
            if domain[1] is None or (edge[0], not edge[1]) < (domain[1][0], not domain[1][1]):
                domain[1] = edge
    for variable, domain in domains.items():
        lower, upper, excluded = domain
        if variable == "n":
            if lower is not None:
                value, strict = lower
                integer = value.numerator // value.denominator + 1 if strict else -(-value.numerator // value.denominator)
                lower = (Fraction(integer), False)
            if upper is not None:
                value, strict = upper
                integer = -(-value.numerator // value.denominator) - 1 if strict else value.numerator // value.denominator
                upper = (Fraction(integer), False)
            if lower is not None:
                while lower[0] in excluded:
                    lower = (lower[0] + 1, False)
            if upper is not None:
                while upper[0] in excluded:
                    upper = (upper[0] - 1, False)
            domain[0], domain[1] = lower, upper
        if lower is not None and upper is not None:
            if lower[0] > upper[0] or (lower[0] == upper[0] and
                    (lower[1] or upper[1] or lower[0] in excluded)):
                raise NeedsConditions(f"{variable} の条件が矛盾しています。両立する条件を指定してください。")
    return domains


def _condition_witness(data: dict[str, Any]) -> tuple[int, Fraction]:
    if all(item.get("op") == "x_gt" for item in data.get("extra_conditions", [])):
        return 0, Fraction(max([0] + condition_bounds(data)) + 1)
    domains = _condition_domains(data)
    values = {}
    for variable, (lower, upper, excluded) in domains.items():
        if variable == "n":
            value = int(lower[0]) if lower is not None else int(upper[0]) if upper is not None else 0
            step = 1 if lower is not None or upper is None else -1
            while value in excluded:
                value += step
        elif upper is None:
            value = lower[0] + 1
            while value in excluded:
                value += 1
        elif lower[0] == upper[0]:
            value = lower[0]
        else:
            value = (lower[0] + upper[0]) / 2
            while value in excluded:
                value = (lower[0] + value) / 2
        values[variable] = value
    return values["n"], Fraction(values["x"])


def _lean_condition(atom: dict[str, Any]) -> str:
    p, q = atom["value"]["numerator"], atom["value"]["denominator"]
    symbol = {"gt": ">", "ge": "≥", "lt": "<", "le": "≤", "eq": "=", "ne": "≠"}[atom["relation"]]
    if atom["variable"] == "x" and atom["relation"] == "gt" and q == 1:
        return f"{p} < x"
    variable = atom["variable"] if q == 1 else f"({atom['variable']} : ℝ)"
    constant = str(p) if q == 1 else f"(({p} : ℝ) / {q})"
    return f"{variable} {symbol} {constant}"


def _recipe(recipe: Any) -> None:
    if not isinstance(recipe, str) or recipe not in RECIPES:
        raise InputError(f"recipe must be one of {sorted(RECIPES)}.")


def lean_expr(node: dict[str, Any], sort: str = "complex") -> str:
    op = node["op"]
    if op == "int":
        return f"({node['value']} : { {'int': 'ℤ', 'real': 'ℝ', 'complex': 'ℂ'}[sort]})"
    if op == "rational":
        return f"(({node['numerator']} : ℝ) / ({node['denominator']} : ℝ))"
    if op == "var":
        return "(x : ℂ)" if sort == "complex" else node["name"]
    if op == "neg":
        return f"(-{lean_expr(node['arg'], sort)})"
    if op == "int_cast":
        return f"({lean_expr(node['arg'], 'int')} : { 'ℝ' if sort == 'real' else 'ℂ'})"
    if op in {"add", "sub", "mul", "div"}:
        left, right = (lean_expr(arg, sort) for arg in node["args"])
        return f"({left} { {'add': '+', 'sub': '-', 'mul': '*', 'div': '/'}[op]} {right})"
    if op == "bessel_j":
        if node["order"]["op"] == "rational":
            order = node["order"]
            return f"(Complex.besselJ ((({order['numerator']} : ℝ) / ({order['denominator']} : ℝ) : ℝ) : ℂ) (({lean_expr(node['arg'], 'real')}) : ℂ))"
        return f"(BesselProofAgent.J {lean_expr(node['order'], 'int')} {lean_expr(node['arg'], 'real')})"
    if op == "deriv":
        return f"(deriv (fun (x : ℝ) => {lean_expr(node['arg'])}) x)"
    if op == "integral":
        return f"(intervalIntegral (fun (x : ℝ) => {lean_expr(node['arg'])}) {lean_expr(node['lower'], 'real')} {lean_expr(node['upper'], 'real')} MeasureTheory.volume)"
    if op == "pow":
        return f"({lean_expr(node['base'], sort)} ^ ({node['exponent']} : ℕ))"
    if op in {"real_rpow", "sqrt"}:
        value = (f"(Real.sqrt {lean_expr(node['arg'], 'real')})" if op == "sqrt" else
                 f"(Real.rpow {lean_expr(node['base'], 'real')} {lean_expr(node['exponent'], 'real')})")
        return f"({value} : ℂ)" if sort == "complex" else value
    return f"({lean_expr(node['base'], sort)} ^ {lean_expr(node['exponent'], 'int')})"


def display_expr(node: dict[str, Any]) -> str:
    op = node["op"]
    if op == "int":
        return str(node["value"])
    if op == "var":
        return node["name"]
    if op == "int_cast":
        return display_expr(node["arg"])
    if op == "rational":
        return f"{node['numerator']}/{node['denominator']}"
    if op == "neg":
        return f"(-{display_expr(node['arg'])})"
    if op in {"add", "sub", "mul", "div"}:
        left, right = (display_expr(arg) for arg in node["args"])
        return f"({left} { {'add': '+', 'sub': '-', 'mul': '·', 'div': '/'}[op]} {right})"
    if op == "bessel_j":
        return f"J_{{{display_expr(node['order'])}}}({display_expr(node['arg'])})"
    if op == "deriv":
        return f"d/dx({display_expr(node['arg'])})"
    if op == "integral":
        return f"integral_{{{display_expr(node['lower'])}}}^{{{display_expr(node['upper'])}}}({display_expr(node['arg'])})"
    if op == "pow":
        return f"({display_expr(node['base'])})^({node['exponent']})"
    if op == "sqrt":
        return f"sqrt({display_expr(node['arg'])})"
    if op == "real_rpow":
        return f"real_power({display_expr(node['base'])}, {display_expr(node['exponent'])})"
    return f"({display_expr(node['base'])})^({display_expr(node['exponent'])})"


def theorem_statement(data: dict[str, Any]) -> str:
    extra = "".join(f"{_lean_condition(atom)} → " for atom in normalized_conditions(data))
    return f"∀ (n : ℤ) (x : ℝ), 0 < x → {extra}{lean_expr(data['lhs'])} = {lean_expr(data['rhs'])}"


def _recipe_text(recipe: str, left: dict, right: dict, bounds: list[dict] | None = None) -> str:
    prefix = []
    for index, atom in enumerate(bounds or []):
        if atom["variable"] == "n":
            real_atom = dict(atom, variable="x")
            proposition = _lean_condition(real_atom).replace("x", "(n : ℝ)")
            prefix.append(f"have hcondition_real_{index + 1} : {proposition} := by exact_mod_cast hcondition_{index + 1}")
    body = _recipe_body(recipe, left, right, bounds)
    if prefix and recipe == "power":
        body = body.replace("(try norm_cast) <;>", "(try norm_cast) <;> (try push_cast) <;>")
    return "\n".join(prefix + [body])


def _recipe_body(recipe: str, left: dict, right: dict, bounds: list[dict] | None = None) -> str:
    orders: set[tuple[int, int]] = set()
    power_bases: list[dict] = []
    denominators: list[dict] = []
    has_new_calculus = False
    has_origin_integral = False

    def collect(node: Any, inside_binding: bool = False) -> None:
        nonlocal has_new_calculus, has_origin_integral
        if isinstance(node, dict):
            if node.get("op") == "integral" and _singular_origin_integral(node):
                has_origin_integral = True
            if node.get("op") == "bessel_j" and node["order"].get("op") == "rational":
                order = node["order"]
                orders.add((order["numerator"], order["denominator"]))
                has_new_calculus = True
            if node.get("op") in {"real_rpow", "sqrt"}:
                has_new_calculus = True
                base = node["arg"] if node["op"] == "sqrt" else node["base"]
                if not inside_binding and base not in power_bases:
                    power_bases.append(base)
            if node.get("op") == "div" and not inside_binding and node["args"][1] not in denominators:
                denominators.append(node["args"][1])
            inside_binding = inside_binding or node.get("op") in {"deriv", "integral"}
            for value in node.values():
                collect(value, inside_binding)
        elif isinstance(node, list):
            for value in node:
                collect(value, inside_binding)

    collect(left)
    collect(right)
    if recipe == "power":
        lines = []
        for index, base in enumerate(power_bases):
            lines += [f"have hpositive_{index} : (0 : ℝ) < {lean_expr(base, 'real')} := by first | positivity | linarith"]
        rules = ["Real.rpow_eq_pow", "Real.sqrt_eq_rpow", "pow_two"] + [f"← Real.rpow_add hpositive_{index}" for index in range(len(power_bases))]
        lines += ["(try norm_cast) <;> (simp only [" + ", ".join(rules) + "] <;> norm_num)"]
        return "\n".join(lines)
    if recipe == "field" and bounds:
        lines = []
        alternatives = ""
        for index, atom in enumerate(bounds):
            if atom["relation"] == "ne":
                name = f"hcondition_real_{index + 1}" if atom["variable"] == "n" else f"hcondition_{index + 1}"
                alternatives += f" | (intro hzero; apply {name}; linarith)"
        for index, denominator in enumerate(denominators):
            lines += [f"have hdenominator_{index} : {lean_expr(denominator)} ≠ 0 := by",
                      f"  have hreal : {lean_expr(denominator, 'real')} ≠ 0 := by",
                      "    first | positivity | (apply ne_of_gt; linarith) | (apply ne_of_lt; linarith)" + alternatives,
                      "  exact_mod_cast hreal"]
        rules = ", ".join(f"hdenominator_{index}" for index in range(len(denominators)))
        lines += [f"field_simp [{rules}] <;> ring"]
        return "\n".join(lines)
    if recipe == "calculus" and has_new_calculus:
        lines = ["have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)",
                 "have hintegrable := BesselProofAgent.intervalIntegrable_inv_sqrt_complex x",
                 "have hsingular := BesselProofAgent.integral_inv_sqrt x hx",
                 "have hweighted := BesselProofAgent.integral_sqrt_mul_bessel_neg_half x hx"]
        names = ["hsingular", "hweighted"]
        if has_origin_integral:
            lines += ["have horigin_integrable := BesselProofAgent.intervalIntegrable_origin_weighted_bessel x hx",
                      "have horigin := BesselProofAgent.integral_origin_weighted_bessel x hx"]
            names.append("horigin")
        for index, (p, q) in enumerate(sorted(orders)):
            lines += [f"have hderivative_{index} := BesselProofAgent.deriv_bessel_rational ({p} : ℤ) ({q} : ℕ) (by norm_num) x hx",
                      f"have hsymmetric_{index} := BesselProofAgent.deriv_bessel_real_symmetric (({p} : ℂ) / ({q} : ℂ)) x hx",
                      f"have hintegral_{index} := BesselProofAgent.integral_deriv_bessel_real (({p} : ℂ) / ({q} : ℂ)) x hx"]
            names += [f"hderivative_{index}", f"hintegral_{index}"]
        symmetric_names = [name.replace("hderivative_", "hsymmetric_") for name in names]
        lines += ["norm_num [div_div] at " + " ".join(dict.fromkeys(names + symmetric_names)) + " ⊢", "solve",
                  "| (try simp only [" + ", ".join(names) + "]) <;> (solve | ring | (field_simp [hxC] <;> ring))",
                  "| (try simp only [" + ", ".join(symmetric_names) + "]) <;> (solve | ring | (field_simp [hxC] <;> ring))"]
        return "\n".join(lines)
    if recipe != "recurrence":
        return RECIPES[recipe]
    if not orders:
        return RECIPES[recipe]
    lines = ["have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)", "solve"]
    for p, q in sorted(orders):
        lines += [f"| have hrec := BesselProofAgent.bessel_recurrence (({p} : ℂ) / ({q} : ℂ)) (x : ℂ) hxC",
                  "  norm_num at hrec ⊢", "  solve", "  | linear_combination hrec",
                  "  | linear_combination -hrec", "  | linear_combination (1 / 2 : ℂ) * hrec",
                  "  | linear_combination -(1 / 2 : ℂ) * hrec", "  | (try simp only [hrec]) <;> ring"]
    return "\n".join(lines)


def render_lean(data: dict[str, Any], kind: str = "proof") -> str:
    validate_request(data)
    if kind not in {"proof", "refutation"}:
        raise InputError("Unknown certificate kind.")
    lines = ["import BesselProofAgent", "", "namespace BesselAgentCandidate", ""]
    statement = theorem_statement(data)
    bounds = normalized_conditions(data)
    hypothesis_names = "".join(f" hcondition_{index + 1}" for index in range(len(bounds)))
    hypothesis_binders = "".join(f" (hcondition_{index + 1} : {_lean_condition(atom)})" for index, atom in enumerate(bounds))
    if kind == "refutation":
        witness_n, witness_x = _condition_witness(data)
        witness = str(witness_x) if witness_x.denominator == 1 else f"({witness_x.numerator} / {witness_x.denominator} : ℝ)"
        lines += [f"theorem target : ¬ ({statement}) := by", "  intro h",
                  f"  have hbad := h {witness_n if witness_n >= 0 else '(' + str(witness_n) + ')'} {witness} (by norm_num)" + " (by norm_num)" * len(bounds), "  first",
                  "  | have bad : (0 : ℂ) = 1 := by linear_combination hbad",
                  "    norm_num at bad",
                  "  | have bad : (0 : ℂ) = 1 := by linear_combination -hbad",
                  "    norm_num at bad", "  | norm_num at hbad"]
    elif data["proof"]["mode"] == "direct":
        lines += [f"theorem target : {statement} := by", "  intro n x hx" + hypothesis_names]
        lines += ["  " + line for line in _recipe_text(data["proof"]["recipe"], data["lhs"], data["rhs"], bounds).splitlines()]
    else:
        steps = data["proof"]["steps"]
        for index, step in enumerate(steps):
            lines += [f"theorem step_{index + 1} (n : ℤ) (x : ℝ) (hx : 0 < x){hypothesis_binders} :",
                      f"    {lean_expr(step['before'])} = {lean_expr(step['after'])} := by"]
            lines += ["  " + line for line in _recipe_text(step["recipe"], step["before"], step["after"], bounds).splitlines()]
            lines += [""]
        lines += [f"theorem target : {statement} := by", "  intro n x hx" + hypothesis_names, "  calc"]
        for index, step in enumerate(steps):
            left = lean_expr(step["before"]) if index == 0 else "_"
            lines += [f"    {left} = {lean_expr(step['after'])} := step_{index + 1} n x hx{hypothesis_names}"]
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


def _diagnostics(text: str, source: Path) -> str:
    return (text.replace(str(source.resolve()), source.name)
            .replace(str(ROOT.resolve()), "<project>").replace(str(Path.home()), "~"))


def _run_lean(path: Path, timeout: float) -> dict[str, Any]:
    try:
        process = subprocess.Popen(["lake", "env", "lean", str(path.resolve())], cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                   start_new_session=True)
    except OSError as exc:
        return {"accepted": False, "reason": "lean_unavailable", "stdout": "", "stderr": _diagnostics(str(exc), path)}
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        return {"accepted": False, "reason": "timeout", "stdout": _diagnostics(stdout, path), "stderr": _diagnostics(stderr, path)}
    stdout, stderr = _diagnostics(stdout, path), _diagnostics(stderr, path)
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
    if data.get("extra_conditions"):
        lines += ["追加条件：" + "、".join(condition_labels(data)[1:]) + "。", ""]
    if result["status"] == "proved":
        lines += ["固定した命題の証明と依存公理の監査が完了しました。", ""]
        if data["proof"]["mode"] == "steps":
            for index, step in enumerate(data["proof"]["steps"], 1):
                method = {"bessel": "整数次数の符号関係と代数式の整理", "ring": "代数式の整理",
                          "power": "正の実底の有理数冪と平方根の公式",
                          "conditions": "明示された変数の比較条件と代数式の整理",
                          "field": "非零条件を用いた分数式の整理", "recurrence": "三項漸化式と代数式の整理",
                          "calculus": "微分・積分の公式と代数式の整理"}[step["recipe"]]
                lines += [f"{index}. `{display_expr(step['before'])} = {display_expr(step['after'])}`",
                          f"   {method}により、この等式をLeanで検査しました。対応する証明は `step_{index}` です。", ""]
            lines += ["以上の等式を連結し、元の左辺から右辺への証明を検査しました。", "",
                      "AIが提案した自由記述の理由は request.json に保存しています。上の説明は検査した構造化手順から生成しています。", ""]
    elif result["status"] == "refuted":
        witness_n, witness = _condition_witness(data)
        lines += [f"n = {witness_n}、x = {witness} を用いて、元の全称命題の否定をLeanで証明しました。", ""]
    else:
        lines += ["今回の手順と制限時間で証明・反証を確定できませんでした。", "",
                  "詳細は result.json の各試行に記録しています。", ""]
    return "\n".join(lines)


def verify(data: Any, output_dir: Path, timeout: float = 60) -> dict[str, Any]:
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    if any(output_dir.iterdir()):
        raise InputError("Use an empty output directory to preserve earlier evidence.")
    # Preserve JSON inputs even when validation stops before Lean is invoked.
    try:
        _save_json(output_dir / "request.json", data)
    except (TypeError, ValueError):
        pass  # Programmatic non-JSON objects have no serializable request.
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
