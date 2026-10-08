"""A closed, non-evaluating parser for a documented subset of Bessel notation.

This intentionally parses equations, not TeX programs. Unknown commands,
unsupported variable scopes, and unstated domains produce explicit errors.
"""

from __future__ import annotations

from fractions import Fraction
import re
from typing import Any

from .core import InputError, NeedsConditions, validate_request


TOKEN = re.compile(r"\s+|\\[A-Za-z]+|\\[,!;:]|[0-9]+|[A-Za-z]+|[_^{}()+\-*/=,;]")


def _integer(value: int) -> dict[str, Any]:
    return {"op": "int", "value": value}


def _binary(op: str, left: dict, right: dict) -> dict:
    return {"op": op, "args": [left, right]}


def _fraction(node: dict) -> Fraction | None:
    if node["op"] == "int":
        return Fraction(node["value"])
    if node["op"] == "neg":
        value = _fraction(node["arg"])
        return -value if value is not None else None
    if node["op"] in {"add", "sub", "mul", "div"}:
        a, b = (_fraction(arg) for arg in node["args"])
        if a is None or b is None:
            return None
        if node["op"] == "div" and b == 0:
            raise NeedsConditions("A rational order has a zero denominator.")
        return {"add": lambda: a + b, "sub": lambda: a - b,
                "mul": lambda: a * b, "div": lambda: a / b}[node["op"]]()
    return None


def _contains_var(node: Any, name: str) -> bool:
    if isinstance(node, dict):
        return (node.get("op") == "var" and node.get("name") == name) or any(
            _contains_var(value, name) for value in node.values())
    return isinstance(node, list) and any(_contains_var(value, name) for value in node)


def _order(node: dict) -> dict:
    rational = _fraction(node)
    if rational is not None:
        if rational.denominator == 1:
            return _integer(rational.numerator)
        return {"op": "rational", "numerator": rational.numerator,
                "denominator": rational.denominator}
    op = node["op"]
    if op == "var" and node["name"] == "n":
        return node
    if op == "neg":
        arg = _order(node["arg"])
        if arg["op"] != "rational":
            return {"op": "neg", "arg": arg}
    if op in {"add", "sub", "mul"}:
        args = [_order(arg) for arg in node["args"]]
        if all(arg["op"] != "rational" for arg in args):
            return {"op": op, "args": args}
    raise NeedsConditions("Orders support integer expressions in n and fixed rational numbers; specify a supported order.")


def _convert(node: dict, sort: str = "complex", bound: str = "x") -> dict:
    op = node["op"]
    if op == "var":
        if node["name"] == "n":
            return {"op": "int_cast", "arg": node}
        if node["name"] == bound:
            return {"op": "var", "name": "x"}
        raise NeedsConditions(f"Variable {node['name']} needs an explicit supported binding.")
    if op == "int":
        return node
    if op in {"add", "sub", "mul", "div"}:
        return {"op": op, "args": [_convert(arg, sort, bound) for arg in node["args"]]}
    if op == "neg":
        return {"op": op, "arg": _convert(node["arg"], sort, bound)}
    if op == "bessel_j":
        return {"op": op, "order": _order(node["order"]),
                "arg": _convert(node["arg"], "real", bound)}
    if op == "power":
        exponent = _order(node["exponent"])
        base = _convert(node["base"], sort, bound)
        if exponent["op"] == "int" and exponent["value"] >= 0:
            return {"op": "pow", "base": base, "exponent": exponent["value"]}
        if exponent["op"] == "rational":
            raise NeedsConditions("Fractional powers need a branch/domain specification; the current grammar supports integer powers.")
        return {"op": "zpow", "base": base, "exponent": exponent}
    if op == "deriv":
        if node.get("variable") not in {None, bound}:
            raise NeedsConditions("The derivative variable differs from the current binding; use an explicit supported scope.")
        return {"op": op, "arg": _convert(node["arg"], "complex", bound)}
    if op == "integral":
        variable = node["variable"]
        if variable == "t" and _contains_var(node["arg"], "x"):
            raise NeedsConditions("An integral with a free x parameter in its integrand needs a separate parameter binding.")
        if bound != "x":
            raise NeedsConditions("Nested integral bindings are outside the supported input grammar.")
        return {"op": op, "arg": _convert(node["arg"], "complex", variable),
                "lower": _convert(node["lower"], "real", bound),
                "upper": _convert(node["upper"], "real", bound)}
    raise InputError(f"Unsupported expression node {op}.")


class _Parser:
    def __init__(self, text: str):
        text = text.replace("−", "-").strip()
        if text.startswith("$") and text.endswith("$"):
            text = text[1:-1].strip("$")
        if text.startswith(r"\[") and text.endswith(r"\]"):
            text = text[2:-2]
        text = re.sub(r"\\frac\s*\{\s*d\s*\}\s*\{\s*d\s*([xt])\s*\}", lambda m: " D" + m[1] + " ", text)
        text = re.sub(r"\bd\s*/\s*d\s*([xt])\b", lambda m: " D" + m[1] + " ", text)
        self.tokens: list[str] = []
        index = 0
        while index < len(text):
            match = TOKEN.match(text, index)
            if not match:
                raise InputError(f"Unsupported notation at character {index + 1}: {text[index:index + 12]!r}")
            token = match.group()
            index = match.end()
            if token.isspace() or token in {r"\left", r"\right", r"\,", r"\!", r"\;", r"\:"}:
                continue
            token = {r"\cdot": "*", r"\times": "*", r"\dfrac": r"\frac"}.get(token, token)
            self.tokens.append(token)
        if len(self.tokens) > 1500:
            raise InputError("The equation exceeds the parser token limit.")
        self.index = 0

    def peek(self) -> str | None:
        return self.tokens[self.index] if self.index < len(self.tokens) else None

    def take(self, token: str | None = None) -> str:
        current = self.peek()
        if current is None or (token is not None and current != token):
            raise InputError(f"Expected {token or 'an expression'}, found {current!r}.")
        self.index += 1
        return current

    def equation(self) -> tuple[dict, dict]:
        left = self.expression()
        self.take("=")
        right = self.expression()
        if self.peek() is not None:
            raise InputError(f"Unexpected trailing token {self.peek()!r}.")
        return left, right

    def expression(self) -> dict:
        left = self.product()
        while self.peek() in {"+", "-"}:
            op = "add" if self.take() == "+" else "sub"
            left = _binary(op, left, self.product())
        return left

    def product(self) -> dict:
        left = self.unary()
        while True:
            if self.peek() in {"*", "/"}:
                op = "mul" if self.take() == "*" else "div"
                left = _binary(op, left, self.unary())
            elif self._starts_atom():
                left = _binary("mul", left, self.unary())
            else:
                return left

    def _starts_atom(self) -> bool:
        token = self.peek()
        return token is not None and (token.isdigit() or token in {"n", "x", "t", "J", "D", "Dx", "Dt", "int", "(", "{", r"\frac", r"\int"})

    def unary(self) -> dict:
        if self.peek() == "+":
            self.take()
            return self.unary()
        if self.peek() == "-":
            self.take()
            arg = self.unary()
            return _integer(-arg["value"]) if arg["op"] == "int" else {"op": "neg", "arg": arg}
        left = self.atom()
        if self.peek() == "^":
            self.take()
            left = {"op": "power", "base": left, "exponent": self.script()}
        return left

    def group(self) -> dict:
        opener = self.take()
        if opener not in {"{", "("}:
            raise InputError("Use parentheses or braces to group this expression.")
        result = self.expression()
        self.take("}" if opener == "{" else ")")
        return result

    def script(self) -> dict:
        if self.peek() in {"{", "("}:
            return self.group()
        if self.peek() in {"+", "-"}:
            sign = self.take()
            value = self.script()
            if sign == "+":
                return value
            return _integer(-value["value"]) if value["op"] == "int" else {"op": "neg", "arg": value}
        token = self.take()
        if token.isdigit():
            return _integer(int(token))
        if token in {"n", "x", "t"}:
            return {"op": "var", "name": token}
        raise InputError("A subscript or exponent requires one symbol, number, or grouped expression.")

    def atom(self) -> dict:
        token = self.peek()
        if token in {"{", "("}:
            return self.group()
        if token is not None and token.isdigit():
            return _integer(int(self.take()))
        if token in {"n", "x", "t"}:
            return {"op": "var", "name": self.take()}
        if token == r"\frac":
            self.take()
            return _binary("div", self.group(), self.group())
        if token == "J":
            self.take()
            if self.peek() == "_":
                self.take()
                order = self.script()
                if self.peek() != "(":
                    raise NeedsConditions("Clarify the Bessel argument explicitly as J_{order}(argument).")
                arg = self.group()
            else:
                self.take("(")
                order = self.expression()
                self.take(",")
                arg = self.expression()
                self.take(")")
            return {"op": "bessel_j", "order": order, "arg": arg}
        if token in {"D", "Dx", "Dt"}:
            self.take()
            arg = self.group() if self.peek() in {"(", "{"} else self.unary()
            return {"op": "deriv", "arg": arg, "variable": token[1:] or None}
        if token == "int":
            self.take()
            self.take("(")
            lower = self.expression()
            self.take(",")
            upper = self.expression()
            self.take(",")
            arg = self.expression()
            self.take(",")
            variable = self.take()
            if variable not in {"x", "t"}:
                raise NeedsConditions("The integration variable must be x or t.")
            self.take(")")
            return {"op": "integral", "arg": arg, "lower": lower, "upper": upper, "variable": variable}
        if token == r"\int":
            self.take()
            self.take("_")
            lower = self.script()
            self.take("^")
            upper = self.script()
            arg = self.expression()
            differential = self.take()
            if differential == "d":
                differential += self.take()
            if differential not in {"dx", "dt"}:
                raise InputError("End the integral with dx or dt.")
            return {"op": "integral", "arg": arg, "lower": lower, "upper": upper,
                    "variable": differential[-1]}
        raise InputError(f"Unsupported token {token!r}; use the documented equation grammar.")


def _conditions(raw: str | list[str] | None, has_n: bool) -> None:
    if isinstance(raw, list):
        if not all(isinstance(item, str) for item in raw):
            raise InputError("Conditions must be text.")
        raw = ",".join(raw)
    if not isinstance(raw, str) or not raw.strip():
        raise NeedsConditions("State x > 0 and, when n appears, n integer.")
    raw = raw.replace(r"\mathbb{Z}", "Z").replace(r"\mathbb{R}", "R")
    raw = raw.replace(r"\in", "in").replace("∈", "in").replace("ℤ", "Z").replace("ℝ", "R")
    parts = {re.sub(r"\s+", "", part).strip("()") for part in raw.split(",")}
    integer = {"ninteger", "ninZ", "n:Z"}
    positive = {"x>0", "0<x", "xpositive"}
    allowed = integer | positive | {"xinR", "xreal", "x:R"}
    if parts - allowed:
        raise NeedsConditions("The supplied conditions require clarification; this input grammar uses n integer and x > 0.")
    if not parts & positive or (has_n and not parts & integer):
        raise NeedsConditions("State x > 0 and, when n appears, n integer.")


def parse_identity(text: str, conditions: str | list[str] | None = None) -> dict[str, Any]:
    """Return the fixed target AST without a proof candidate."""
    if not isinstance(text, str) or len(text) > 32768:
        raise InputError("An equation must be at most 32768 characters of text.")
    separated = re.split(r"(?<!\\);", text, maxsplit=1)
    if len(separated) == 2:
        if conditions is not None:
            raise NeedsConditions("Conditions were supplied twice; retain one explicit condition list.")
        text, conditions = separated
    try:
        left, right = _Parser(text).equation()
        _conditions(conditions, _contains_var(left, "n") or _contains_var(right, "n"))
        data = {"schema_version": 1, "assumptions": ["x > 0"],
                "lhs": _convert(left), "rhs": _convert(right)}
        validate_request(data, require_proof=False)
        return data
    except RecursionError as exc:
        raise InputError("The equation exceeds the parser nesting limit.") from exc
