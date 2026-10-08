"""A closed, non-evaluating parser for a documented subset of Bessel notation.

This intentionally parses equations, not TeX programs. Unknown commands,
unsupported variable scopes, and unstated domains produce explicit errors.
"""

from __future__ import annotations

from fractions import Fraction
import re
from typing import Any

from .core import InputError, NeedsConditions, _condition_domains, validate_request


TOKEN = re.compile(r"\s+|\\[A-Za-z]+|\\[,!;:]|[0-9]+|[A-Za-z]+|[_^{}()+\-*/=,;']")
TEX_BUILTINS = {"frac", "dfrac", "tfrac", "int", "sqrt", "left", "right", "cdot", "times", "operatorname"}
TEX_RESERVED = TEX_BUILTINS | {"newcommand", "def", "DeclareMathOperator", "begin", "end", "text", "quad", "qquad", "in", "mathbb", "le", "leq", "ge", "geq", "ne", "neq", "prime"}


def _tex_group(text: str, index: int) -> tuple[str, int]:
    while index < len(text) and text[index].isspace():
        index += 1
    if index >= len(text) or text[index] != "{":
        raise InputError("Macro names, bodies, and arguments must use braces.")
    start = index + 1
    depth = 1
    index += 1
    while index < len(text):
        depth += (text[index] == "{") - (text[index] == "}")
        if depth > 16:
            raise InputError("A macro group exceeds the nesting limit.")
        if depth == 0:
            return text[start:index], index + 1
        index += 1
    raise InputError("Unclosed macro group.")


def _expand_macros(text: str) -> str:
    """Expand bounded expression macros; never execute TeX."""
    macros: dict[str, tuple[int, str]] = {}
    text = text.lstrip()
    while re.match(r"\\(?:newcommand|def|DeclareMathOperator)\b", text):
        command = re.match(r"\\([A-Za-z]+)", text)[1]
        index = len(command) + 1
        if command == "def":
            match = re.match(r"\s*\\([A-Za-z]{1,16})(?![A-Za-z])", text[index:])
            if not match:
                raise InputError("Use a short macro name after def.")
            name = match[1]
            index += match.end()
            placeholders = re.match(r"(?:#[1-3])*", text[index:])[0]
            arity = len(placeholders) // 2
            if placeholders != "".join(f"#{number}" for number in range(1, arity + 1)):
                raise InputError("def supports consecutive parameters #1 through #3.")
            body, end = _tex_group(text, index + len(placeholders))
        else:
            name_group, index = _tex_group(text, index)
            match = re.fullmatch(r"\\([A-Za-z]{1,16})", name_group)
            if not match:
                raise InputError("Use a macro name of 1 to 16 ASCII letters.")
            name = match[1]
            if command == "DeclareMathOperator":
                body, end = _tex_group(text, index)
                if body != "J":
                    raise InputError("DeclareMathOperator currently supports the Bessel operator J.")
                arity = 0
            else:
                arity_match = re.match(r"\s*\[([0-3])\]", text[index:])
                if not arity_match:
                    raise InputError("Declare an explicit macro arity from [0] to [3].")
                arity = int(arity_match[1])
                body, end = _tex_group(text, index + arity_match.end())
        if name in TEX_RESERVED or name in macros:
            raise InputError("A macro cannot replace a built-in or an earlier definition.")
        if len(body) > 512 or not re.fullmatch(r"[A-Za-z0-9_#{}()^+*/\-\\,\s]*", body):
            raise InputError("A macro body must be a short mathematical expression.")
        placeholders = re.findall(r"#([0-9]+)", body)
        if set(placeholders) != {str(number) for number in range(1, arity + 1)}:
            raise InputError("Every declared macro argument must occur in the expression body.")
        if any(not 1 <= int(value) <= arity for value in placeholders) or "#" in re.sub(r"#[0-9]+", "", body):
            raise InputError("A macro placeholder must refer to one declared argument.")
        macros[name] = arity, body
        if len(macros) > 4:
            raise InputError("At most four macros may be declared.")
        text = text[end:].lstrip()
    dependencies = {name: set(re.findall(r"\\([A-Za-z]+)", body)) - TEX_BUILTINS
                    for name, (_, body) in macros.items()}

    def acyclic(name: str, stack: set[str]) -> None:
        if name in stack:
            raise InputError("Recursive macros are unsupported.")
        for dependency in dependencies[name]:
            if dependency not in macros:
                raise InputError("A macro body refers to an undeclared command.")
            acyclic(dependency, stack | {name})

    for name in macros:
        acyclic(name, set())
    count = [0]

    def expand(source: str, depth: int = 0) -> str:
        if depth > 8:
            raise InputError("Macro expansion exceeds the depth limit.")
        parts: list[str] = []
        index = 0
        length = 0
        while index < len(source):
            match = re.match(r"\\([A-Za-z]+)", source[index:])
            if match and match[1] in macros:
                count[0] += 1
                if count[0] > 128:
                    raise InputError("Macro expansion exceeds the invocation limit.")
                arity, body = macros[match[1]]
                index += match.end()
                arguments = []
                for _ in range(arity):
                    argument, index = _tex_group(source, index)
                    if re.search(r"[=<>;#&]|\\\\|\\(?:text|begin|end)\b", argument):
                        raise NeedsConditions("Macro arguments must be expressions; equations and condition rows need explicit separation.")
                    arguments.append(argument)
                replaced = re.sub(r"#([1-3])", lambda m: arguments[int(m[1]) - 1], body)
                part = " " + expand(replaced, depth + 1) + " "
            else:
                part = source[index:index + match.end()] if match else source[index]
                index += match.end() if match else 1
            parts.append(part)
            length += len(part)
            if length > 32768:
                raise InputError("Expanded equation exceeds the length limit.")
        return "".join(parts)

    return expand(text)


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
            return {"op": "real_rpow", "base": _convert(node["base"], "real", bound), "exponent": exponent}
        return {"op": "zpow", "base": base, "exponent": exponent}
    if op == "sqrt":
        return {"op": "sqrt", "arg": _convert(node["arg"], "real", bound)}
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
        text = text.replace("−", "-").replace(r"\prime", "'").strip()
        text = re.sub(r"\\(?:frac|dfrac|tfrac)\s*\{\s*d\s*\}\s*\{\s*d\s*([xt])\s*\}", lambda m: " D" + m[1] + " ", text)
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
            token = {r"\cdot": "*", r"\times": "*", r"\dfrac": r"\frac", r"\tfrac": r"\frac"}.get(token, token)
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
        return token is not None and (token.isdigit() or token in {"n", "x", "t", "J", "D", "Dx", "Dt", "int", "sqrt", "(", "{", r"\frac", r"\int", r"\sqrt"})

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
        if token in {"sqrt", r"\sqrt"}:
            self.take()
            return {"op": "sqrt", "arg": self.group()}
        if token == "J":
            self.take()
            prime = self.peek() == "'"
            if prime:
                self.take()
            if self.peek() == "_":
                self.take()
                order = self.script()
                if self.tokens[self.index:self.index + 2] == ["^", "'"]:
                    self.index += 1
                elif self.tokens[self.index:self.index + 4] == ["^", "{", "'", "}"]:
                    self.tokens[self.index:self.index + 4] = ["'"]
                if self.peek() == "'":
                    if prime:
                        raise NeedsConditions("Only the first Bessel derivative is supported.")
                    prime = True
                    self.take()
                if self.peek() != "(":
                    raise NeedsConditions("Clarify the Bessel argument explicitly as J_{order}(argument).")
                arg = self.group()
            else:
                self.take("(")
                order = self.expression()
                self.take(",")
                arg = self.expression()
                self.take(")")
            result = {"op": "bessel_j", "order": order, "arg": arg}
            if prime:
                if arg.get("op") != "var" or arg.get("name") not in {"x", "t"}:
                    raise NeedsConditions("Prime notation requires the explicit argument x or t; use D for a composition.")
                return {"op": "deriv", "arg": result, "variable": arg["name"]}
            return result
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


def _conditions(raw: str | list[str] | None, has_n: bool) -> list[dict[str, Any]]:
    if isinstance(raw, list):
        if not all(isinstance(item, str) for item in raw):
            raise InputError("Conditions must be text.")
        raw = ",".join(raw)
    if not isinstance(raw, str) or not raw.strip():
        raise NeedsConditions("State x > 0 and, when n appears, n integer.")
    raw = raw.replace("、", ",").replace("かつ", ",").replace("，", ",")
    raw = re.sub(r"\b(?:and|where|for)\b", ",", raw)
    raw = raw.replace(r"\mathbb{Z}", "Z").replace(r"\mathbb{R}", "R")
    raw = raw.replace(r"\in", "in").replace("∈", "in").replace("ℤ", "Z").replace("ℝ", "R")
    for source, target in [(r"\geq", ">="), (r"\ge", ">="), (r"\leq", "<="), (r"\le", "<="),
                           (r"\neq", "!="), (r"\ne", "!="), ("≥", ">="), ("≤", "<="), ("≠", "!=")]:
        raw = raw.replace(source, target)
    raw = re.sub(r"\\(?:tfrac|dfrac|frac)\s*\{\s*(-?[0-9]+)\s*\}\s*\{\s*([0-9]+)\s*\}", r"\1/\2", raw)
    parts = [re.sub(r"\s+", "", part) for part in raw.split(",") if part.strip()]
    integer = {"ninteger", "ninZ", "n:Z", "nは整数", "n整数"}
    positive = {"x>0", "0<x", "xpositive", "xは正", "xは正の実数"}
    real = {"xinR", "xreal", "x:R", "xは実数"}
    relation_names = {">": "gt", ">=": "ge", "<": "lt", "<=": "le", "=": "eq", "!=": "ne"}
    extras = []
    stated_positive = False
    stated_integer = False
    for part in parts:
        while part.startswith("(") and part.endswith(")"):
            part = part[1:-1]
        if "(" in part or ")" in part:
            raise NeedsConditions("条件の括弧が対応していません。各比較を明示してください。")
        if part in integer:
            stated_integer = True
            continue
        if part in real:
            continue
        if part in positive:
            stated_positive = True
            continue
        tokens = re.split(r"(>=|<=|!=|>|<|=)", part)
        if len(tokens) not in {3, 5} or (len(tokens) == 5 and tokens[2] not in {"x", "n"}):
            raise NeedsConditions("条件は x または n と有理数との比較を明示してください。")
        for index in range(0, len(tokens) - 2, 2):
            left, operator, right = tokens[index:index + 3]
            if left in {"x", "n"}:
                variable, constant = left, right
            elif right in {"x", "n"}:
                variable, constant = right, left
                operator = {">": "<", ">=": "<=", "<": ">", "<=": ">=", "=": "=", "!=": "!="}[operator]
            else:
                raise NeedsConditions("Each comparison must have one variable and one rational constant.")
            if not re.fullmatch(r"[+-]?[0-9]+(?:/[0-9]+)?", constant):
                raise NeedsConditions("比較条件の定数は整数または正確な分数で指定してください。")
            try:
                value = Fraction(constant)
            except ZeroDivisionError as exc:
                raise NeedsConditions("条件の分母は非零である必要があります。") from exc
            if variable == "x" and ((operator == ">" and value >= 0) or (operator in {">=", "="} and value > 0)):
                stated_positive = True
            if variable == "x" and operator == ">" and value == 0:
                continue
            if variable == "x" and operator == ">" and value.denominator == 1 and 1 <= value <= 1000:
                atom = {"op": "x_gt", "value": value.numerator}
            else:
                atom = {"op": "compare", "variable": variable, "relation": relation_names[operator],
                        "value": {"numerator": value.numerator, "denominator": value.denominator}}
            if atom not in extras:
                extras.append(atom)
    zero_relations = {atom["relation"] for atom in extras if atom.get("variable") == "x" and atom["value"]["numerator"] == 0}
    stated_positive = stated_positive or {"ge", "ne"} <= zero_relations
    if not stated_positive or ((has_n or any(atom.get("variable") == "n" for atom in extras)) and not stated_integer):
        raise NeedsConditions("State a positive domain for x and, when n appears, n integer.")
    _condition_domains({"extra_conditions": extras})
    return extras


def _paper_notation(text: str) -> tuple[str, str | None]:
    """Remove verified layout only; multiple mathematical rows require confirmation."""
    text = text.strip()
    if text.startswith(r"\[") and text.endswith(r"\]"):
        text = text[2:-2]
    elif text.startswith("$"):
        delimiter = "$$" if text.startswith("$$") else "$"
        if len(text) < 2 * len(delimiter) or not text.endswith(delimiter):
            raise InputError("Mismatched TeX math delimiters.")
        text = text[len(delimiter):-len(delimiter)]
        if "$" in text:
            raise InputError("Mismatched or multiple TeX math delimiters.")
    stack = []
    parts = []
    end = 0
    top_start = None
    top_end = None
    for match in re.finditer(r"\\(begin|end)\{([A-Za-z*]+)\}", text):
        parts.append(text[end:match.start()])
        action, environment = match.groups()
        if environment not in {"equation", "equation*", "align", "align*", "aligned"}:
            raise InputError("Supported display environments are equation, align, and aligned.")
        if action == "begin":
            if not stack:
                if top_start is not None:
                    raise NeedsConditions("複数の数式環境があります。1つずつ検証対象を指定してください。")
                top_start = match.start()
            stack.append(environment)
        elif not stack or stack.pop() != environment:
            raise InputError("Mismatched TeX display environments.")
        elif not stack:
            top_end = match.end()
        end = match.end()
    parts.append(text[end:])
    if stack:
        raise InputError("Unclosed TeX display environment.")
    if top_start is not None and (text[:top_start].strip() or
            (text[top_end:].strip() and not text[top_end:].lstrip().startswith(";"))):
        raise NeedsConditions("数式環境の外に別の式があります。検証対象を1つにまとめてください。")
    text = "".join(parts)
    text = re.sub(r"\\operatorname\s*\{J\}", " J ", text)
    # A text block begins a trailing condition section. Its entire content survives.
    embedded = None
    marker = re.search(r"\\text\b", text)
    if marker:
        content, end = _tex_group(text, marker.end())
        before = text[:marker.start()]
        if "=" not in before:
            raise NeedsConditions("Place text conditions after the complete equation.")
        content = re.sub(r"^\s*(?:for\b|where\b|条件[:：]?|ただし)[ \t]*", "", content)
        embedded = content + text[end:]
        text = before
        if r"\text" in embedded or r"\\" in embedded or "&" in embedded:
            raise NeedsConditions("Combine all condition rows into one explicit condition list.")
    text = re.sub(r"\\(?:qquad|quad)\b", " ", text)
    rows = text.split(r"\\")
    if any(not row.strip(" &\n\t") for row in rows[:-1]):
        raise NeedsConditions("An empty or ambiguous equation row needs clarification.")
    for row in rows[1:]:
        continuation = row.strip(" &\n\t")
        if continuation and continuation[0] not in "+-=":
            raise NeedsConditions("次の数式行の意味が曖昧です。+、-、= で続く変形か、独立した式かを明示してください。")
    text = " ".join(rows).replace("&", " ")
    if re.split(r"(?<!\\);", text, maxsplit=1)[0].count("=") > 1:
        raise NeedsConditions("複数の等式が含まれています。検証する等式と条件を1組ずつ指定してください。")
    return text, embedded


def parse_identity(text: str, conditions: str | list[str] | None = None) -> dict[str, Any]:
    """Return the fixed target AST without a proof candidate."""
    if not isinstance(text, str) or len(text) > 32768:
        raise InputError("An equation must be at most 32768 characters of text.")
    try:
        text = _expand_macros(text)
        text, embedded = _paper_notation(text)
        separated = re.split(r"(?<!\\);", text, maxsplit=1)
        if len(separated) == 2:
            if embedded is not None or conditions is not None:
                raise NeedsConditions("Conditions were supplied twice; retain one explicit condition list.")
            text, conditions = separated
        if embedded is not None:
            if conditions is not None:
                raise NeedsConditions("Conditions were supplied twice; retain one explicit condition list.")
            conditions = embedded.strip(" ,; ")
        left, right = _Parser(text).equation()
        extra = _conditions(conditions, _contains_var(left, "n") or _contains_var(right, "n"))
        data = {"schema_version": 1, "assumptions": ["x > 0"],
                "lhs": _convert(left), "rhs": _convert(right)}
        if extra:
            data["extra_conditions"] = extra
        validate_request(data, require_proof=False)
        return data
    except RecursionError as exc:
        raise InputError("The equation exceeds the parser nesting limit.") from exc
