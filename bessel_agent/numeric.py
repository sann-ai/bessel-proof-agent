"""Bounded numerical diagnostics. Every mismatch remains an unverified candidate."""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
import math
from pathlib import Path

from .core import load_json, validate_request

PI = Decimal('3.14159265358979323846264338327950288419716939937510582097494459')


class NumericalScopeError(ValueError):
    pass


def _integer(node: dict, n: int) -> int:
    op = node['op']
    if op == 'int':
        return node['value']
    if op == 'var' and node['name'] == 'n':
        return n
    if op == 'neg':
        return -_integer(node['arg'], n)
    if op in ('add', 'sub', 'mul'):
        a, b = (_integer(v, n) for v in node['args'])
        return {'add': lambda: a + b, 'sub': lambda: a - b, 'mul': lambda: a * b}[op]()
    raise NumericalScopeError('Unsupported integer expression.')


def bessel_j(order: Fraction, x: Decimal) -> Decimal:
    """Evaluate the defining real series with 60-digit arithmetic and bounded inputs."""
    if abs(order) > 20 or abs(x) > 12:
        raise NumericalScopeError('Numerical scope is |order| <= 20 and |argument| <= 12.')
    sign = 1
    if order.denominator == 1:
        n = int(order)
        if n < 0:
            sign *= -1 if (-n) % 2 else 1
            n = -n
        if x < 0:
            sign *= -1 if n % 2 else 1
            x = -x
        order = Fraction(n)
        term = (x / 2) ** n / Decimal(math.factorial(n)) if n else Decimal(1)
    elif order.denominator == 2 and x > 0:
        m = order.numerator // 2
        a = Decimal(order.numerator) / 2 + 1
        gamma, t = PI.sqrt(), Decimal('0.5')
        while t < a:
            gamma *= t
            t += 1
        while t > a:
            t -= 1
            gamma /= t
        term = (x / 2) ** m * (x / 2).sqrt() / gamma
    else:
        raise NumericalScopeError('Numerics supports integer orders and half-integers at positive arguments.')
    result = term
    q = Decimal(order.numerator) / Decimal(order.denominator)
    for k in range(1, 501):
        term *= -(x / 2) ** 2 / (Decimal(k) * (q + k))
        result += term
        if k > abs(q) + abs(x) + 5 and abs(term) < Decimal('1e-48'):
            return result * sign
    raise NumericalScopeError('The bounded series did not converge to the diagnostic tolerance.')


def evaluate(node: dict, n: int, x: Decimal) -> Decimal:
    op = node['op']
    if op == 'int':
        return Decimal(node['value'])
    if op == 'var' and node['name'] == 'x':
        return x
    if op == 'int_cast':
        return Decimal(_integer(node['arg'], n))
    if op == 'neg':
        return -evaluate(node['arg'], n, x)
    if op in ('add', 'sub', 'mul', 'div'):
        a, b = (evaluate(v, n, x) for v in node['args'])
        if op == 'add': return a + b
        if op == 'sub': return a - b
        if op == 'mul': return a * b
        if not b: raise NumericalScopeError('A sampled denominator is zero.')
        return a / b
    if op in ('pow', 'zpow'):
        exponent = node['exponent'] if op == 'pow' else _integer(node['exponent'], n)
        if abs(exponent) > 100:
            raise NumericalScopeError('Sampled exponent exceeds 100.')
        base = evaluate(node['base'], n, x)
        if not base and exponent < 0:
            raise NumericalScopeError('A sampled negative power has zero base.')
        return base ** exponent if exponent else Decimal(1)
    if op == 'bessel_j':
        order = node['order']
        q = (Fraction(order['numerator'], order['denominator']) if order['op'] == 'rational'
             else Fraction(_integer(order, n)))
        return bessel_j(q, evaluate(node['arg'], n, x))
    raise NumericalScopeError(f'Numerical sampling does not implement {op}.')


def diagnose(target: dict) -> dict:
    validate_request(target, require_proof=False)
    mismatches = []
    skipped = set()
    checked = 0
    with localcontext() as context:
        context.prec = 60
        for n in range(-3, 4):
            for sample in ('0.5', '1', '2', '3'):
                try:
                    left = evaluate(target['lhs'], n, Decimal(sample))
                    right = evaluate(target['rhs'], n, Decimal(sample))
                except (ArithmeticError, NumericalScopeError) as exc:
                    skipped.add(str(exc))
                    continue
                checked += 1
                error = abs(left - right)
                tolerance = Decimal('1e-25') * max(Decimal(1), abs(left), abs(right))
                if error > tolerance:
                    mismatches.append({'n': n, 'x': sample, 'lhs': str(left), 'rhs': str(right),
                                       'absolute_difference': str(error)})
                    if len(mismatches) == 3:
                        break
            if len(mismatches) == 3:
                break
    diagnostic = ('counterexample_candidates' if mismatches else
                  'no_mismatch_found' if checked else 'unsupported_expression')
    return {'status': 'unresolved', 'diagnostic': diagnostic,
            'checked_samples': checked, 'candidates': mismatches, 'skipped_reasons': sorted(skipped),
            'precision_digits': 60, 'relative_tolerance': '1e-25', 'max_series_terms': 500,
            'explanation': '有限個の点で級数を数値評価した診断です。反証の確定には元命題の否定をLeanで検査します。'}


def main() -> int:
    parser = argparse.ArgumentParser(description='Bounded numerical counterexample candidates')
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        result = diagnose(load_json(args.input))
    except (ValueError, OSError) as exc:
        result = {'status': 'unresolved', 'diagnostic': 'input_error', 'error': str(exc)}
    text = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
    if args.output:
        if args.output.exists():
            parser.error('Output already exists.')
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
