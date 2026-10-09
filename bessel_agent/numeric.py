"""Bounded numerical diagnostics. Every mismatch remains an unverified candidate."""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from decimal import Decimal, localcontext
from fractions import Fraction
import json
import math
from pathlib import Path

from .core import condition_holds, normalized_conditions, load_json, validate_request

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
    elif order.denominator > 1 and x > 0:
        q = Decimal(order.numerator) / Decimal(order.denominator)
        try:
            gamma = Decimal(str(math.gamma(float(order + 1))))
        except (ValueError, OverflowError) as exc:
            raise NumericalScopeError('The rational-order Gamma approximation exceeded its numerical scope.') from exc
        term = (x / 2) ** q / gamma
    else:
        raise NumericalScopeError('Noninteger numerical orders require a positive argument.')
    result = term
    q = Decimal(order.numerator) / Decimal(order.denominator)
    for k in range(1, 501):
        term *= -(x / 2) ** 2 / (Decimal(k) * (q + k))
        result += term
        if k > abs(q) + abs(x) + 5 and abs(term) < Decimal('1e-48'):
            return result * sign
    raise NumericalScopeError('The bounded series did not converge to the diagnostic tolerance.')


@dataclass
class Estimate:
    value: Decimal
    error: Decimal = Decimal(0)


@dataclass
class EvaluationContext:
    remaining: int = 50000
    methods: set[str] = field(default_factory=set)


def _rational(node: dict) -> Fraction:
    if node['op'] == 'int':
        return Fraction(node['value'])
    return Fraction(node['numerator'], node['denominator'])


def _has_fractional_expression(node: dict) -> bool:
    if node['op'] in {'real_rpow', 'sqrt'}:
        return True
    if node['op'] == 'bessel_j' and node['order']['op'] == 'rational':
        return True
    return any(_has_fractional_expression(value) for value in node.values() if isinstance(value, dict)) or any(
        _has_fractional_expression(arg) for value in node.values() if isinstance(value, list)
        for arg in value if isinstance(arg, dict))


def _eval(node: dict, n: int, x: Decimal, ctx: EvaluationContext, calculus_depth: int = 0) -> Estimate:
    ctx.remaining -= 1
    if ctx.remaining < 0:
        raise NumericalScopeError('The sample exceeded 50000 expression evaluations.')
    op = node['op']
    child = lambda arg, at=x: _eval(arg, n, at, ctx, calculus_depth)
    if op == 'int':
        return Estimate(Decimal(node['value']))
    if op == 'var' and node['name'] == 'x':
        return Estimate(x)
    if op == 'int_cast':
        return Estimate(Decimal(_integer(node['arg'], n)))
    if op == 'neg':
        a = child(node['arg'])
        return Estimate(-a.value, a.error)
    if op in ('add', 'sub', 'mul', 'div'):
        a, b = (child(v) for v in node['args'])
        if op in ('add', 'sub'):
            return Estimate(a.value + b.value if op == 'add' else a.value - b.value, a.error + b.error)
        if op == 'mul':
            return Estimate(a.value * b.value,
                            abs(a.value) * b.error + abs(b.value) * a.error + a.error * b.error)
        if abs(b.value) <= b.error:
            raise NumericalScopeError('A sampled denominator is zero or too close to its estimated error.')
        value = a.value / b.value
        return Estimate(value, (a.error + abs(value) * b.error) / (abs(b.value) - b.error))
    if op in ('pow', 'zpow', 'real_rpow', 'sqrt'):
        if op == 'sqrt':
            exponent, base = Fraction(1, 2), child(node['arg'])
        else:
            exponent = (_rational(node['exponent']) if op == 'real_rpow' else
                        Fraction(node['exponent'] if op == 'pow' else _integer(node['exponent'], n)))
            base = child(node['base'])
        if abs(exponent) > 100:
            raise NumericalScopeError('Sampled exponent exceeds 100.')
        if (base.value < 0 and exponent.denominator != 1) or (not base.value and exponent < 0):
            raise NumericalScopeError('The sampled power needs a positive base or a nonsingular endpoint.')
        q = Decimal(exponent.numerator) / Decimal(exponent.denominator)
        value = base.value ** q if q else Decimal(1)
        if base.value:
            error = abs(q * value / base.value) * base.error
        elif base.error:
            raise NumericalScopeError('A power at zero has uncertain input.')
        else:
            error = Decimal(0)
        return Estimate(value, error + Decimal('1e-45') * max(Decimal(1), abs(value)))
    if op == 'bessel_j':
        order = node['order']
        q = _rational(order) if order['op'] == 'rational' else Fraction(_integer(order, n))
        argument = child(node['arg'])
        value = bessel_j(q, argument.value)
        propagated = Decimal(0)
        if argument.error:
            slope = (bessel_j(q - 1, argument.value) - bessel_j(q + 1, argument.value)) / 2
            propagated = abs(slope) * argument.error
        ctx.methods.add('bounded_bessel_series')
        if q.denominator not in (1, 2):
            ctx.methods.add('binary64_gamma_for_rational_order')
            scale_error = Decimal('1e-12')
        else:
            scale_error = Decimal('1e-45')
        return Estimate(value, propagated + scale_error * max(Decimal(1), abs(value)))
    if op in ('deriv', 'integral'):
        if calculus_depth >= 2:
            raise NumericalScopeError('Numerical calculus nesting is limited to 2 levels.')
        inner = lambda at: _eval(node['arg'], n, at, ctx, calculus_depth + 1)
        if op == 'deriv':
            ctx.methods.add('central_difference_richardson')
            h = Decimal('1e-6') * max(Decimal(1), abs(x))
            if x > 0:
                h = min(h, x / 4)
            estimates = []
            for step in (h, h / 2):
                plus, minus = inner(x + step), inner(x - step)
                estimates.append(Estimate((plus.value - minus.value) / (2 * step),
                                          (plus.error + minus.error) / (2 * step)))
            coarse, fine = estimates
            value = (4 * fine.value - coarse.value) / 3
            error = abs(fine.value - coarse.value) / 3 + (4 * fine.error + coarse.error) / 3
            return Estimate(value, error)
        lower, upper = child(node['lower']), child(node['upper'])
        if lower.error > Decimal('1e-30') or upper.error > Decimal('1e-30'):
            raise NumericalScopeError('Integral endpoints have excessive numerical uncertainty.')
        a, b = lower.value, upper.value
        if a == b:
            return Estimate(Decimal(0))
        direction = Decimal(1)
        if a > b:
            a, b, direction = b, a, Decimal(-1)
        # An open quadrature avoids evaluating undefined endpoint expressions.
        # The squared substitution resolves the supported t^(-1/2) endpoint.
        squared = a == 0 and b > 0 and _has_fractional_expression(node['arg'])
        ctx.methods.add('open_midpoint_richardson')
        if squared:
            ctx.methods.add('zero_endpoint_square_substitution')
        previous_midpoint = previous_extrapolated = None
        for count in (8, 16, 32, 64, 128, 256, 512):
            total, propagated = Decimal(0), Decimal(0)
            for k in range(count):
                u = (Decimal(k) + Decimal('0.5')) / count
                at = a + (b - a) * (u * u if squared else u)
                weight = (b - a) * (2 * u if squared else 1)
                value = inner(at)
                total += weight * value.value
                propagated += abs(weight) * value.error
            midpoint = Estimate(total / count, propagated / count)
            if previous_midpoint is not None:
                extrapolated = Estimate((4 * midpoint.value - previous_midpoint.value) / 3,
                                        (4 * midpoint.error + previous_midpoint.error) / 3)
                if previous_extrapolated is not None:
                    error = abs(extrapolated.value - previous_extrapolated.value) / 15 + extrapolated.error
                    if error <= Decimal('1e-10') * max(Decimal(1), abs(extrapolated.value)):
                        return Estimate(direction * extrapolated.value, error)
                previous_extrapolated = extrapolated
            previous_midpoint = midpoint
        raise NumericalScopeError('Quadrature refinement did not converge within 512 subdivisions.')
    raise NumericalScopeError(f'Numerical sampling does not implement {op}.')


def evaluate(node: dict, n: int, x: Decimal) -> Decimal:
    """Evaluate a supported expression; use diagnose for error estimates and scope metadata."""
    return _eval(node, n, x, EvaluationContext()).value


def diagnose(target: dict) -> dict:
    validate_request(target, require_proof=False)
    if target["schema_version"] == 2:
        from .real_numeric import diagnose as diagnose_real
        return diagnose_real(target)
    conditions = normalized_conditions(target)
    mismatches = []
    skipped = set()
    checked = excluded = 0
    methods = set()
    max_error = Decimal(0)
    with localcontext() as context:
        context.prec = 60
        for n in range(-3, 4):
            for sample in ('0.5', '1', '2', '3'):
                x = Decimal(sample)
                if any(not condition_holds(condition, n, Fraction(x)) for condition in conditions):
                    excluded += 1
                    continue
                ctx = EvaluationContext()
                try:
                    left = _eval(target['lhs'], n, x, ctx)
                    right = _eval(target['rhs'], n, x, ctx)
                except (ArithmeticError, NumericalScopeError) as exc:
                    skipped.add(str(exc))
                    methods.update(ctx.methods)
                    continue
                methods.update(ctx.methods)
                checked += 1
                error = abs(left.value - right.value)
                estimated_error = left.error + right.error
                max_error = max(max_error, estimated_error)
                has_calculus = bool(ctx.methods & {'central_difference_richardson', 'open_midpoint_richardson'})
                has_general_rational = 'binary64_gamma_for_rational_order' in ctx.methods
                relative = (Decimal('1e-9') if has_calculus else
                            Decimal('1e-10') if has_general_rational else Decimal('1e-25'))
                tolerance = max(relative * max(Decimal(1), abs(left.value), abs(right.value)), 10 * estimated_error)
                if error > tolerance:
                    mismatches.append({'n': n, 'x': sample, 'lhs': str(left.value), 'rhs': str(right.value),
                                       'absolute_difference': str(error), 'estimated_numerical_error': str(estimated_error),
                                       'comparison_tolerance': str(tolerance)})
                    if len(mismatches) == 3:
                        break
            if len(mismatches) == 3:
                break
    diagnostic = ('counterexample_candidates' if mismatches else
                  'no_mismatch_found' if checked else
                  'no_eligible_samples' if excluded and not skipped else 'unsupported_expression')
    return {'status': 'unresolved', 'diagnostic': diagnostic,
            'checked_samples': checked, 'excluded_by_conditions': excluded,
            'candidates': mismatches, 'skipped_reasons': sorted(skipped),
            'precision_digits': 60, 'relative_tolerance': '1e-25', 'calculus_relative_tolerance': '1e-9',
            'general_rational_relative_tolerance': '1e-10', 'general_rational_gamma_backend': 'math.gamma_binary64',
            'max_series_terms': 500, 'max_quadrature_subdivisions': 512, 'max_evaluations_per_sample': 50000,
            'methods': sorted(methods), 'largest_estimated_error': str(max_error),
            'error_estimate_kind': 'empirical_refinement_difference',
            'explanation': '有限標本の数値診断です。微分は中心差分、積分は開区間求積の細分差から誤差を推定します。打切り・収束失敗は記録し、反証の確定には元命題の否定をLeanで検査します。'}


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
