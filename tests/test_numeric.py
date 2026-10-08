import copy
from decimal import Decimal, localcontext
from fractions import Fraction
import math
import unittest
from unittest.mock import patch
from bessel_agent.core import load_json, ROOT
from bessel_agent.numeric import bessel_j, diagnose
from bessel_agent.parser import parse_identity

class NumericalDiagnosticsTests(unittest.TestCase):
    def test_half_integer_series_matches_closed_form(self):
        with localcontext() as c:
            c.prec = 60
            value = bessel_j(Fraction(1, 2), Decimal(1))
        expected = math.sqrt(2 / math.pi) * math.sin(1)
        self.assertAlmostEqual(float(value), expected, places=14)

    def test_known_identity_has_no_sample_mismatch(self):
        data = load_json(ROOT / 'demo/target.json')
        result = diagnose(data)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['checked_samples'], 28)
        self.assertEqual(result['candidates'], [])

    def test_numeric_mismatch_stays_a_candidate(self):
        data = copy.deepcopy(load_json(ROOT / 'demo/target.json'))
        data['rhs'] = {'op': 'add', 'args': [data['rhs'], {'op': 'int', 'value': 1}]}
        result = diagnose(data)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['diagnostic'], 'counterexample_candidates')
        self.assertTrue(result['candidates'])

    def test_wrong_recurrence_produces_only_unverified_candidates(self):
        data = load_json(ROOT / 'examples/numeric-recurrence-candidate.target.json')
        result = diagnose(data)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['candidates'][0]['n'], -3)
        self.assertEqual(result['candidates'][0]['x'], '0.5')
        self.assertGreater(Decimal(result['candidates'][0]['absolute_difference']), Decimal('0.01'))

    def test_half_integer_derivative_is_checked_by_finite_differences(self):
        data = parse_identity("D(J_{1/2}(x))=(1/(2*x))*J_{1/2}(x)-J_{3/2}(x)", "x > 0")
        result = diagnose(data)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 28)
        self.assertIn('central_difference_richardson', result['methods'])
        self.assertGreater(Decimal(result['largest_estimated_error']), 0)
        wrong = parse_identity("D(J_{1/2}(x))=(1/(2*x))*J_{1/2}(x)+J_{3/2}(x)", "x > 0")
        result = diagnose(wrong)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['diagnostic'], 'counterexample_candidates')

    def test_bessel_integral_uses_bounded_quadrature(self):
        data = parse_identity("int(0,x,t*J_0(t),t)=x*J_1(x)", "x > 0")
        result = diagnose(data)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 28)
        self.assertIn('open_midpoint_richardson', result['methods'])
        self.assertEqual(result['max_quadrature_subdivisions'], 512)
        wrong = parse_identity("int(0,x,t*J_0(t),t)=2*x*J_1(x)", "x > 0")
        result = diagnose(wrong)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['diagnostic'], 'counterexample_candidates')
        self.assertIn('comparison_tolerance', result['candidates'][0])

    def test_integral_derivative_binding_and_orientation(self):
        data = parse_identity("int(x,1,D(J_0(t)),t)=J_0(1)-J_0(x)", "x > 0")
        result = diagnose(data)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 28)
        self.assertIn('central_difference_richardson', result['methods'])

    def test_scope_failures_are_reported_without_candidates(self):
        data = parse_identity("int(0,x,J_0(1000*t),t)=0", "x > 0")
        result = diagnose(data)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['diagnostic'], 'unsupported_expression')
        self.assertTrue(result['skipped_reasons'])
        self.assertFalse(result['candidates'])

    def test_integrable_endpoint_singularity_uses_a_substitution(self):
        x = {'op': 'var', 'name': 'x'}
        data = {'schema_version': 1, 'assumptions': ['x > 0'],
                'lhs': {'op': 'integral', 'lower': {'op': 'int', 'value': 0}, 'upper': x,
                        'arg': {'op': 'real_rpow', 'base': x,
                                'exponent': {'op': 'rational', 'numerator': -1, 'denominator': 2}}},
                'rhs': {'op': 'mul', 'args': [{'op': 'int', 'value': 2}, {'op': 'sqrt', 'arg': x}]}}
        result = diagnose(data)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 28)
        self.assertIn('zero_endpoint_square_substitution', result['methods'])

    def test_extra_conditions_filter_only_the_outer_sample(self):
        data = parse_identity('int(0,x,t*J_0(t),t)=x*J_1(x)', 'x > 0')
        data['extra_conditions'] = [{'op': 'x_gt', 'value': 2}]
        result = diagnose(data)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 7)
        self.assertEqual(result['excluded_by_conditions'], 21)
        data['extra_conditions'][0]['value'] = 3
        result = diagnose(data)
        self.assertEqual(result['diagnostic'], 'no_eligible_samples')
        self.assertEqual(result['checked_samples'], 0)
        self.assertEqual(result['status'], 'unresolved')

    def test_half_integer_weighted_integral_on_a_positive_interval(self):
        data = parse_identity('int(1,x,sqrt(t)*J_{-1/2}(t),t)=sqrt(x)*J_{1/2}(x)-J_{1/2}(1)', 'x > 0')
        result = diagnose(data)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 28)
        self.assertEqual(result['status'], 'unresolved')

    def test_quarter_order_gamma_rounding_does_not_create_candidates(self):
        target = parse_identity('J_{-3/4}(x)+J_{5/4}(x)=1/(2*x)*J_{1/4}(x)', 'x > 0')
        original_gamma = math.gamma
        def rounded_gamma(argument):
            return original_gamma(argument) * (1 + (1e-14 if argument < 1 else -1e-14))
        with patch('bessel_agent.numeric.math.gamma', side_effect=rounded_gamma):
            result = diagnose(target)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 28)
        self.assertIn('binary64_gamma_for_rational_order', result['methods'])
        self.assertGreater(Decimal(result['largest_estimated_error']), Decimal('1e-12'))
        self.assertEqual(result['general_rational_relative_tolerance'], '1e-10')

    def test_quarter_order_derivative_reports_gamma_uncertainty(self):
        target = parse_identity('D(J_{1/4}(x))=1/(4*x)*J_{1/4}(x)-J_{5/4}(x)', 'x > 0')
        result = diagnose(target)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 28)
        self.assertIn('binary64_gamma_for_rational_order', result['methods'])
        wrong = parse_identity('D(J_{1/4}(x))=1/(4*x)*J_{1/4}(x)+J_{5/4}(x)', 'x > 0')
        result = diagnose(wrong)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['diagnostic'], 'counterexample_candidates')

    def test_mixed_scalar_conditions_filter_n_and_x_exactly(self):
        target = load_json(ROOT / 'demo/target.json')
        def condition(variable, relation, p, q=1):
            return {'op': 'compare', 'variable': variable, 'relation': relation,
                    'value': {'numerator': p, 'denominator': q}}
        target['extra_conditions'] = [condition('n', 'ge', 1), condition('n', 'le', 2),
                                      condition('x', 'le', 2), condition('x', 'ne', 1)]
        result = diagnose(target)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 4)
        self.assertEqual(result['excluded_by_conditions'], 24)

    def test_origin_bessel_singularity_and_wrong_coefficient(self):
        target = parse_identity((ROOT / 'examples/origin-singular-composed.txt').read_text())
        result = diagnose(target)
        self.assertEqual(result['diagnostic'], 'no_mismatch_found')
        self.assertEqual(result['checked_samples'], 14)
        self.assertEqual(result['excluded_by_conditions'], 14)
        self.assertIn('zero_endpoint_square_substitution', result['methods'])
        self.assertIn('binary64_gamma_for_rational_order', result['methods'])
        wrong = copy.deepcopy(target)
        wrong['rhs'] = {'op': 'add', 'args': [wrong['rhs'], {'op': 'int', 'value': 1}]}
        result = diagnose(wrong)
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['diagnostic'], 'counterexample_candidates')
