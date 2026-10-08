import copy
from decimal import Decimal, localcontext
from fractions import Fraction
import math
import unittest
from bessel_agent.core import load_json, ROOT
from bessel_agent.numeric import bessel_j, diagnose

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
