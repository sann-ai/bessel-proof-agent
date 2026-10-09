"""Version 2 boundaries, positive-real sampling, and conditional evidence."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from bessel_agent import archive
from bessel_agent.core import InputError, NeedsConditions, ROOT, render_lean, replay, validate_request, verify
from bessel_agent.generate import generate
from bessel_agent.parser import parse_identity
from bessel_agent.real_bessel import domain_obligations, template_match
from bessel_agent.real_numeric import diagnose

TEXT = (ROOT/'examples/cross-product-root.txt').read_text()


def request(text=TEXT):
    return {**parse_identity(text), 'proof': {'mode': 'diagnostic'}}


class RealParserTests(unittest.TestCase):
    def test_preserves_root_and_typed_parameters(self):
        target = parse_identity(TEXT)
        self.assertEqual(target['variables'], {'lambda': 'real', 'z': 'real'})
        self.assertEqual(len(target['assumptions']), 4)
        self.assertEqual(target['assumptions'][-1]['lhs']['op'], 'bessel_cross')
        self.assertIsNotNone(template_match(target))
        self.assertEqual(domain_obligations(target, template_match(target)), [])

    def test_y_generic_orders_two_variables_and_tex(self):
        for text in [
            'Y_{n-1}(x)+Y_{n+1}(x)=2*n/x*Y_n(x); n integer,x>0',
            'Y_{1/2}(z)=Y(1/2,z); z>0',
            'X(0,1,s,w)=X_{0,1}(s,w); s>0,w>0',
            TEXT.replace('lambda', r'\lambda'),
            TEXT.replace('lambda', 'λ'),
        ]:
            with self.subTest(text=text):
                validate_request(parse_identity(text), require_proof=False)
        with self.assertRaises(NeedsConditions):
            parse_identity('Y_n(x)=Y_n(x); x>0')

    def test_root_and_formula_changes_do_not_match_template(self):
        cases = [TEXT.replace(', X_01(z,lambda*z) = 0', ''),
                 TEXT.replace('X_02(z,lambda*z)', 'X_01(z,lambda*z)'),
                 TEXT.replace('(1/lambda)', '(2/lambda)'),
                 TEXT.replace('0 < lambda < 1', '0 < lambda <= 1')]
        for text in cases:
            target = parse_identity(text)
            self.assertIsNone(template_match(target))
            self.assertTrue(domain_obligations(target, None))

    def test_conditions_are_not_replaced_or_silently_strengthened(self):
        target = parse_identity('1/Y_0(x)=1/Y_0(x); x>0')
        self.assertEqual(domain_obligations(target, None), ['Y_{0}(x) != 0'])
        explicit = parse_identity('1/Y_0(x)=1/Y_0(x); x>0,Y_0(x)!=0')
        self.assertEqual(domain_obligations(explicit, None), [])
        for text in ['Y_0(x)=Y_0(x); x>=0', 'Y_0(z)=Y_0(z); z<0']:
            self.assertTrue(domain_obligations(parse_identity(text), None))
        extra = parse_identity(TEXT.strip()+', Y_0(-z)!=0')
        self.assertIn('(-z) > 0', domain_obligations(extra, template_match(extra)))

    def test_conflicting_invalid_and_injected_inputs(self):
        for text in [TEXT.strip()+',lambda=0', TEXT.strip()+',lambda=1',
                     TEXT.strip()+',z<=0', 'Y_0(x)=Y_0(x);x>0,Y_0(x)=0,Y_0(x)!=0',
                     'Y_0(x)=0;x>0,Y_0(x)=0']:
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text)
        for field,value in [('variables',{'z':'complex'}),('proof',{'mode':'direct','recipe':'ring'})]:
            data=request();data[field]=value
            with self.assertRaises(InputError): validate_request(data)
        data=request();data['lhs']={'op':['bad']}
        with self.assertRaises(InputError): validate_request(data)
        with self.assertRaises(InputError): render_lean(request())
        with self.assertRaises(InputError): parse_identity('Y_0(x)=Y_0(x);x>0; axiom bad')

    def test_archive_identity_includes_every_condition(self):
        target=parse_identity(TEXT)
        changed=copy.deepcopy(target);changed['assumptions'].pop()
        self.assertNotEqual(archive.target_hash(target),archive.target_hash(changed))
        reordered=copy.deepcopy(target);reordered['assumptions'].reverse()
        self.assertEqual(archive.target_hash(target),archive.target_hash(reordered))


class RealDiagnosticTests(unittest.TestCase):
    def test_missing_backend_and_missing_domain_are_saved(self):
        with patch('bessel_agent.real_numeric.importlib.import_module',side_effect=ImportError), tempfile.TemporaryDirectory() as directory:
            data=request('1/Y_0(x)=1/Y_0(x);x>0')
            result=verify(data,Path(directory)/'run')
            self.assertEqual(result['status'],'needs_conditions')
            self.assertEqual(result['numerical']['diagnostic'],'backend_unavailable')
            self.assertFalse(result['full_bessel_proof'])
            saved=archive.register_verification(Path(directory)/'run',Path(directory)/'archive',original_input='original')
            self.assertEqual(saved['status'],'needs_conditions')
            self.assertEqual(saved['request'],data)
            self.assertTrue((Path(saved['verification_dir'])/'numerical.json').exists())

    def test_generator_never_calls_ai_for_extended_targets(self):
        for route in ['direct','steps']:
            with tempfile.TemporaryDirectory() as directory, patch('bessel_agent.generate.subprocess.Popen') as process, patch('bessel_agent.real_numeric.importlib.import_module',side_effect=ImportError):
                target=parse_identity('Y_0(x)=Y_0(x);x>0')
                result=generate(target,route,Path(directory)/'run',archive=True,
                                archive_dir=Path(directory)/'archive')
                process.assert_not_called()
                self.assertEqual(result['status'],'unresolved')
                self.assertFalse(result['generation']['ai_called'])
                self.assertFalse(result['full_bessel_proof'])
                record=archive.show_record(result['archive_id'],Path(directory)/'archive')
                self.assertFalse(record['provenance']['ai_called'])
                self.assertEqual(record['provenance']['requested_route'],route)

    @unittest.skipUnless(importlib.util.find_spec('mpmath'), 'uses an existing mpmath runtime')
    def test_y_recurrence_and_wrong_coefficient(self):
        correct='Y_0(x)+Y_2(x)=2/x*Y_1(x);x>0'
        result=diagnose(parse_identity(correct))
        self.assertEqual(result['diagnostic'],'no_mismatch_found')
        self.assertGreater(result['checked_samples'],0)
        bad=diagnose(parse_identity(correct.replace('2/x','3/x')))
        self.assertEqual(bad['diagnostic'],'counterexample_candidates')
        self.assertEqual(bad['status'],'unresolved')
        rational=diagnose(parse_identity('Y_0(x)=Y_0(x);x=1/3'))
        self.assertEqual(rational['checked_samples'],1)
        self.assertEqual(rational['excluded_by_conditions'],0)

    @unittest.skipUnless(importlib.util.find_spec('mpmath'), 'uses an existing mpmath runtime')
    def test_general_y_root_samples_obey_conditions(self):
        result=diagnose(parse_identity('Y_0(x)^2=0;x>0,x<4,Y_0(x)=0'))
        self.assertEqual(result['diagnostic'],'no_mismatch_found')
        self.assertGreater(result['checked_samples'],0)
        for sample in result['samples']:
            self.assertGreater(float(sample['values']['x']),0)
            self.assertLess(float(sample['values']['x']),4)
            self.assertLess(float(sample['condition_residuals'][0]['absolute_value']),1e-35)
        system=diagnose(parse_identity('Y_0(x)^2=0;x>0,Y_0(x)=0,Y_1(x)=0'))
        self.assertEqual(system['diagnostic'],'unsupported_root_system')

    @unittest.skipUnless(importlib.util.find_spec('mpmath'), 'uses an existing mpmath runtime')
    def test_photographed_fraction_and_misread_factor(self):
        result=diagnose(parse_identity(TEXT))
        self.assertEqual(result['diagnostic'],'no_mismatch_found')
        self.assertEqual(result['checked_samples'],9)
        bad=diagnose(parse_identity(TEXT.replace('X_02(z,lambda*z)','X_01(z,lambda*z)')))
        self.assertEqual(bad['diagnostic'],'counterexample_candidates')

    @unittest.skipUnless(os.environ.get('BESSEL_RUN_LEAN_TESTS')=='1','opt-in Lean execution')
    def test_conditional_lean_replay_and_tamper_boundary(self):
        with tempfile.TemporaryDirectory() as directory, patch('bessel_agent.real_numeric.importlib.import_module',side_effect=ImportError):
            output=Path(directory)/'run'
            result=verify(request(),output)
            self.assertEqual(result['status'],'unresolved')
            self.assertTrue(result['conditional_lean']['accepted'])
            replayed=replay(output)
            self.assertFalse(replayed['replayed'])
            self.assertTrue(replayed['conditional_replayed'])
            self.assertFalse(replayed['full_bessel_proof'])
            saved=archive.register_verification(output,Path(directory)/'archive')
            self.assertTrue(archive.replay_record(saved['id'],Path(directory)/'archive')['conditional_replayed'])
            certificate=output/'conditional_certificate.lean'
            certificate.write_text(certificate.read_text()+'\n-- modified\n')
            with self.assertRaises(InputError): replay(output)
            saved_result=json.loads((output/'result.json').read_text());saved_result['status']='proved'
            (output/'result.json').write_text(json.dumps(saved_result))
            with self.assertRaises(InputError): archive.register_verification(output,Path(directory)/'other')


if __name__=='__main__': unittest.main()
