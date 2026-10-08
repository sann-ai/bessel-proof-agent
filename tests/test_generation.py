"""Exercise the AI/verifier boundary without network access."""
import copy
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from bessel_agent.core import InputError, NeedsConditions
from bessel_agent.generate import ROOT, generate, output_schema


class GenerationBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.target = json.loads((ROOT / 'demo/target.json').read_text())

    def candidate_process(self, candidate):
        def start(command, **kwargs):
            path = Path(command[command.index('--output-last-message') + 1])
            path.write_text(json.dumps(candidate))
            self.assertEqual(command[command.index('--sandbox') + 1], 'read-only')
            self.assertIn('model_reasoning_effort="ultra"', command)
            return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))
        return start

    def test_model_proof_preserves_original_target(self):
        original = copy.deepcopy(self.target)
        proof = {'mode': 'direct', 'recipe': 'bessel'}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(proof)), \
             patch('bessel_agent.generate.verify', return_value={'status': 'proved'}) as verify:
            result = generate(self.target, 'direct', Path(temp) / 'result')
            self.assertEqual(result['status'], 'proved')
            self.assertEqual(verify.call_args.args[0], {**original, 'proof': proof})
            self.assertEqual(self.target, original)

    def test_model_cannot_replace_theorem_or_add_assumptions(self):
        candidate = {'mode': 'direct', 'recipe': 'bessel', 'assumptions': ['False']}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(candidate)), \
             patch('bessel_agent.generate.verify') as verify:
            with self.assertRaises(InputError):
                generate(self.target, 'direct', Path(temp) / 'result')
            verify.assert_not_called()

    def test_missing_conditions_do_not_invoke_ai(self):
        self.target['assumptions'] = []
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.subprocess.Popen') as run:
            with self.assertRaises(NeedsConditions):
                generate(self.target, 'direct', Path(temp) / 'result')
            run.assert_not_called()

    def test_checked_refutation_stops_retries(self):
        proof = {'mode': 'direct', 'recipe': 'bessel'}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(proof)) as run, \
             patch('bessel_agent.generate.verify', return_value={'status': 'refuted'}):
            result = generate(self.target, 'direct', Path(temp) / 'result', attempts=3)
            self.assertEqual(result['status'], 'refuted')
            self.assertEqual(run.call_count, 1)

    def test_extra_conditions_remain_part_of_the_fixed_target(self):
        self.target['extra_conditions'] = [{'op': 'x_gt', 'value': 1}]
        original = copy.deepcopy(self.target)
        proof = {'mode': 'direct', 'recipe': 'bessel'}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(proof)), \
             patch('bessel_agent.generate.verify', return_value={'status': 'proved'}) as verify:
            generate(self.target, 'direct', Path(temp) / 'result')
            self.assertEqual(verify.call_args.args[0], {**original, 'proof': proof})
        schema = output_schema('steps', self.target)
        self.assertEqual(schema['properties']['steps']['items']['properties']['conditions']['items']['enum'],
                         ['x > 0', 'x > 1'])

    def test_model_cannot_inject_extra_conditions(self):
        candidate = {'mode': 'direct', 'recipe': 'bessel',
                     'extra_conditions': [{'op': 'x_gt', 'value': 99}]}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(candidate)), \
             patch('bessel_agent.generate.verify') as verify:
            with self.assertRaises(InputError):
                generate(self.target, 'direct', Path(temp) / 'result')
            verify.assert_not_called()

    def test_general_scalar_conditions_are_kept_in_generation(self):
        self.target['extra_conditions'] = [
            {'op': 'compare', 'variable': 'n', 'relation': 'ge', 'value': {'numerator': 2, 'denominator': 1}},
            {'op': 'compare', 'variable': 'x', 'relation': 'lt', 'value': {'numerator': 1, 'denominator': 1}},
            {'op': 'compare', 'variable': 'x', 'relation': 'ne', 'value': {'numerator': 1, 'denominator': 2}}]
        original = copy.deepcopy(self.target)
        proof = {'mode': 'direct', 'recipe': 'bessel'}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(proof)), \
             patch('bessel_agent.generate.verify', return_value={'status': 'proved'}) as verify:
            generate(self.target, 'direct', Path(temp) / 'result')
            self.assertEqual(verify.call_args.args[0], {**original, 'proof': proof})
        labels = output_schema('steps', self.target)['properties']['steps']['items']['properties']['conditions']['items']['enum']
        self.assertEqual(labels, ['x > 0', 'n >= 2', 'x < 1', 'x != 1/2'])
