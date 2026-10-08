"""Exercise the AI/verifier boundary without network access."""
import copy
from contextlib import redirect_stderr
import io
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

    def test_exact_archive_hit_is_rechecked_before_reuse_without_ai(self):
        proof = {'mode': 'direct', 'recipe': 'bessel'}
        record = {'id': 'saved', 'status': 'proved', 'candidate': proof}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.archive.find_exact', return_value=[record]), \
             patch('bessel_agent.archive.replay_record', return_value={'replayed': True}) as replay, \
             patch('bessel_agent.archive.register_verification', return_value={'id': 'new'}) as register, \
             patch('bessel_agent.generate.verify', return_value={'status': 'proved'}) as verify, \
             patch('bessel_agent.generate.shutil.which') as which, \
             patch('bessel_agent.generate.subprocess.Popen') as run:
            result = generate(self.target, 'direct', Path(temp) / 'result', archive=True,
                              archive_dir=Path(temp) / 'archive')
            replay.assert_called_once()
            verify.assert_called_once()
            self.assertEqual(verify.call_args.args[0], {**self.target, 'proof': proof})
            self.assertEqual(register.call_args.kwargs['provenance']['reused_record_id'], 'saved')
            self.assertFalse(result['reuse']['ai_called'])
            which.assert_not_called()
            run.assert_not_called()

    def test_stale_archive_result_is_not_accepted_as_a_proof(self):
        proof = {'mode': 'direct', 'recipe': 'bessel'}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.archive.find_exact', return_value=[{'id': 'old', 'status': 'proved', 'candidate': proof}]), \
             patch('bessel_agent.archive.replay_record', side_effect=InputError('Environment changed')), \
             patch('bessel_agent.archive.register_verification', return_value={'id': 'new'}), \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(proof)) as run, \
             patch('bessel_agent.generate.verify', return_value={'status': 'unresolved'}):
            out = Path(temp) / 'result'
            result = generate(self.target, 'direct', out, archive=True, archive_dir=Path(temp) / 'archive')
            self.assertEqual(result['status'], 'unresolved')
            self.assertNotIn('reuse', result)
            self.assertEqual(run.call_count, 1)
            self.assertIn('Environment changed', (out / 'archive-reuse-skipped.json').read_text())

    def test_archived_invalid_candidate_keeps_the_fixed_original_input(self):
        candidate = {'mode': 'direct', 'recipe': 'bessel', 'assumptions': ['False']}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.archive.find_exact', return_value=[]), \
             patch('bessel_agent.archive.register_failure', return_value={'id': 'failed'}) as failure, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(candidate)), \
             patch('bessel_agent.generate.verify') as verify:
            with self.assertRaises(InputError):
                generate(self.target, 'direct', Path(temp) / 'result', archive=True,
                         archive_dir=Path(temp) / 'archive')
            verify.assert_not_called()
            self.assertEqual(failure.call_args.kwargs['request'], self.target)
            self.assertEqual(failure.call_args.kwargs['candidate'], candidate)
            self.assertEqual(failure.call_args.args[0]['status'], 'unresolved')

    def test_each_generated_attempt_is_archived(self):
        proof = {'mode': 'direct', 'recipe': 'bessel'}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.archive.find_exact', return_value=[]), \
             patch('bessel_agent.archive.register_verification', side_effect=[{'id': 'one'}, {'id': 'two'}]) as register, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(proof)), \
             patch('bessel_agent.generate.verify', side_effect=[{'status': 'unresolved'}, {'status': 'proved'}]):
            result = generate(self.target, 'direct', Path(temp) / 'result', attempts=2,
                              archive=True, archive_dir=Path(temp) / 'archive')
            self.assertEqual(register.call_count, 2)
            self.assertNotEqual(register.call_args_list[0].args[0], register.call_args_list[1].args[0])
            self.assertEqual(result['archive_record_id'], 'two')

    def test_rejected_new_candidate_from_saved_request_is_still_archived(self):
        from bessel_agent.archive import list_records
        old_request = {**self.target, 'proof': {'mode': 'direct', 'recipe': 'bessel'}}
        candidate = {'mode': 'direct', 'recipe': 'ring', 'assumptions': ['False']}
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('bessel_agent.generate.subprocess.Popen', side_effect=self.candidate_process(candidate)):
            archive = Path(temp) / 'archive'
            with self.assertRaisesRegex(InputError, 'Expected keys'):
                generate(old_request, 'direct', Path(temp) / 'result', archive=True, archive_dir=archive)
            records = list_records(archive)
            self.assertEqual(len(records), 1)
            self.assertEqual(records[0]['status'], 'unresolved')
            self.assertEqual(records[0]['request'], self.target)
            self.assertEqual(records[0]['candidate'], candidate)

    def test_invalid_json_cli_input_is_archived_before_generation(self):
        from bessel_agent.archive import list_records
        from bessel_agent.generate import main
        with tempfile.TemporaryDirectory() as temp, \
             patch('bessel_agent.generate.subprocess.Popen') as run:
            root = Path(temp)
            source = root / 'invalid.json'
            source.write_text('{invalid input')
            argv = ['generate', str(source), '--route', 'direct', '--output', str(root / 'result'),
                    '--archive', '--archive-dir', str(root / 'archive')]
            with patch('sys.argv', argv), redirect_stderr(io.StringIO()):
                self.assertEqual(main(), 2)
            run.assert_not_called()
            record = list_records(root / 'archive')[0]
            self.assertEqual(record['status'], 'unresolved')
            self.assertEqual((Path(record['record_dir']) / 'original_input.txt').read_text(), '{invalid input')
