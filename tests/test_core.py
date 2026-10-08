import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from bessel_agent.core import (
    InputError, NeedsConditions, ROOT, audit_axioms, load_json,
    render_lean, replay, validate_request, verify,
)


def example(name="direct.json"):
    return load_json(ROOT / "examples" / name)


class InputBoundaryTests(unittest.TestCase):
    def test_examples_have_one_fixed_target(self):
        for name in ("direct.json", "steps.json", "refuted.json"):
            data = example(name)
            validate_request(data)
            source = render_lean(data)
            self.assertIn("theorem target : ∀ (n : ℤ) (x : ℝ), 0 < x →", source)
            self.assertNotIn("sorry", source)

    def test_generated_target_can_be_validated_without_a_candidate(self):
        data = example("argument-negation.target.json")
        validate_request(data, require_proof=False)
        with self.assertRaises(InputError):
            validate_request(data)

    def test_missing_domain_is_reported_explicitly(self):
        data = example()
        data["assumptions"] = []
        with self.assertRaises(NeedsConditions):
            validate_request(data)
        with tempfile.TemporaryDirectory() as directory:
            with patch("bessel_agent.core._run_lean") as lean:
                result = verify(data, Path(directory))
            self.assertEqual(result["status"], "needs_conditions")
            lean.assert_not_called()

    def test_tactics_axioms_and_extra_fields_cannot_enter_the_wrapper(self):
        for payload in ("sorry", "admit", "axiom trusted : False", "exact hx", "ring\nend X"):
            data = example()
            data["proof"]["recipe"] = payload
            with self.assertRaises(InputError):
                validate_request(data)
        data = example()
        data["proof"]["lean"] = "by sorry"
        with self.assertRaises(InputError):
            validate_request(data)

    def test_forged_assumptions_and_variable_names_are_rejected(self):
        data = example()
        data["assumptions"].append("lhs = rhs")
        with self.assertRaises(InputError):
            validate_request(data)
        data = example()
        data["lhs"]["order"]["name"] = "n) : False := by sorry --"
        with self.assertRaises(InputError):
            validate_request(data)

    def test_integer_powers_require_the_exact_nonzero_sign_base(self):
        data = example()
        validate_request(data)
        self.assertEqual(data["rhs"]["args"][0]["base"], {"op": "int", "value": -1})
        for base in ({"op": "int", "value": 0},
                     {"op": "bessel_j", "order": {"op": "var", "name": "n"},
                      "arg": {"op": "var", "name": "x"}},
                     {"op": "int", "value": -1.0}):
            candidate = example()
            candidate["lhs"] = {"op": "zpow", "base": base,
                                "exponent": {"op": "int", "value": -1}}
            with self.subTest(base=base), self.assertRaises(InputError):
                validate_request(candidate)

    def test_free_text_cannot_change_lean_or_verified_explanation(self):
        data = example("steps.json")
        original = render_lean(data)
        data["proof"]["steps"][0]["reason"] = "\nend BesselAgentCandidate\naxiom forged : False\n"
        self.assertEqual(render_lean(data), original)

    def test_steps_cannot_change_target_or_smuggle_conditions(self):
        data = example("steps.json")
        data["proof"]["steps"][-1]["after"] = {"op": "int", "value": 7}
        with self.assertRaises(InputError):
            validate_request(data)
        data = example("steps.json")
        data["proof"]["steps"][0]["conditions"] = ["False"]
        with self.assertRaises(InputError):
            validate_request(data)

    def test_duplicate_json_fields_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            path.write_text('{"proof": 1, "proof": 2}')
            with self.assertRaises(InputError):
                load_json(path)

    def test_dependency_audit_rejects_holes_and_new_axioms(self):
        def audit(names):
            return ("BESSEL_AUDIT_BEGIN\n'BesselAgentCandidate.target' depends on axioms: ["
                    + names + "]\nBESSEL_AUDIT_END\n")
        self.assertEqual(audit_axioms(audit("propext, Classical.choice, Quot.sound")),
                         ["Classical.choice", "Quot.sound", "propext"])
        for names in ("sorryAx", "Custom.fact", "Lean.ofReduceBool", "propext, sorryAx"):
            with self.assertRaises(InputError):
                audit_axioms(audit(names))
        with self.assertRaises(InputError):
            audit_axioms("success")

    def test_altered_saved_lean_is_rejected_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            with patch("bessel_agent.core._run_lean", return_value={"accepted": True, "axioms": []}):
                verify(example(), path)
            with (path / "certificate.lean").open("a") as stream:
                stream.write("\naxiom forged : False\n")
            with patch("bessel_agent.core._run_lean") as lean:
                with self.assertRaises(InputError):
                    replay(path)
            lean.assert_not_called()


@unittest.skipUnless(os.environ.get("BESSEL_RUN_LEAN_TESTS") == "1",
                     "Set BESSEL_RUN_LEAN_TESTS=1 after lake build for real Lean checks.")
class LeanIntegrationTests(unittest.TestCase):
    def check(self, data, expected):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = verify(data, path)
            self.assertEqual(result["status"], expected, json.dumps(result, ensure_ascii=False))
            if expected in {"proved", "refuted"}:
                self.assertTrue(replay(path)["replayed"])
            return result

    def test_direct_parity_proof_and_replay(self):
        self.check(example(), "proved")

    def test_bessel_recipe_also_handles_algebra_only_steps(self):
        data = example()
        x = {"op": "var", "name": "x"}
        data["lhs"] = {"op": "add", "args": [x, x]}
        data["rhs"] = {"op": "mul", "args": [{"op": "int", "value": 2}, x]}
        self.check(data, "proved")

    def test_three_step_double_negation_and_replay(self):
        result = self.check(example("steps.json"), "proved")
        self.assertEqual(result["attempts"][0]["kind"], "proof")

    def test_false_statement_has_a_checked_negation(self):
        result = self.check(example("refuted.json"), "refuted")
        self.assertEqual(result["certificate_kind"], "refutation")

    def test_incorrect_intermediate_step_is_unresolved(self):
        data = example("steps.json")
        bad = {"op": "int", "value": 5}
        data["proof"]["steps"][0]["after"] = bad
        data["proof"]["steps"][1]["before"] = copy.deepcopy(bad)
        self.check(data, "unresolved")

    def test_insufficient_recipe_is_unresolved_not_false(self):
        data = example()
        data["proof"]["recipe"] = "ring"
        self.check(data, "unresolved")


if __name__ == "__main__":
    unittest.main()
