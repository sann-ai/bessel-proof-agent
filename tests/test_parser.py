import copy
import os
from pathlib import Path
import tempfile
import unittest

from bessel_agent.core import InputError, NeedsConditions, ROOT, load_json, render_lean, validate_request, verify
from bessel_agent.parser import parse_identity


DOMAIN = "n integer, x > 0"


class ParserTests(unittest.TestCase):
    def test_plain_and_latex_have_the_same_fixed_target(self):
        expected = load_json(ROOT / "examples/argument-negation.target.json")
        plain = parse_identity("J_n(-x) = (-1)^n * J(n, x)", DOMAIN)
        latex = parse_identity(r"J_{n}\left(-x\right)=(-1)^{n}\,J_{n}(x)", r"n \in \mathbb{Z}, x>0")
        self.assertEqual(plain, expected)
        self.assertEqual(latex, expected)

    def test_recurrence_parses_coefficients_and_shifted_orders(self):
        data = parse_identity(r"J_{n-1}(x)+J_{n+1}(x)=\frac{2n}{x}J_n(x)", DOMAIN)
        self.assertEqual(data["rhs"]["args"][0]["op"], "div")
        self.assertEqual(data["rhs"]["args"][0]["args"][0]["args"][1]["op"], "int_cast")
        self.assertEqual(data["lhs"]["args"][0]["order"]["op"], "sub")

    def test_fixed_half_integer_orders_are_exact(self):
        data = parse_identity(r"J_{-1/2}(x)+J_{3/2}(x)=\frac{1}{x}J_{1/2}(x)", "x > 0")
        self.assertEqual(data["lhs"]["args"][0]["order"],
                         {"op": "rational", "numerator": -1, "denominator": 2})

    def test_derivative_and_integral_bindings(self):
        derivative = parse_identity(r"\frac{d}{dx}J_{-n}(x)=(-1)^n D(J_n(x))", DOMAIN)
        self.assertEqual(derivative["lhs"]["op"], "deriv")
        latex = parse_identity(r"\int_0^x J_{-n}(t)\,dt=(-1)^n\int_0^x J_n(t)\,dt", DOMAIN)
        plain = parse_identity("int(0,x,J_-n(t),t)=(-1)^n int(0,x,J_n(t),t)", DOMAIN)
        self.assertEqual(latex, plain)
        self.assertEqual(latex["lhs"]["arg"]["arg"], {"op": "var", "name": "x"})

    def test_conditions_are_explicit_and_not_strengthened_silently(self):
        for text, domain in [("J_n(x)=J_n(x)", None), ("J_n(x)=J_n(x)", "x > 0"),
                             ("J_n(x)=J_n(x)", "n integer, x > 0, n > 0")]:
            with self.subTest(domain=domain), self.assertRaises(NeedsConditions):
                parse_identity(text, domain)
        data = parse_identity("J_n(x)=J_n(x); n integer, x > 0")
        self.assertEqual(data["assumptions"], ["x > 0"])
        with self.assertRaises(NeedsConditions):
            parse_identity("J_n x=J_n(x)", DOMAIN)

    def test_unsupported_tex_and_code_are_never_executed(self):
        for text in [r"\input{secrets}=0", "__import__('os')=0", "J_n(x)=J_n(x); x > 0; axiom bad",
                     "J_n(x)=J_n(x)=0", "J_n x=0", "J_n(x) := by sorry"]:
            with self.subTest(text=text), self.assertRaises(InputError):
                parse_identity(text, DOMAIN)

    def test_unsafe_denominators_and_powers_need_conditions(self):
        for text in ["1/J_n(x)=0", "0^(-1)=0", "1/n=0", "x^(1/2)=0", "J_{1/2}(-x)=0"]:
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text, DOMAIN)
        for text in ["x/x=1", "x^(-1)=1/x", "(2*x)/(2*x)=1", "x^2=x*x"]:
            validate_request(parse_identity(text, DOMAIN), require_proof=False)

    def test_integral_singularities_and_free_parameter_capture_are_rejected(self):
        for text in ["int(0,x,1/t,t)=0", "int(0,x,t^(-1),t)=0",
                     "int(0,x,J_{-1/2}(t),t)=0", "int(0,x,x*J_n(t),t)=0"]:
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text, DOMAIN)
        with self.assertRaises(NeedsConditions):
            parse_identity(r"\int_0^x \frac{d}{dx}J_n(t)dt=0", DOMAIN)
        data = parse_identity(r"\int_0^x \frac{d}{dt}J_n(t)dt=J_n(x)-J_n(0)", DOMAIN)
        self.assertEqual(data["lhs"]["arg"]["op"], "deriv")

    def test_fractional_json_order_requires_exact_integer_fields(self):
        data = parse_identity("J_{1/2}(x)=J_{1/2}(x)", "x > 0")
        for numerator, denominator in [(1.0, 2), (1, 2.0), (2, 4), (1, 0), (True, 2)]:
            candidate = copy.deepcopy(data)
            candidate["lhs"]["order"].update(numerator=numerator, denominator=denominator)
            with self.subTest(values=(numerator, denominator)), self.assertRaises(InputError):
                validate_request(candidate, require_proof=False)

    def test_binders_and_domains_have_fixed_lean_translation(self):
        data = parse_identity("D(J_-n(x))=(-1)^n D(J_n(x))", DOMAIN)
        data["proof"] = {"mode": "direct", "recipe": "calculus"}
        source = render_lean(data)
        self.assertIn("deriv (fun (x : ℝ) =>", source)
        self.assertIn("∀ (n : ℤ) (x : ℝ), 0 < x →", source)


@unittest.skipUnless(os.environ.get("BESSEL_RUN_LEAN_TESTS") == "1", "Enable real Lean integration checks.")
class ParsedLeanTests(unittest.TestCase):
    def check(self, text, recipe, domain=DOMAIN):
        data = parse_identity(text, domain)
        data["proof"] = {"mode": "direct", "recipe": recipe}
        with tempfile.TemporaryDirectory() as directory:
            result = verify(data, Path(directory))
            self.assertEqual(result["status"], "proved", result)

    def test_parity_from_latex(self):
        self.check(r"J_n(-x)=(-1)^n J_n(x)", "bessel")

    def test_general_recurrence_and_algebraic_rearrangement(self):
        self.check(r"J_{n-1}(x)+J_{n+1}(x)=\frac{2n}{x}J_n(x)", "recurrence")
        self.check("J_{n-1}(x)+J_{n+1}(x)+J_n(x)=(2*n/x+1)*J_n(x)", "recurrence")

    def test_half_integer_recurrence(self):
        self.check("J_{-1/2}(x)+J_{3/2}(x)=1/x*J_{1/2}(x)", "recurrence", "x > 0")

    def test_safe_division(self):
        self.check("(2*x)/(2*x)=1", "field")
        self.check("x^(-1)=1/x", "field")

    def test_derivative_identity(self):
        self.check("D(J_-n(x))=(-1)^n*D(J_n(x))", "calculus")
        self.check("D(J_n(x))=(n/x)*J_n(x)-J_{n+1}(x)", "calculus")
        self.check("D(J_n(x))=(J_{n-1}(x)-J_{n+1}(x))/2", "calculus")

    def test_integral_and_fundamental_theorem(self):
        self.check("int(0,x,J_-n(t),t)=(-1)^n*int(0,x,J_n(t),t)", "calculus")
        self.check("int(0,x,D(J_n(t)),t)=J_n(x)-J_n(0)", "calculus")
        self.check("int(0,x,t*J_0(t),t)=x*J_1(x)", "calculus", "x > 0")

    def test_wrong_derivatives_and_integrals_never_receive_proved_status(self):
        for text in ["D(J_n(x))=(n/x)*J_n(x)+J_{n+1}(x)",
                     "D(J_n(x))=2*((n/x)*J_n(x)-J_{n+1}(x))",
                     "int(0,x,D(J_n(t)),t)=J_n(0)-J_n(x)",
                     "int(0,x,t*J_0(t),t)=2*x*J_1(x)"]:
            data = parse_identity(text, DOMAIN)
            data["proof"] = {"mode": "direct", "recipe": "calculus"}
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                result = verify(data, Path(directory))
                self.assertIn(result["status"], {"unresolved", "refuted"}, result)
                if result["status"] == "refuted":
                    self.assertEqual(result["certificate_kind"], "refutation")


if __name__ == "__main__":
    unittest.main()
