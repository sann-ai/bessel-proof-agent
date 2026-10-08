import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from bessel_agent.core import InputError, NeedsConditions, ROOT, load_json, render_lean, replay, validate_request, verify
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
                             ("J_n(x)=J_n(x)", "n integer, x > 0, m > 0")]:
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
        for text in ["1/J_n(x)=0", "0^(-1)=0", "1/n=0", "(-x)^(1/2)=0", "J_{1/2}(-x)=0"]:
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

    def test_japanese_conditions_and_extra_assumptions_are_preserved(self):
        target = parse_identity("(x-1)/(x-1)=1", "nは整数、x > 1")
        self.assertEqual(target["extra_conditions"], [{"op": "x_gt", "value": 1}])
        target["proof"] = {"mode": "direct", "recipe": "field"}
        self.assertIn("0 < x → 1 < x →", render_lean(target))
        self.assertIn("intro n x hx hcondition_1", render_lean(target))
        self.assertEqual(parse_identity("J_n(x)=J_n(x)", "nは整数、xは正の実数")["assumptions"], ["x > 0"])
        with self.assertRaises(NeedsConditions):
            parse_identity("(x-1)/(x-1)=1", "x > 0")

    def test_real_rational_powers_and_sqrt_keep_real_semantics(self):
        target = parse_identity(r"x^{1/2}=\sqrt{x}", "x > 0")
        self.assertEqual(target["lhs"]["op"], "real_rpow")
        self.assertEqual(target["rhs"]["op"], "sqrt")
        target["proof"] = {"mode": "direct", "recipe": "power"}
        source = render_lean(target)
        self.assertIn("Real.rpow", source)
        self.assertIn("Real.sqrt", source)
        self.assertNotIn("Complex.cpow", source)
        with self.assertRaises(NeedsConditions):
            parse_identity("sqrt(x-1)=0", "x > 0")
        validate_request(parse_identity("sqrt(x-1)=sqrt(x-1)", "x > 1"), require_proof=False)

    def test_positive_interval_and_integrable_singularity_have_separate_gates(self):
        validate_request(parse_identity("int(1,x,J_{1/2}(t),t)=0", "x > 0"), require_proof=False)
        validate_request(parse_identity("int(0,x,t^(-1/2),t)=2*sqrt(x)", "x > 0"), require_proof=False)
        for text in ["int(0,x,1/t,t)=0", "int(0,x,1/(t-1),t)=0",
                     "int(1,x,1/(t-1),t)=0", "int(0,x,t^(-3/2),t)=0",
                     "int(0,x,D(1/(t-1)),t)=0"]:
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text, "x > 2")
        with self.assertRaisesRegex(NeedsConditions, "not_intervalIntegrable_inv"):
            parse_identity("int(0,x,1/t,t)=0", "x > 0")

    def test_bounded_macros_expand_to_the_same_ast(self):
        macro = r"\newcommand{\J}[2]{J_{#1}(#2)} \J{n}{-x}=(-1)^n\J{n}{x}"
        self.assertEqual(parse_identity(macro, DOMAIN), parse_identity("J_n(-x)=(-1)^n J_n(x)", DOMAIN))
        nested = r"\newcommand{\J}[2]{J_{#1}(#2)} \newcommand{\Half}[1]{\J{1/2}{#1}} \Half{x}=J_{1/2}(x)"
        validate_request(parse_identity(nested, "x > 0"), require_proof=False)

    def test_macro_redefinition_recursion_malformed_and_scope_are_rejected(self):
        invalid = [r"\newcommand{\frac}[2]{#1} 1=1", r"\newcommand{\J}[1]{\J{#1}} \J{x}=0",
                   r"\newcommand{\A}[1]{\B{#1}} \newcommand{\B}[1]{\A{#1}} \A{x}=0",
                   r"\newcommand{\A}[1]{#2} \A{x}=0", r"\newcommand{\A}[4]{#1} 1=1",
                   r"\newcommand{\A}[0]{1} \newcommand{\A}[0]{2} 1=1",
                   r"\newcommand{\A}[0]{\input{file}} \A=0", r"\newcommand{\A}[1]{#1} \A{x=0"]
        for text in invalid:
            with self.subTest(text=text), self.assertRaises(InputError):
                parse_identity(text, DOMAIN)
        with self.assertRaises(NeedsConditions):
            parse_identity(r"\newcommand{\J}[1]{x*J_n(#1)} int(0,x,\J{t},t)=0", DOMAIN)
        with self.assertRaises(InputError):
            parse_identity(r"\newcommand{\A}[0]{x} " + "+".join([r"\A"] * 129) + "=0", DOMAIN)
        with self.assertRaises(InputError):
            parse_identity(r"\newcommand{\A}[1]{#1} " + r"\A{" * 10 + "x" + "}" * 10 + "=x", DOMAIN)

    def test_forged_extra_conditions_and_rational_float_fields_are_rejected(self):
        target = parse_identity("x=x", "x > 0")
        for condition in [{"op": "axiom", "value": "False"}, {"op": "x_gt", "value": 1.0},
                          {"op": "x_gt", "value": True}, {"op": "x_gt", "value": -1}]:
            target["extra_conditions"] = [condition]
            with self.subTest(condition=condition), self.assertRaises(InputError):
                validate_request(target, require_proof=False)
        target = parse_identity("x^(1/2)=sqrt(x)", "x > 0")
        target["lhs"]["exponent"]["numerator"] = 1.0
        with self.assertRaises(InputError):
            validate_request(target, require_proof=False)

    def test_comparison_conditions_preserve_exact_atoms_and_domains(self):
        from bessel_agent.core import condition_labels, normalized_conditions, condition_holds
        from fractions import Fraction
        target = parse_identity("(x-1)/(x-1)=1", "n integer, 0<x<=3/2, x!=1, -2<=n<3")
        labels = condition_labels(target)
        self.assertEqual(labels, ["x > 0", "x <= 3/2", "x != 1", "n >= -2", "n < 3"])
        atoms = normalized_conditions(target)
        self.assertTrue(all(condition_holds(atom, 0, Fraction(5, 4)) for atom in atoms))
        self.assertFalse(all(condition_holds(atom, 3, Fraction(5, 4)) for atom in atoms))
        self.assertFalse(all(condition_holds(atom, 0, Fraction(1)) for atom in atoms))
        validate_request(parse_identity("n/n=1", "n integer, x>0, n!=0"), require_proof=False)
        validate_request(parse_identity("sqrt(2-x)=sqrt(2-x)", "0<x<2"), require_proof=False)
        validate_request(parse_identity("J_n(x)=J_n(x)", "n integer, x>=0, x!=0"), require_proof=False)
        target["proof"] = {"mode": "direct", "recipe": "field"}
        source = render_lean(target)
        self.assertIn("(x : ℝ) ≤ ((3 : ℝ) / 2)", source)
        self.assertIn("n ≥ -2", source)
        self.assertIn("n < 3", source)

    def test_inconsistent_real_and_integer_conditions_are_rejected(self):
        for conditions in ["x>0, x<=0", "x=1,x!=1", "x>=2,x<2", "x>0,x<0",
                           "n integer,x>0,0<n<1", "n integer,x>0,n=1/2",
                           "n integer,x>0,0<=n<=1,n!=0,n!=1", "n integer,x>0,n>=2,n<2"]:
            with self.subTest(conditions=conditions), self.assertRaises(NeedsConditions):
                parse_identity("J_0(x)=J_0(x)", conditions)
        for conditions in ["x<1", "x>=0", "x>0,n>0", "x>0, J_0(x)=0", "x>0,n>x", "x>0)", "(x>0"]:
            with self.subTest(conditions=conditions), self.assertRaises(NeedsConditions):
                parse_identity("J_0(x)=J_0(x)", conditions)

    def test_conclusion_cannot_be_inserted_as_an_equality_condition(self):
        for text, conditions in [("x=1", "x=1"), ("1=x", "x=1"), ("2*x=2", "x=1"),
                                 ("x^1=1", "x=1"), ("n^1=0", "n integer,x>0,n=0"),
                                 ("n=0", "n integer,x>0,n=0"), ("x=1", "x>=1,x<=1")]:
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text, conditions)
        validate_request(parse_identity("J_n(x)=J_0(x)", "n integer,x>0,n=0"), require_proof=False)
        target = parse_identity("x=x", "x>0")
        invalid = [dict(op="compare", variable="x", relation="eq", value={"numerator": 1.0, "denominator": 1}),
                   dict(op="compare", variable="x", relation="eq", value={"numerator": 1, "denominator": 0}),
                   dict(op="compare", variable="x", relation="eq", value={"numerator": 2, "denominator": 2}),
                   dict(op="compare", variable={"op": "bessel_j"}, relation="eq", value={"numerator": 1, "denominator": 1})]
        for condition in invalid:
            target["extra_conditions"] = [condition]
            with self.subTest(condition=condition), self.assertRaises(InputError):
                validate_request(target, require_proof=False)

    def test_outer_conditions_never_protect_an_integral_pole(self):
        for conditions in ["x>0,x!=1", "x=2", "1<x<=2"]:
            with self.subTest(conditions=conditions), self.assertRaises(NeedsConditions):
                parse_identity("int(0,x,1/(t-1),t)=0", conditions)
        with self.assertRaises(NeedsConditions):
            parse_identity("int(0,x,D(1/(t-1)),t)=0", "x>0,x!=1")

    def test_paper_environments_prime_and_operator_notation(self):
        expected = parse_identity("D(J_n(x))=n/x*J_n(x)-J_{n+1}(x)", DOMAIN)
        examples = [r"\begin{equation}J_n'(x)=\tfrac{n}{x}\operatorname{J}_n(x)-J_{n+1}(x)\end{equation}",
                    r"\begin{align}J'_n(x)&=\frac{n}{x}J_n(x)\\&-J_{n+1}(x)\end{align}",
                    r"\begin{equation*}\begin{aligned}J_n^{\prime}(x)&=n/x*J_n(x)-J_{n+1}(x)\end{aligned}\end{equation*}"]
        for text in examples:
            with self.subTest(text=text):
                self.assertEqual(parse_identity(text, DOMAIN), expected)
        with self.assertRaises(NeedsConditions):
            parse_identity("J_n'(2*x)=D(J_n(2*x))", DOMAIN)

    def test_paper_macro_subset_and_text_conditions(self):
        expected = parse_identity("J_n(-x)=(-1)^n J_n(x)", DOMAIN)
        for declaration, body in [(r"\def\B#1#2{J_{#1}(#2)}", r"\B{n}{-x}=(-1)^n\B{n}{x}"),
                                  (r"\DeclareMathOperator{\B}{J}", r"\B_n(-x)=(-1)^n\B_n(x)")]:
            text = declaration + r"\begin{equation}" + body + r"\quad\text{for }n\in\mathbb{Z},x>0\end{equation}"
            self.assertEqual(parse_identity(text), expected)
        target = parse_identity((ROOT / "examples/origin-singular-composed.txt").read_text())
        self.assertEqual(target["extra_conditions"][1]["value"], {"numerator": 1, "denominator": 2})

    def test_paper_rows_and_macro_arguments_cannot_disappear(self):
        invalid = [r"\begin{align}J_n(x)&=J_n(x)\\J_n(x)&=0\end{align}",
                   r"\begin{aligned}J_0(x)&=J_0(x)\\J_1(x)\end{aligned}",
                   r"\begin{equation}x=x\end{equation}\begin{equation}1\end{equation}",
                   r"1\begin{equation}x=x\end{equation}", "$x=x$$", "$$x=x$",
                   r"\[$x=x$$\]",
                   r"\begin{equation}J_n(x)=J_n(x)\end{align}",
                   r"\begin{equation}J_n(x)=J_n(x)",
                   r"\begin{cases}J_n(x)=J_n(x)\end{cases}",
                   r"\def\B#1#2{#1}\B{x}{x=0}=x",
                   r"\def\B#1{#1}\B{x=0}=0",
                   r"\def\B#1{\B{#1}}\B{x}=x",
                   r"\DeclareMathOperator{\B}{sin}\B(x)=0",
                   r"\def\text#1{#1}x=x",
                   r"\def\B#2{#2}x=x",
                   r"\def\B#1{#1}\B{x; x>0}=x",
                   r"\def\B#1{#1}\B{x\\x}=x",
                   r"J_n(x)=J_n(x)\quad\text{n integer,x>0}\\\text{x<0}",
                   r"\operatorname{sin}(x)=0"]
        for text in invalid:
            with self.subTest(text=text), self.assertRaises(InputError):
                parse_identity(text, DOMAIN)
        with self.assertRaises(NeedsConditions):
            parse_identity(r"J_n(x)=J_n(x)\quad\text{n integer,x>0,x<0}")

    def test_origin_singular_integrand_requires_the_exact_supported_shape(self):
        validate_request(parse_identity("int(0,x,t^(1/4)*J_{-3/4}(t),t)=0", "x>0"), require_proof=False)
        for text in ["int(0,x,t^(-1/4)*J_{-3/4}(t),t)=0",
                     "int(0,x,t^(1/4)*J_{-7/4}(t),t)=0", "int(0,x,J_{-3/4}(t),t)=0"]:
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text, "x>0")

    def test_parse_cli_displays_conditions_without_changing_target_json(self):
        path = ROOT / "examples/origin-singular-composed.txt"
        result = subprocess.run([sys.executable, "-m", "bessel_agent", "parse", str(path)],
                                cwd=ROOT, capture_output=True, text=True, check=True)
        self.assertEqual(json.loads(result.stdout), parse_identity(path.read_text()))
        self.assertIn("正規化した式：", result.stderr)
        self.assertIn("x <= 2", result.stderr)
        self.assertIn("x != 1/2", result.stderr)


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


@unittest.skipUnless(os.environ.get("BESSEL_RUN_LEAN_TESTS") == "1", "Enable real Lean integration checks.")
class ExtendedCalculusLeanTests(unittest.TestCase):
    check = ParsedLeanTests.check
    def test_rational_derivative_and_positive_interval_integral(self):
        self.check("D(J_{1/2}(x))=1/(2*x)*J_{1/2}(x)-J_{3/2}(x)", "calculus", "x > 0")
        self.check("D(J_{1/3}(x))=1/(3*x)*J_{1/3}(x)-J_{4/3}(x)", "calculus", "x > 0")
        self.check("D(J_{1/2}(x))=(J_{-1/2}(x)-J_{3/2}(x))/2", "calculus", "x > 0")
        self.check("int(1,x,(1/(2*t))*J_{1/2}(t)-J_{3/2}(t),t)=J_{1/2}(x)-J_{1/2}(1)", "calculus", "x > 0")

    def test_weighted_half_order_and_singular_integrals(self):
        self.check("int(1,x,sqrt(t)*J_{-1/2}(t),t)=sqrt(x)*J_{1/2}(x)-J_{1/2}(1)", "calculus", "x > 0")
        self.check("int(0,x,t^(-1/2),t)=2*sqrt(x)", "calculus", "x > 0")

    def test_real_powers_and_added_domain(self):
        self.check("x^(1/2)*x^(1/2)=x", "power", "x > 0")
        self.check("sqrt(x)^2=x", "power", "x > 0")
        self.check("(x-1)/(x-1)=1", "field", "x > 1")
        self.check("sqrt(x-1)^2=x-1", "power", "x > 1")

    def test_composed_new_calculus_under_extra_condition(self):
        self.check("D(J_{1/2}(x))+int(0,x,t^(-1/2),t)=1/(2*x)*J_{1/2}(x)-J_{3/2}(x)+2*sqrt(x)", "calculus", "x > 1")

    def test_original_ai_symmetric_derivation_and_replay(self):
        data = load_json(ROOT / "examples/rational-symmetric-steps.json")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = verify(data, path)
            self.assertEqual(result["status"], "proved", result)
            self.assertTrue(replay(path)["replayed"])

    def test_macro_expansion_and_extra_condition_certificate_replay(self):
        self.check(r"\newcommand{\J}[2]{J_{#1}(#2)} \J{n}{-x}=(-1)^n\J{n}{x}", "bessel")
        data = parse_identity("(x-1)/(x-1)=1", "x > 1")
        data["proof"] = {"mode": "direct", "recipe": "field"}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            self.assertEqual(verify(data, path)["status"], "proved")
            self.assertTrue(replay(path)["replayed"])
            changed = copy.deepcopy(data)
            changed["extra_conditions"][0]["value"] = 2
            (path / "request.json").write_text(json.dumps(changed))
            with self.assertRaises(InputError):
                replay(path)

    def test_wrong_new_calculus_coefficients_stay_unresolved_or_refuted(self):
        for text in ["D(J_{1/2}(x))=1/(2*x)*J_{1/2}(x)+J_{3/2}(x)",
                     "int(0,x,t^(-1/2),t)=sqrt(x)",
                     "int(1,x,sqrt(t)*J_{-1/2}(t),t)=sqrt(x)*J_{1/2}(x)+J_{1/2}(1)",
                     "sqrt(x-1)^2=x"]:
            data = parse_identity(text, "x > 1")
            data["proof"] = {"mode": "direct", "recipe": "power" if text.startswith("sqrt") else "calculus"}
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                result = verify(data, Path(directory))
                self.assertIn(result["status"], {"unresolved", "refuted"}, result)
                if result["status"] == "refuted":
                    self.assertEqual(result["certificate_kind"], "refutation")

    def test_refutation_witness_satisfies_extra_conditions(self):
        data = parse_identity("J_n(x)+1=J_n(x)", "nは整数、x > 2")
        data["proof"] = {"mode": "direct", "recipe": "ring"}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = verify(data, path)
            self.assertEqual(result["status"], "refuted", result)
            self.assertIn("h 0 3 (by norm_num) (by norm_num)", (path / "certificate.lean").read_text())
            self.assertTrue(replay(path)["replayed"])


if __name__ == "__main__":
    unittest.main()


@unittest.skipUnless(os.environ.get("BESSEL_RUN_LEAN_TESTS") == "1", "Enable real Lean integration checks.")
class PaperConditionsLeanTests(unittest.TestCase):
    check = ParsedLeanTests.check

    def test_new_comparison_conditions_are_used_by_the_proofs(self):
        self.check("sqrt(1-x)^2=1-x", "power", "0<x<1")
        self.check("(x-1)/(x-1)=1", "field", "x>0,x!=1")
        self.check("n/n=1", "field", "n integer,x>0,n!=0")
        self.check("J_n(x)=J_0(x)", "conditions", "n integer,x>0,n=0")
        self.check("J_0(x)=J_0(1/2)", "conditions", "x=1/2")
        self.check("sqrt(n-1)^2=n-1", "power", "n integer,x>0,n>=2")

    def test_refutation_witness_obeys_integer_and_rational_bounds(self):
        data = parse_identity("J_n(x)+1=J_n(x)", "n integer,0<x<1,n>=2")
        data["proof"] = {"mode": "direct", "recipe": "ring"}
        with tempfile.TemporaryDirectory() as folder:
            result = verify(data, Path(folder))
            self.assertEqual(result["status"], "refuted", result)
            self.assertIn("h 2 (1 / 2 : ℝ)", (Path(folder) / "certificate.lean").read_text())
            self.assertTrue(replay(Path(folder))["replayed"])

    def test_paper_derivative_and_condition_certificate_replay(self):
        self.check(r"\begin{aligned}J_n'(x)&=\tfrac{n}{x}\operatorname{J}_n(x)-J_{n+1}(x)\end{aligned}", "calculus")
        data = parse_identity("(x-1)/(x-1)=1", "0<x<=3/2,x!=1")
        data["proof"] = {"mode": "direct", "recipe": "field"}
        with tempfile.TemporaryDirectory() as folder:
            result = verify(data, Path(folder))
            self.assertEqual(result["status"], "proved", result)
            self.assertTrue(replay(Path(folder))["replayed"])
            report = (Path(folder) / "report.md").read_text()
            self.assertIn("x <= 3/2", report)
            self.assertIn("x != 1", report)

    def test_origin_singular_bessel_and_composed_identity(self):
        self.check("int(0,x,t^(1/4)*J_{-3/4}(t),t)=x^(1/4)*J_{1/4}(x)", "calculus", "x>0")
        target = parse_identity((ROOT / "examples/origin-singular-composed.txt").read_text())
        target["proof"] = {"mode": "direct", "recipe": "calculus"}
        source = render_lean(target)
        self.assertIn("intervalIntegrable_origin_weighted_bessel x hx", source)
        with tempfile.TemporaryDirectory() as folder:
            result = verify(target, Path(folder))
            self.assertEqual(result["status"], "proved", result)
            self.assertTrue(replay(Path(folder))["replayed"])

    def test_origin_singular_wrong_coefficients_never_receive_proved(self):
        for right in ["2*x^(1/4)*J_{1/4}(x)", "-x^(1/4)*J_{1/4}(x)"]:
            target = parse_identity("int(0,x,t^(1/4)*J_{-3/4}(t),t)=" + right, "x>0")
            target["proof"] = {"mode": "direct", "recipe": "calculus"}
            with self.subTest(right=right), tempfile.TemporaryDirectory() as folder:
                result = verify(target, Path(folder))
                self.assertIn(result["status"], {"unresolved", "refuted"}, result)
