# 数学的対象と検証範囲

対象は第1種ベッセル関数の整数次数である。Lean の公開定義は
`BesselProofAgent.J (n : ℤ) (x : ℝ) : ℂ` とし、
`Complex.besselJ (n : ℂ) (x : ℂ)` に接続している。
CLI の等式判定は `∀ (n : ℤ) (x : ℝ), 0 < x → lhs = rhs` の形で行い、
関数値の等式は複素数体で検証する。

## 固定したライブラリ

- Lean: `leanprover/lean4:v4.34.0`
- mathlib: `db00fb3901b1bb4954f8a2373285959a5930bbfa`
- 上流モジュール: `Mathlib.Analysis.SpecialFunctions.Bessel`
- プロジェクトの公開 import: `BesselProofAgent`

このコミットは mathlib に Bessel モジュールが追加された版である。
同リポジトリの `lean-toolchain` に合わせて Lean の版を固定した。
mathlib の `v4.34.1` タグでは Bessel モジュールの存在を確認できなかったため、
コミットを直接指定している。依存ライブラリの版は `lake-manifest.json` に記録する。

上流の定義は、正則化超幾何関数を用いた

\[
J_a(z)=(z/2)^a\,{}_0\widetilde F_1(;a+1;-(z/2)^2)
\]

に基づく。`regularizedHGFun` が、ガンマ関数による正則化を含む
超幾何関数を直接定義し、負の整数次数も扱う。

出典:
[mathlib の Bessel モジュール](https://github.com/leanprover-community/mathlib4/blob/db00fb3901b1bb4954f8a2373285959a5930bbfa/Mathlib/Analysis/SpecialFunctions/Bessel.lean)

## コンパイル済みの恒等式

`BesselProofAgent/Basic.lean` には、任意の `n : ℤ`、`x : ℝ` について次を証明した。

- `argument_neg`: `J n (-x) = (-1 : ℂ) ^ n * J n x`
- `order_neg`: `J (-n) x = (-1 : ℂ) ^ n * J n x`
- `order_argument_neg`: `J (-n) x = J n (-x)`
- `double_neg`: `J (-n) (-x) = J n x`
- `recurrence_zero`: `J (-1) x + J 1 x = (2 * (0 : ℂ) / (x : ℂ)) * J 0 x`

最初の2式は、上流の `Complex.besselJ_int_neg` と
`Complex.besselJ_neg_int` から導出する。次数0の漸化式は、次数1の反転公式で証明する。
`sign_cancel` と `sign_mul_self` は整数指数の符号因子を整理する補題である。

反証例 `J n x + 1 = J n x` については、各点での否定 `add_one_ne` と、
`x > 0` 上の全称命題の否定 `not_forall_add_one` を証明した。
全称命題の反証では `n = 0, x = 1` を代入し、加法の消去律で矛盾を導く。
ベッセル関数値の数値近似は用いない。

## 3項漸化式の調査結果

一般の整数次数に対する目標は

\[
J_{n-1}(x)+J_{n+1}(x)=\frac{2n}{x}J_n(x),\qquad x>0
\]

である。固定した Bessel モジュール全体と、その定義元の
`RegularizedHypergeometric.lean` を調べた。この版の Bessel モジュールには、
符号反転、解析性、原点での値が収録されている。
一般の3項漸化式の専用補題は収録されていない。

この目標に、公開した符号反転補題と環の正規化を適用するコンパイルを実行した。
Lean は `J (n - 1) x`、`J (n + 1) x`、`J n x` を含む未解決の等式を返した。
したがって、この実装の一般次数の漸化式判定は `unresolved` とする。
対応を拡張する際は、正則化超幾何級数の係数間関係から漸化式を形式化する作業が必要である。

## 検証方法

- `lake build`: 公開定義と全補題をコンパイルする。
- `lake env lean BesselProofAgent/Examples.lean`: CLI 向けの固定された証明手順で、
  引数反転、次数反転、同時反転、段階的な符号反転の積、および誤った等式の両向きの反証を確認する。
- `#print axioms`: 主要補題の依存公理を確認する。
  出力は Lean/mathlib の標準公理 `propext`、`Classical.choice`、`Quot.sound` のみであった。

全補題は証明項を伴う。判定には未証明の追加公理や数値的な一致を採用しない。
