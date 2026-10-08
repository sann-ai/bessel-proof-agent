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

## 一般3項漸化式の形式証明

`Recurrence.lean` は、任意の複素次数 `a`、非零複素引数 `z` について

\[
J_{a-1}(z)+J_{a+1}(z)=\frac{2a}{z}J_a(z)
\]

を証明する。整数次数・実引数 `x > 0` 用には `recurrence` を公開している。
固定したmathlibには専用の漸化式補題がないため、正則化超幾何級数から導出した。

1. `gamma_inv_step`: `1/Gamma(a)=a/Gamma(a+1)` を `a=0` も含めて証明。
2. `hg_coeff_zero`、`hg_coeff_succ`: 正則化 `₀F₁` の級数係数の隣接関係を証明。
3. `hg_hasSum`: 上流の全域収束級数を `HasSum` に接続。
4. `hg_contiguous`: 係数関係を級数の和に移し、
   `H(a,z)=a H(a+1,z)+z H(a+2,z)` を証明。
5. `bessel_recurrence`: Bessel定義の複素冪因子を整理。

## 微分と定積分

`Derivative.lean` では `(k+1) C_a(k+1)=C_{a+1}(k)` を証明し、
`FormalMultilinearSeries.derivSeries` に接続して `H'_a=H_{a+1}` を得る。
積と合成の微分から、`z ∈ Complex.slitPlane` を条件として

\[
J'_a(z)=\frac{a}{z}J_a(z)-J_{a+1}(z)
       =\frac{J_{a-1}(z)-J_{a+1}(z)}2
\]

を証明する。`RealCalculus.lean` の `deriv_bessel_real` は任意の複素次数と
正の実引数を扱い、`deriv_J`、`deriv_J_symmetric` は整数次数向けの補題である。

`Calculus.lean` は整数次数の実解析性、微分・積分の次数反転公式、
任意の実数端点についての

\[
\int_a^b J'_n(t)\,dt=J_n(b)-J_n(a)
\]

を証明する。さらに `RealCalculus.lean` では漸化式と微分公式から
`(x J_1(x))'=x J_0(x)` を導き、`x > 0` のもとで

\[
\int_0^x tJ_0(t)\,dt=xJ_1(x)
\]

を証明する。端点0は原始関数の連続性と値を使い、開区間の微分から
積分の基本定理を適用している。

## 数学ライブラリと入力インターフェイスの対応

Leanの漸化式は任意の複素次数を扱う。CLIは整数式と固定有理数次数を入力し、
等式の変数を整数 `n` と正の実数 `x` に固定する。
非整数次数の引数は正と確認できる式に限定する。
微分公式の複素版は分岐領域上で、CLIは正の実引数上で利用する。
積分は、整数次数のJと多項式など、区間内の正則性を入力構造から確認できる式を受理する。

除算・負冪には分母・底の非零確認が必要である。
`x > 0` と非零定数から確認できる式を受理し、追加条件が必要な式は
`needs_conditions` とする。数値診断で見つけた差は `unresolved` の反例候補として保存する。

## 検証方法

- `lake build`: 公開定義と全補題をコンパイルする。
- `lake env lean BesselProofAgent/Examples.lean`: CLI 向けの固定された証明手順で、
  引数反転、次数反転、同時反転、段階的な符号反転の積、および誤った等式の両向きの反証を確認する。
- `#print axioms`: 主要補題の依存公理を確認する。
  出力は Lean/mathlib の標準公理 `propext`、`Classical.choice`、`Quot.sound` のみであった。

全補題は証明項を伴う。判定には未証明の追加公理や数値的な一致を採用しない。
