# Bessel Proof Agent

整数次数の第1種ベッセル関数について、構造化した恒等式の証明候補をAIが作り、Leanで検証する実装です。式全体を扱う直接経路と、一つずつ等式変形を検査して連結する段階経路を備えます。

初期対象は、すべての整数 `n` と正の実数 `x` に対する等式です。`J n x` は mathlib の `Complex.besselJ (n : ℂ) (x : ℂ)` と定義し、等式を複素数上で検査します。整数次数の符号関係、一般三項漸化式、微分公式、定積分を扱います。固定した有理数次数も入力できます。

## 準備

必要なものは Python 3.12以上、Git、[elan / Lean](https://lean-lang.org/install/) です。Python追加パッケージは使いません。Lean版とmathlibのコミットはリポジトリ内で固定しています。

```sh
lake update
lake exe cache get
lake build
BESSEL_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/replay_examples.py
```

初回のmathlib取得にはネット接続と数GBの空き容量が必要です。環境取得後の保存証明の再検証は、AIやAPIキーを使わずに実行できます。

## 保存された候補を検証する

```sh
python3 -m bessel_agent verify demo/direct/request.json --output runs/direct
python3 -m bessel_agent verify demo/steps/request.json --output runs/steps
python3 -m bessel_agent replay runs/direct
```

同じ対象 `J_{-n}(x) + J_n(-x) = 2 (-1)^n J_n(x)` の保存済みAI出力を、両経路で検査します。レポート、正規化した入力、Lean証明、依存公理の検査結果が出力されます。各段階の説明は、検証した式と許可された証明操作に対応します。

## AIで新しい候補を生成する

[Codex CLI](https://learn.chatgpt.com/docs/non-interactive-mode) が既存の認証で使用可能な環境では、次のコマンドで候補生成からLean検証まで実行できます。

```sh
codex login status
python3 -m bessel_agent.generate demo/target.json --route direct --output runs/live-direct
python3 -m bessel_agent.generate demo/target.json --route steps --output runs/live-steps
```

既定では、インストール済みCLIのモデル設定と保存された認証を利用し、推論量に `ultra` を指定します。対応モデルを `--model MODEL` で明示できます。`--attempts 2` または `3` を指定すると、同じ命題について検証エラーを使った再生成を行います。既定は1回です。

生成は読み取り専用の一時ディレクトリで行い、JSONの証明計画だけを受け取ります。生成モデルが命題・前提を出力する欄はありません。検証側は元入力に候補を付加し、改めて構造を検査します。生成処理のタイムアウトは既定240秒です。出力先には新しいディレクトリを指定してください。

## LaTeX・通常表記から入力する

等式の末尾に条件を付けたテキストを読み込めます。

```text
J_{n-1}(x) + J_{n+1}(x) = \frac{2 n}{x} J_n(x); n integer, x > 0
```

```sh
mkdir -p runs
python3 -m bessel_agent parse examples/recurrence.txt --output runs/target.json
python3 -m bessel_agent verify examples/recurrence.txt --recipe recurrence --output runs/recurrence
```

`parse` は解釈した式をJSONで保存します。条件は末尾のセミコロンに続けて、または `--conditions 'n integer, x > 0'` で指定します。変数 `n` が現れる式では整数条件を明示し、`x > 0` は全入力で明示します。対応する条件が欠ける場合、積分変数の束縛が曖昧な場合、分母の非零条件が不足する場合は、条件確認待ちになります。

対応する表記は `J_n(x)`、`J_{n+1}(x)`、`J(n,x)`、括弧、加減乗除、隣接する因子の積、`\frac`、整数冪、`D(J_n(x))`、`\frac{d}{dx} J_n(x)`、`int(0,x,t*J_0(t),t)`、`\int_0^x t J_0(t) dt` です。次数の `1/2` などの固定有理数は既約分数へ正規化します。マクロ定義、任意のTeXプログラム、無指定の変数・分岐条件は対応文法の外に置き、入力時に確認します。

## 今回追加した数学

Leanの基礎補題は、任意の複素次数 `a`・非零複素引数 `z` の三項漸化式を証明しています。

\[
J_{a-1}(z)+J_{a+1}(z)=\frac{2a}{z}J_a(z).
\]

微分公式は複素冪の分岐領域 `Complex.slitPlane` 上で証明し、CLIは正の実数引数へ適用します。

\[
J'_n(x)=\frac{n}{x}J_n(x)-J_{n+1}(x)
       =\frac{J_{n-1}(x)-J_{n+1}(x)}{2},\qquad x>0.
\]

CLIでは整数変数 `n` または固定した有理数次数を入力し、複素数次数の自由変数はLean APIから扱います。次の積分も検査できます。

\[
\int_0^x tJ_0(t)\,dt=xJ_1(x),\qquad x>0,
\]

\[
\int_a^b J'_n(t)\,dt=J_n(b)-J_n(a).
\]

後者のLean補題は任意の実数端点を扱います。CLIの端点は定数または `x` からなる対応文法の実式で指定します。積分の初期対応は、整数次数のJ、多項式、これらの微分、非零定数による除算からなる、実軸全体で正則な被積分関数です。

非整数次数についてCLIで検証済みの機能は固定有理数の漸化式です。
微分・積分のCLI証明手順は整数次数を対象とし、任意の複素次数の微分公式はLean APIで利用できます。

- 四則演算と整数係数 `n` の埋め込みに対応します。
- 自然数冪は指数 `0..12`、整数冪は前提から底の非零を確認できる式に対応します。
- 分母は `x`、非零定数、その積など、`x > 0` から非零が分かる形を受理します。`J_n(x)` を分母とする式は、追加条件の確認待ちになります。
- 非整数次数は固定有理数と正の引数に対応します。非整数次数の負引数、分数冪の分岐、積分区間内に特異点を含む表現は、必要条件の指定を求めます。
- 証明操作は `bessel`、`ring`、`field`、`recurrence`、`calculus`。JSONの式構造と条件から、固定した証明命題を生成します。

証明の構成と数学的範囲は [数学ノート](docs/mathematics.md) に記載しています。

追加した例の再検査:

```sh
python3 -m bessel_agent verify examples/half-integer.txt --recipe recurrence --output runs/half-integer
python3 -m bessel_agent verify examples/derivative.txt --recipe calculus --output runs/derivative
python3 -m bessel_agent verify examples/integral.txt --recipe calculus --output runs/integral
```

これらはそれぞれ半整数次数の漸化式、整数次数の微分公式、重み付き定積分について
Leanの証明と依存公理監査を通過した例です。漸化式を含む合成式は
`demo/recurrence-direct` と `demo/recurrence-steps` に保存し、live AI生成から
直接経路・段階経路の両方を検査しています。

## 数値反例候補を探す

```sh
python3 -m bessel_agent.numeric examples/numeric-recurrence-candidate.target.json
```

次数 `-3..3` と引数 `0.5, 1, 2, 3` の有限個の点を調べます。整数次数・半整数次数のJを60桁の十進演算で級数評価し、相対許容差 `1e-25` を超える差を最大3件保存します。項数は最大500、評価引数は絶対値12以下、次数は絶対値20以下に制限します。微分・積分式の数値評価は今後の範囲です。

係数 `2` を `3` に変えた漸化式では、例えば `n=-3, x=0.5` に差が見つかります。この出力は `unresolved` と反例候補を持つ数値診断で、反証の確定にはLeanで元の全称命題の否定を検査します。

## 結果の意味

- **proved / 証明済み**: 固定した全称命題をLeanが検査し、依存公理監査を通過。
- **refuted / 反証済み**: 固定した全称命題の否定をLeanが検査し、依存公理監査を通過。
- **unresolved / 未解決**: 許可した証明操作で完了しない、入力が不正、または実行制限に到達。
- **needs_conditions / 条件確認待ち**: 対応する定義域条件の確認が必要。

## 検証の境界

任意のLean文字列を候補として受け付けず、許可されたJSON操作から検証器が証明を生成します。型付きの式変換と固定したtheoremの外枠により、候補からの前提追加、目標差し替え、任意コマンド挿入を防ぎます。段階経路は、開始式・隣接する式・終了式の一致も検査します。

Leanの依存公理は `propext`、`Classical.choice`、`Quot.sound` のみを許可します。`sorryAx` を含む証明穴や独自公理は受理されません。信頼する構成要素は、固定したLean/mathlib、リポジトリの検証器、実行環境です。保存された生成物は再検査時に元入力から再生成されます。

GitHub Actionsでは、固定した環境を準備し、入力境界・誤式・段階変形の試験と、両経路の保存済みAI候補の検証を行います。CIの再検証にAI認証情報は渡しません。
