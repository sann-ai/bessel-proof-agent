# Bessel Proof Agent

整数次数・固定有理数次数の第1種ベッセル関数について、構造化した恒等式の証明候補をAIが作り、Leanで検証する実装です。式全体を扱う直接経路と、一つずつ等式変形を検査して連結する段階経路を備えます。

第2種の `Y`、交差積 `X`、複数の実変数、関数値を含む根の条件は、追加の診断経路で受け付けます。元の式と条件を保持して、自然言語の解析、条件付きLean証明、有限個の点での数値診断を保存します。[Y・交差積・根の条件](#第2種y交差積x根の条件を含む式)を参照してください。

既存の証明経路（schema version 1）の対象は、すべての整数 `n` と正の実数 `x` に対する等式です。`J n x` は mathlib の `Complex.besselJ (n : ℂ) (x : ℂ)` と定義し、等式を複素数上で検査します。整数次数の符号関係、一般三項漸化式、微分公式、定積分を扱います。固定した有理数次数も入力できます。

利用者の検証履歴は、`--archive` を指定すると本体外の `~/BesselProofAgentData/archive` に保存します。
4状態の結果・元入力・条件・証拠を追記し、Markdown目録とJSON索引から検索できます。
AI生成も同じ命題の保存証拠を再検査して再利用します。
[蓄積・検索の使い方](docs/archive.md)と[Codex用の実行手順](docs/codex-workflow.md)を参照してください。

## 準備

必要なものは Python 3.12以上、Git、[elan / Lean](https://lean-lang.org/install/) です。Python追加パッケージは使いません。Git cloneとZIPの取得手順、初回診断、問題の切り分けは [セットアップガイド](docs/setup.md) を参照してください。ZIPからの利用でも、依存取得のためにGitが必要です。

取得したプロジェクトのディレクトリで実行します。

```sh
elan toolchain install leanprover/lean4:v4.34.0
lake exe cache get
lake build
python3 scripts/doctor.py
python3 -m bessel_agent verify demo/direct/request.json --output runs/first-check
python3 -m bessel_agent replay runs/first-check
```

Lean版・mathlib・間接依存のコミットは `lean-toolchain`、`lakefile.toml`、`lake-manifest.json` に固定しています。初回取得にはネット接続と数GB規模の空き容量が必要です。準備後の保存証明の検査・再検査は、Codex CLIやAPIキーを使わずに実行できます。新しいAI候補の生成には本人のCodex認証を用意します。

個人の蓄積記録の既定保存先はリポジトリ外の `~/BesselProofAgentData/archive` です。共有・公開する記録は利用者本人が選びます。

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

`parse` は解釈した式をJSONで保存し、正規化した式と全条件を標準エラー出力にも表示します。条件は末尾のセミコロン、末尾の `\text{for }`、または `--conditions 'n integer, x > 0'` で指定します。以下のschema version 1の証明経路では、変数 `n` が現れる式・条件に整数条件を明示し、正の実数 `x` を扱う条件を指定します。対応する条件が欠ける場合、積分変数の束縛が曖昧な場合、分母の非零条件が不足する場合は、条件確認待ちになります。

対応する表記は `J_n(x)`、`J_{n+1}(x)`、`J(n,x)`、括弧、加減乗除、隣接する因子の積、`\frac`、整数冪、`D(J_n(x))`、`\frac{d}{dx} J_n(x)`、`int(0,x,t*J_0(t),t)`、`\int_0^x t J_0(t) dt` です。次数の `1/2` などの固定有理数は既約分数へ正規化します。無指定の変数・分岐条件は入力時に確認します。

追加条件は `x` または整数 `n` と固定有理数との比較 `>`, `>=`, `<`, `<=`, `=`, `!=` を最大8件組み合わせます。例えば `0 < x < 1`、`n >= 2, n != 3`、`x != 1/2` に対応します。有理数は既約の分子・分母で保存し、分子の絶対値と正の分母を1000以下に制限します。日本語の `nは整数、xは正の実数` も入力できます。`x > 1` などから導かれる基底条件 `x > 0` は、正規化したJSONに併記します。

各条件は元のLean命題に明示的な前提として含めます。区間の矛盾、整数条件と両立しない等値、有限区間の全整数の除外を入力時に検査します。条件と同じ一次等式を結論に置く入力も条件確認待ちにします。`x != 1` は `(x-1)` による除算、`0 < x < 1` は `sqrt(1-x)` の定義域確認に利用できます。`n = 0` のもとで `J_n(x)=J_0(x)` を検査するには `conditions` 操作を使います。Bessel値の根・非零条件を含む入力は、次節の診断経路で扱います。

```sh
python3 -m bessel_agent verify examples/conditions-specialization.txt --recipe conditions --output runs/specialization
python3 -m bessel_agent verify examples/conditions-division.txt --recipe field --output runs/division
```

JSONでは `extra_conditions` の要素を次の形で記録します。

```json
{"op":"compare","variable":"x","relation":"ne","value":{"numerator":1,"denominator":2}}
```

旧形式の `{"op":"x_gt","value":1}` も引き続き受理します。

冪の底と平方根の引数は実数式に限定します。`x^(1/2)` は `Real.rpow x (1/2)`、`sqrt(x)` と `\sqrt{x}` は `Real.sqrt x` を複素数へ埋め込んだ値です。複素冪の枝を選ぶ入力は対象外です。

式の先頭では、次のマクロ宣言を使用できます。

```text
\newcommand{\B}[2]{J_{#1}(#2)}
D(\B{1/2}{x})=1/(2*x)*\B{1/2}{x}-\B{3/2}{x}; x > 0
```

マクロは最大4個、引数個数を `[0]`〜`[3]` で明示し、呼び出しの各引数を `{...}` で囲みます。名前は英字1〜16文字、本体は512文字以内です。`\def\B#1#2{J_{#1}(#2)}` と `\DeclareMathOperator{\B}{J}` も使用できます。宣言した引数はすべて本体中で使い、式や条件の行を引数へ埋め込む入力は拒否します。組込み名の上書き、未定義参照、直接・相互再帰を拒否します。グループの深さ16、展開の深さ8、呼び出し128回、展開後32768文字を上限とし、展開後の式を同じ数式parserで検査します。

論文表記では `equation`、`equation*`、`align`、`align*`、`aligned`、`\left` / `\right`、`\dfrac` / `\tfrac`、`\operatorname{J}`、`J'_n(x)` / `J_n'(x)` に対応します。primeは引数が現在の微分変数そのものの場合に受理し、合成関数には `D(...)` を使います。複数行は、2行目以降が明示的な `+`、`-`、`=` で続く単一等式に限ります。独立した複数式、複数環境、未知の命令、不一致の数式区切りは確認待ちまたは入力エラーとなり、行を削除せずに停止します。

## 第2種Y・交差積X・根の条件を含む式

診断経路（schema version 2）は、正の実引数での `J` と `Y`、および

\[
X_{nm}(s,t)=J_n(s)Y_m(t)-Y_n(s)J_m(t)
\]

を扱います。`Y_n(x)` / `Y(n,x)`、`X_01(s,t)` / `X_{0,1}(s,t)` / `X(0,1,s,t)` を入力でき、`λ`・`\lambda` は `lambda` に正規化します。実変数は `x, z, lambda, s, w, t`、整数次数の変数は `n`（`n integer` が必要）です。各変数と有理数の比較に加え、`X_01(z,lambda*z)=0` や `Y_0(x)!=0` を条件として保存します。対応する入力から診断経路を自動選択します。

`examples/cross-product-root.txt` は次の式を収録しています。

```text
X_00(z,lambda*z)^2/(X_01(z,z)^2+lambda^2*X_00(z,lambda*z)*X_02(z,lambda*z)) = (1/lambda)*X_00(z,lambda*z)/(X_11(z,lambda*z)-lambda*X_00(z,lambda*z)); 0 < lambda < 1, z > 0, X_01(z,lambda*z)=0
```

```sh
mkdir -p runs
python3 -m bessel_agent parse examples/cross-product-root.txt --output runs/cross-product-target.json
python3 -m bessel_agent verify examples/cross-product-root.txt --output runs/cross-product --archive
```

この式と条件の構造を認識した場合、漸化式、Wronskian、分母の正値性の積分表示に基づく解析を保存し、明示した仮定から分数式を導くLean証明を検査します。出力は `request.json`、`result.json`、`report.md`、`analysis.json`、`numerical.json`、`conditional_certificate.lean` です。Bessel Yの定義・漸化式・Wronskian・積分正値性をLeanへ接続する工程が残るため、元命題の状態は `unresolved`、条件付き代数証明の成否は別項目に記録します。数学的な対応は[数学ノート](docs/mathematics.md#第2種yと交差積の診断経路)を参照してください。

この例の正常な診断結果は `status: unresolved`、`full_bessel_proof: false` で、Leanの代数検査が通ると `conditional_lean.accepted: true` となります。`verify` の終了コードは、元命題の形式証明が残ることを表す `1` です。

数値診断は、利用中のPythonに既に `mpmath` がある場合に実行し、有限個の標本、根の近似、残差、収束状況を記録します。未導入時は `backend_unavailable` を保存し、入力の解析、条件付きLean検査、アーカイブ保存を続けます。一般のY・複数変数の式は対応範囲と残る検査事項を保存します。複数の根条件の探索、微積分、複素枝を含む入力は、診断で扱える範囲を理由とともに報告します。

根の数値探索は、正の有限区間での符号変化から、パラメータ標本ごとに最大3根を精密化します。60桁計算を用い、探索範囲・許容差・時間制限は `numerical.json` に記録します。標本と符号走査による探索範囲を `root_search.exhaustive: false` と明示します。

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

固定有理数次数は漸化式・微分と、正の端点間の積分公式に対応します。
任意の複素次数の微分と正区間の積分公式はLean APIで利用できます。

- 四則演算と整数係数 `n` の埋め込みに対応します。
- 自然数冪は指数 `0..12`、整数冪は前提から底の非零を確認できる式に対応します。
- 分母は `x`、非零定数、その積など、固定条件から非零が分かる形を受理します。`x != 1` のもとでの `x-1`、`n != 0` のもとでの `n` も使用できます。`J_n(x)` を分母とする式は、追加条件の確認待ちになります。
- 非整数次数は固定有理数と正の引数に対応します。実数の有理数冪と平方根は、底が正と確認できる式を受理します。負の底の分数冪や、未対応の特異点を含む式は条件確認待ちになります。
- 証明操作は `bessel`、`ring`、`field`、`recurrence`、`calculus`、`power`、`conditions`。JSONの式構造と条件から、固定した証明命題を生成します。

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

## 非整数次数と端点特異性

固定有理数次数について、正の引数の微分と、正の端点間の積分を扱います。具体例は

\[
J'_{1/2}(x)=\frac{J_{1/2}(x)}{2x}-J_{3/2}(x),\qquad x>0,
\]

\[
\int_1^x\left(\frac{J_{1/2}(t)}{2t}-J_{3/2}(t)\right)dt
=J_{1/2}(x)-J_{1/2}(1),\qquad x>0,
\]

\[
\int_1^x \sqrt t\,J_{-1/2}(t)\,dt
=\sqrt x\,J_{1/2}(x)-J_{1/2}(1),\qquad x>0
\]

です。正の両端点を持つ区間では、区間全体が正となることを使います。

端点0の特異例は、可積分性をLeanで確認した冪関数

\[
\int_0^x t^{-1/2}\,dt=2\sqrt x,\qquad x>0
\]

に対応します。原点を含む `1/t` は非可積分性のLean補題を用意し、`int(0,x,1/t,t)=0` のような入力を条件確認待ちにします。通常の積分恒等式として扱うには可積分性が必要です。外側の条件 `x > 2` は求積変数tの条件へ引き継がず、区間内に特異点を持つ `int(0,x,1/(t-1),t)` も受理しません。

ベッセル関数を含み、原点へ近づくと被積分関数が発散する具体例として、次も検査できます。

\[
\int_0^x t^{1/4}J_{-3/4}(t)\,dt
=x^{1/4}J_{1/4}(x),\qquad x>0.
\]

Leanでは被積分関数の可積分性、原始関数の右極限0、被積分関数のノルムの右極限∞、積分等式をそれぞれ証明しています。被積分関数は `t^{-1/2}` と連続な非零因子に分解されます。入力側はこの具体的な積と端点 `[0,x]` を認識し、可積分性の証明を固定した検査義務に含めます。Lean定義の原点での値0と、正側からの発散を区別しています。

`examples/origin-singular-composed.txt` はこの等式の両辺に同じ項を加え、条件 `x > 0, x <= 2, x != 1/2` と論文形式のTeXを付けた例です。`demo/origin-direct` と `demo/origin-steps` は、同一入力のlive AI生成からLean検証まで通過した候補です。段階経路は積分の評価と同類項の整理を個別に検査します。

一般の次数・重みの原点特異積分、変数間の追加仮定、複素枝、任意TeXプログラムは継続対象です。現在のCLIは、上記の条件言語・TeX文法・可積分性を証明した具体式を扱います。

新しい例の再検査:

```sh
python3 -m bessel_agent verify examples/noninteger-derivative.txt --recipe calculus --output runs/rational-derivative
python3 -m bessel_agent verify examples/noninteger-integral.txt --recipe calculus --output runs/rational-integral
python3 -m bessel_agent verify examples/singular-integral.txt --recipe calculus --output runs/singular
python3 -m bessel_agent verify examples/real-power.txt --recipe power --output runs/real-power
python3 -m bessel_agent verify examples/macro-recurrence.txt --recipe recurrence --output runs/macro
python3 -m bessel_agent verify examples/origin-singular-composed.txt --recipe calculus --output runs/origin
```

有理数次数の微分と可積分特異例を組み合わせ、x>1を付けた命題について、
`demo/calculus-direct` と `demo/calculus-steps` にlive AIの両経路を保存しています。
段階経路は対称微分形と漸化式も使います。初回の未解決候補を、対応する既存補題へ
接続した後に再検査し、同じ候補を回帰例にしています。

## 数値反例候補を探す

```sh
python3 -m bessel_agent.numeric examples/numeric-recurrence-candidate.target.json
python3 -m bessel_agent.numeric examples/numeric-derivative-candidate.target.json
```

次数 `-3..3` と引数 `0.5, 1, 2, 3` の有限個の点を調べ、整数・実数の全追加条件を満たす標本だけ評価します。整数次数・半整数次数のJを60桁の十進演算で級数評価します。その他の固定有理数次数も級数評価し、初項のGammaには標準ライブラリの倍精度近似を使用します。Gammaを使う値には少なくとも相対 `1e-12` の誤差予算を割り当て、微分・積分へ伝播させます。項数は最大500、評価引数は絶対値12以下、次数は絶対値20以下です。

微分は2段階の中心差分とRichardson補外、積分は開区間の中点求積と細分化を使います。原点の分数式には二乗変数変換を適用します。積分は最大512分割、1標本は最大50000回の式評価、微積分の入れ子は2段までです。求積点の値は局所の積分変数で評価し、外側xの追加条件は標本選択にだけ使います。

通常式は相対許容差 `1e-25`、一般有理数次数を含む式は `1e-10`、微積分式は `1e-9` と推定誤差の10倍の大きい方を比較閾値にし、差のある点を最大3件保存します。微積分の誤差推定は細分間の差と評価誤差の伝播に基づく経験的な値です。使用手法、Gamma近似、推定誤差、収束しなかった標本、条件から除外した標本を出力します。条件内の標本が無い場合は `no_eligible_samples` を返します。

半整数Jの微分公式で引く項を足した入力では、例えば `x=2` に約 `0.9826` の数値差が見つかります。係数 `2` を `3` に変えた漸化式では、例えば `n=-3, x=0.5` に差が見つかります。この出力は `unresolved` と反例候補を持つ数値診断で、反証の確定にはLeanで元の全称命題の否定を検査します。

## 結果の意味

- **proved / 証明済み**: 固定した全称命題をLeanが検査し、依存公理監査を通過。
- **refuted / 反証済み**: 固定した全称命題の否定をLeanが検査し、依存公理監査を通過。
- **unresolved / 未解決**: 許可した証明操作で完了しない、入力が不正、または実行制限に到達。Y・交差積の診断では、条件付きLean証明や数値結果を保存していても、元命題の形式証明が残る間はこの状態を使う。
- **needs_conditions / 条件確認待ち**: 対応する定義域条件の確認が必要。

## 検証の境界

任意のLean文字列を候補として受け付けず、許可されたJSON操作から検証器が証明を生成します。型付きの式変換と固定したtheoremの外枠により、候補からの前提追加、目標差し替え、任意コマンド挿入を防ぎます。段階経路は、開始式・隣接する式・終了式の一致も検査します。

Leanの依存公理は `propext`、`Classical.choice`、`Quot.sound` のみを許可します。`sorryAx` を含む証明穴や独自公理は受理されません。信頼する構成要素は、固定したLean/mathlib、リポジトリの検証器、実行環境です。保存された生成物は再検査時に元入力から再生成されます。

GitHub Actionsでは、固定した環境を準備し、入力境界・誤式・段階変形の試験と、両経路の保存済みAI候補の検証を行います。CIの再検証にAI認証情報は渡しません。

## ライセンス

配布本体と同梱サンプルは [MIT License](LICENSE) です。mathlibなどの依存には各配布元のライセンスが適用されます。[依存の出典とライセンス](docs/setup.md#ライセンスと依存の出典)を参照してください。外部保存先に蓄積する利用者の記録は、本人が共有・公開の扱いを選びます。
