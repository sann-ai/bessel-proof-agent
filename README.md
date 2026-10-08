# Bessel Proof Agent

整数次数の第1種ベッセル関数について、構造化した恒等式の証明候補をAIが作り、Leanで検証する小さな初版です。式全体を扱う直接経路と、一つずつ等式変形を検査して連結する段階経路を備えます。

初期対象は、すべての整数 `n` と正の実数 `x` に対する等式です。`J n x` は mathlib の `Complex.besselJ (n : ℂ) (x : ℂ)` と定義し、等式を複素数上で検査します。既存の整数次数の符号関係と多項式の整理に対応します。

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

## 入力と範囲

入力は `schema_version`、`assumptions`、`lhs`、`rhs` を持つJSONです。保存候補の検査時は `proof` を加えます。具体的な構造は [demo/target.json](demo/target.json) と [examples](examples) にあります。

- 次数・整数冪指数: 整数定数、`n`、符号反転、加減乗算。
- 実引数: 整数定数、`x`、符号反転、加減乗算。
- 等式の式: 上記Bessel関数、複素数に埋め込んだ実式、整数定数、加減乗算、符号因子 `(-1)^整数`。
- 前提: `x > 0`。前提の欠落は条件確認待ちになります。
- 証明操作: `bessel`（検証済み符号関係と環の整理）、`ring`（環の整理）。

自由なLaTeXの解釈、微分・積分、非整数次数、一般の除算・冪、数値による反例探索は今後の範囲です。三項漸化式の調査・試作と採用mathlibの詳細は [数学ノート](docs/mathematics.md) を参照してください。

## 結果の意味

- **proved / 証明済み**: 固定した全称命題をLeanが検査し、依存公理監査を通過。
- **refuted / 反証済み**: 固定した全称命題の否定をLeanが検査し、依存公理監査を通過。
- **unresolved / 未解決**: 許可した証明操作で完了しない、入力が不正、または実行制限に到達。
- **needs_conditions / 条件確認待ち**: 対応する定義域条件の確認が必要。

## 検証の境界

任意のLean文字列を候補として受け付けず、許可されたJSON操作から検証器が証明を生成します。型付きの式変換と固定したtheoremの外枠により、候補からの前提追加、目標差し替え、任意コマンド挿入を防ぎます。段階経路は、開始式・隣接する式・終了式の一致も検査します。

Leanの依存公理は `propext`、`Classical.choice`、`Quot.sound` のみを許可します。`sorryAx` を含む証明穴や独自公理は受理されません。信頼する構成要素は、固定したLean/mathlib、リポジトリの検証器、実行環境です。保存された生成物は再検査時に元入力から再生成されます。

GitHub Actionsでは、固定した環境を準備し、入力境界・誤式・段階変形の試験と、両経路の保存済みAI候補の検証を行います。CIの再検証にAI認証情報は渡しません。
