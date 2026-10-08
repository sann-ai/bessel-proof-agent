# 保存したAI生成例

両例は、`target.json` の同じ入力から実際にCodex CLIを呼び出して生成した。
CLIは既存のChatGPTログインを利用した。実行時の設定は
`codex-cli 0.159.2`、モデル `gpt-6.1-sol`、推論量 `ultra` である。
`--model` は省略し、その時点のCLI設定を利用したため、
`generation.json` の `model_override` は `null` となっている。

- `direct`: 符号関係の適用と代数式の整理を1つの命題として証明。
- `steps`: 負次数の変換、引数の符号変換、同類項の整理の3段を証明し、最後に連結。

`candidate.json` は生成された候補そのもの、`request.json` は元の対象に候補を付加した入力である。
`prompt.txt` と `schema.json` は生成時の指示と出力形式を保存している。
`generation.json` は終了コード、経過秒数、元入力のSHA-256を記録する。
`certificate.lean`、`result.json`、`report.md` は最終検証器で検査し直した証拠と説明である。

再検証:

```sh
lake build
python3 scripts/replay_examples.py
```

再検証では生成AIを呼び出さず、保存リクエストから再生成した証明と
保存証明の一致を調べたうえでLeanを実行する。環境と入力のハッシュも検査する。

## 拡張版のAI生成例

`recurrence.target.json` はLaTeXの一般三項漸化式に同類項を加えた入力を
固定ASTへ変換したものです。

\[
J_{n-1}(x)+J_{n+1}(x)+J_n(x)=\left(\frac{2n}{x}+1\right)J_n(x),
\qquad n\in\mathbb Z,\ x>0.
\]

`recurrence-direct` と `recurrence-steps` は、同じ入力について実際に
Codex CLIを呼び出した候補です。段階経路では漸化式の適用と因子の整理を
個別に証明しています。両経路ともLeanの検査と標準3公理の監査を通過しました。

`numeric-candidates.json` は係数を3に変えた誤漸化式の数値診断です。
この記録の状態は `unresolved` で、数値差のある点を候補として保存しています。


## 有理数次数・特異積分・追加条件のAI生成例

`calculus.target.json` は、追加条件x>1を明示した次の命題です。

\[
J'_{1/2}(x)+\int_0^x t^{-1/2}dt
=\frac{J_{1/2}(x)}{2x}-J_{3/2}(x)+2\sqrt{x},\qquad x>1.
\]

`calculus-direct` と `calculus-steps` に実際のAI候補を保存しました。
直接経路は隣接次数の微分と特異積分を適用します。段階経路は対称微分形、
漸化式、特異積分の3段です。段階経路の初回検証は対応する証明操作が不足して
未解決となり、既存数学補題への接続を追加して、同じ候補が証明済みになりました。
この候補をCIの回帰例として保存しています。

`numeric-calculus-candidates.json` は半整数の微分式の符号を変えた入力の診断です。
元入力は `examples/numeric-derivative-candidate.target.json`、結果はunresolvedで、
中心差分の手法・推定誤差・比較閾値も記録しています。
