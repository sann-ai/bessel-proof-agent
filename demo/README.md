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
