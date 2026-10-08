# 初回セットアップ

保存済み候補の検証には Python 3.12以上、Git、elan が管理する固定版の Lean / Lake を使います。Python追加パッケージは不要です。最初のツール・依存取得にはネット接続が必要で、Lean、mathlib、ビルドキャッシュは数GB規模になります。

macOS・Linuxでは、[Lean公式のインストール案内](https://lean-lang.org/install/)に従って elan を導入し、`python3`、`git`、`elan` がターミナルから利用できる状態にしてください。以下はmacOS・Linux向けの手順です。Windows向けの初回手順は未検証です。

## ソースを取得する

Gitで取得する場合:

```sh
git clone https://github.com/sann-ai/bessel-proof-agent.git
cd bessel-proof-agent
```

ZIPで取得する場合は、[リポジトリ](https://github.com/sann-ai/bessel-proof-agent)の **Code → Download ZIP** を選びます。ダウンロード先で次を実行し、展開したディレクトリへ移動します。

```sh
python3 -m zipfile -e bessel-proof-agent-main.zip .
cd bessel-proof-agent-main
```

ZIPにはプロジェクトのGit履歴が含まれません。Lakeはmathlibなどの依存をGitで取得するため、ZIPから利用する場合もGitを用意してください。

## 固定環境を準備する

プロジェクトのディレクトリ内で実行します。

```sh
elan toolchain install leanprover/lean4:v4.34.0
lake exe cache get
lake build
python3 scripts/doctor.py
```

`lean-toolchain` は `leanprover/lean4:v4.34.0`、`lakefile.toml` のmathlibは `db00fb3901b1bb4954f8a2373285959a5930bbfa` に固定しています。`lake-manifest.json` は間接依存のコミットも記録します。これら3ファイルを保持したまま上記を実行してください。通常の導入・再検証では `lake update` や最新版への更新は必要ありません。

`doctor.py` はPython、Git、固定版のLean / Lake、依存コミット、ビルド出力の存在を確認します。インストール、AI実行、認証情報の読み取り、個人記録ディレクトリの作成は行いません。終了コード `0` は全項目確認済み、`1` は準備が必要な項目があることを表します。ソース更新後のビルドと証明の検査は、次の手順で行います。

## 最初の検証と再検証

保存されたAI候補を検証し、生成された証明を再検査します。出力先には未使用のディレクトリを指定してください。

```sh
python3 -m bessel_agent verify demo/direct/request.json --output runs/first-check
python3 -m bessel_agent replay runs/first-check
python3 -m bessel_agent replay demo/direct
```

`proved` と、再検査時の `replayed: true` を確認します。これらの操作はCodex CLI、AIへの接続、APIキーを使いません。固定環境の取得とビルドが完了した端末ではローカルで実行できます。

全保存例とテストを実行する場合:

```sh
python3 scripts/replay_examples.py
BESSEL_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -v
```

`runs/` は手動検証の一時出力先としてGit管理から除外しています。個人の蓄積記録の既定保存先はリポジトリ外の `~/BesselProofAgentData/archive` です。共有・公開の対象は、記録を作成した利用者が選びます。アーカイブ操作はREADMEの対応節を参照してください。

## 新しいAI候補を生成する場合

新規生成には、利用者本人の [Codex CLI](https://learn.chatgpt.com/docs/codex/cli) と [認証](https://learn.chatgpt.com/docs/auth)を用意します。本人のChatGPTアカウントまたはAPIキーによる認証を使用し、リポジトリに認証情報を保存しません。

```sh
codex login
codex login status
python3 -m bessel_agent.generate demo/target.json --route direct --output runs/my-first-generation
```

モデル・推論量の条件と生成経路の指定はREADMEの「AIで新しい候補を生成する」を参照してください。セットアップや環境診断がCodexをインストールしたりログインしたりすることはありません。

## 準備に失敗した場合

- `python3`、`git`、`elan` が見つからない: それぞれを導入し、ターミナルを開き直してPATHを確認してください。
- 固定版Leanが未導入: 上記の `elan toolchain install` を実行してください。doctorは自動ダウンロードを行いません。
- 依存が未取得・キャッシュが不足: ネット接続と空き容量を確認して `lake exe cache get`、`lake build` を実行してください。
- 依存コミットがlockfileと異なる: 利用中のソースと3つの固定環境ファイルを確認してください。新しいclone・ZIP展開先で手順をやり直すと、既存作業を保持して切り分けられます。
- 保存証明の再検査が環境差分を報告: 記録に対応する版のソース・固定環境を使ってください。現行版で再評価するときは、保存入力を `verify` に渡して新しい出力先へ記録します。

## 確認した環境と範囲

macOS arm64、Python 3.14、Lean 4.34.0で、作業ツリーから分離した一時cloneとGit履歴を含まないZIP展開先の両方を検査しました。既存の固定コミットの依存・コンパイル済みmathlibキャッシュを再利用し、各展開先でプロジェクトをビルド、doctor、保存候補の検証、生成証明と同梱証明の再検査を実行しました。今回の一時環境検査では、Lean本体と数GBの依存をネットから再取得する工程を省いています。

[GitHub Actions](https://github.com/sann-ai/bessel-proof-agent/actions/workflows/verify.yml)は Ubuntu 24.04・Python 3.12で固定環境を準備し、入力境界・Lean検証・保存例の再検査を実行します。Windowsの実行確認は今後の対象です。

## ライセンスと依存の出典

配布本体、Lean証明、文書、同梱サンプルは [MIT License](../LICENSE) で提供します。利用者が外部保存先に蓄積する入力・生成候補・検査記録は、利用者本人が共有・公開の扱いを選びます。

Lean証明はmathlibのBessel・正則化超幾何関数・Gamma・微積分の定義と補題をimportして組み立てています。依存ソースはLakeが `.lake/packages/` に取得し、各依存のライセンスと著作権表記を維持します。リポジトリとソースZIPにはこの依存ディレクトリを同梱しません。

固定した依存のうち、mathlib、Batteries、Aesop、Qq、ProofWidgets、ImportGraph、LeanSearchClient、PlausibleはApache-2.0、Lean CLIライブラリ（`Cli`）はMITです。取得した各パッケージの `LICENSE` とソースの著作権表記を参照してください。Lean本体は[公式配布元のライセンス](https://github.com/leanprover/lean4/blob/v4.34.0/LICENSE)に従います。依存のファイルやコピー・改変したコードを再配布する場合は、元のライセンス、著作権表示、改変の表示、該当するNOTICEを含めてください。
