# Kaggle Notebookとの対応

## 2026-10-29: CI引継ぎからKaggle保存Version 2までの検証

検証対象は固定コミット [`5d23c590398680aa7a67919a54fc2bdd915614b4`](https://github.com/Sumuji-zkdwn/primitive-lean/commit/5d23c590398680aa7a67919a54fc2bdd915614b4) です。以下のActions検査、Kaggle実行、結果ZIP監査は独立した証拠として扱います。この記録を追加する文書更新コミットや、それ以降のコミットをKaggle実行済みとするものではありません。

### 1. GitHub Actionsの検査と引継ぎ成果物

[Run 40703848720](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/40703848720)、attempt 1 は上記コミットに対して成功しました。Pythonテスト8件が合格し、fresh proof-only検査は **494定理・538宣言、終了コード0**、joint/supplement両段階のLean警告なしでした。Notebook生成も成功しています。

取得したhandoff artifact IDは `12823706986`、証明記録artifact IDは `12822624002` です。両ZIPのサイズ・SHA-256がGitHubの記録と一致し、CRC検査にも合格しました。`handoff.json` のソースコミット、run ID、attemptと、次の実ファイルのサイズ・ハッシュも照合しました。

| ファイル | Bytes | SHA-256 |
|---|---:|---|
| `primitive_lean_proof_check.ipynb` | 53,684 | `b745f55b779db4712deb75fe057baef5d972002e99997ed14093cc409acc0240` |
| `primitive_lean_setup_one_cell.ipynb` | 53,800 | `a179143832148d1d404e4a6041dbc61fcf244a9601b109e6329360026e89efb1` |
| `audit_kaggle_result.py` | 3,921 | `a2b5f3be3bb9046a40726fb577d872ec58391af00e5352ebb97a36e1c237e78c` |

handoff ZIP自体のSHA-256は `b821c0ec697bcd617350460ced6b8443685f5586350a7d98947f9a703da209b8` です。監査器は上記固定コミットのリポジトリ内ソースともバイト単位で一致しました。

### 2. 新規Kaggle Notebookの保存Version実行

取得したhandoff ZIPから証明検査Notebookを再生成せず取り出し、新規Notebook `sumuji/primitive-lean-proof-check` へ元のファイルをアップロードしました。実行証拠は次の **保存Version 2** です。

| 項目 | 記録 |
|---|---|
| 保存Version | [Version 2 / scriptVersionId 363335255](https://www.kaggle.com/code/sumuji/primitive-lean-proof-check?scriptVersionId=363335255) |
| 確定ログ | [Version 2のログ](https://www.kaggle.com/code/sumuji/primitive-lean-proof-check/log?scriptVersionId=363335255) |
| 保存出力 | [Version 2のOutput](https://www.kaggle.com/code/sumuji/primitive-lean-proof-check/output?scriptVersionId=363335255) |
| Notebook内実行ID | `20261029T012228-309486` |
| Input | `sumuji/archive-zip`、Dataset Version ID `21217503` |
| 実行設定 | Internet有効、アクセラレータなし |
| Kaggle完了表示 | **Successfully ran in 358.1s** |
| 検査結果 | source/setup/proofsすべて `passed`、117ファイル照合、**494定理・538宣言、proof exit code 0** |

Version 1は取り込み時の未実行Quick Saveであり、証明実行の証拠には使用していません。NotebookはPrivateのままです。上記358.1秒はKaggleの実行時間表示で、出力保存の待機時間を含む総作業時間ではありません。

Version 2の実行中に同じ保存VersionのNotebookをダウンロードし、アップロードしたCI NotebookとMarkdown・コードの全セルを比較しました。セル種別とソース文字列は完全一致しました。Kaggleが付加する設定情報を含むJSON全体のハッシュは、元のCIファイルのハッシュと区別しています。

### 3. 同じ保存Versionから取得した結果ZIPの再監査

Kaggleの実行成功と出力保存の確定後、Version 2のOutput画面から `primitive_lean_result.zip` を取得しました。

- サイズ: **60,353 bytes**
- SHA-256: `becc42a804a5915466ae68514853848d2ba48fd7a9d436a05956e96685e2bc8c`
- ZIP内の実行ID: `20261029T012228-309486`
- 使用した監査器: 同じhandoff内の `audit_kaggle_result.py`（変更なし）
- 再監査結果: **PASS、監査器の終了コード0**

handoffを展開した場所で、完全なソースコミットSHAを指定して実行しました。

```bash
python -X utf8 audit_kaggle_result.py primitive_lean_result.zip --expected-source 5d23c590398680aa7a67919a54fc2bdd915614b4 --out audit-saved-version-2.json
```

追加照合では、117ファイルのハッシュ辞書がCI Notebookの実効期待値と全件一致しました。proof reportと実行状態内のレポート、ログハッシュ、9依存revisionも整合し、CI/Kaggle間で宣言一覧、公理監査結果、証明ソースハッシュ、結合コンパイラ入力 `All.lean` / `MainResult.lean` のハッシュも一致しました。

今回の新規実行には、**Actions artifact取得 → 元ファイルのハッシュ照合 → 新規Notebookへの取り込み → 固定保存Versionでの実行成功 → 同Versionの出力ZIP取得 → 既存監査器によるPASS** という観測・照合の来歴があります。[PR #2の追記記録](https://github.com/Sumuji-zkdwn/primitive-lean/pull/2#issuecomment-6485595106)も参照してください。Notebook内実行IDとKaggleのscriptVersionIdは別の識別子です。

### 検証範囲と過去記録との区別

- 対象は必要117ファイルとadapter overlaysによるproof-only検査です。`source_subset_only=true` であり、リポジトリ全体のclone照合ではありません。
- `clean_project_build=false`、`historical_preservation` / `delivery_and_rendering` は `not_checked` です。過去全成果物の保存・配送・描画やコンペスコアまで検証したものではありません。
- 2026-10-25の旧固定版実行、および2026-10-28の下書き実行記録は別の証拠です。今回の保存Versionの来歴を、過去の下書き実行へ遡って適用しません。
- 今回の記録追加では、証明原稿、Notebookファイル、既存の検証済み成果物・監査記録を変更していません。

## 2026-10-25の実行記録（旧固定版）

2026-10-25、ユーザーのKaggleで `--proof-only` が成功しました。**494定理・538宣言、終了コード0**。提供された結果ZIPの生ログ、固定コミットの117ファイル、9依存revision、2つの結合コンパイラ入力ハッシュを照合しました。[実行記録と証拠](verification/2026-10-25-kaggle.md)を参照してください。過去版保存・配送・描画の監査は別扱いです。

## 環境準備を1セルで実行する版

`STATE is not defined` が出る場合は、初期化セルが現在のカーネルで実行されていません。[環境準備・1セル版](../notebooks/primitive_lean_setup_one_cell.ipynb)なら、初期化、原本照合、環境準備を一つのセルで実行できます。同じ原本ZIPをInputに用意し、InternetをOnにして、唯一のコードセルの▶を押してください。初期設定は `RUN_SETUP=True`、`RUN_PROOFS=False` です。

この版は、空のPython名前空間からの初期化・117ファイルの照合・結果保存をローカルで確認しました（ネットワーク環境準備を無効化した確認）。このローカル確認自体は環境準備・Lean検査の実行ではありません。その後の初期版のKaggle実行は、2026-10-25の実行記録で別途確認しています。

再生成は `python scripts/build_kaggle_notebook.py --source-ref 2e058f2d76e7c7d1fb0f811bcb26a990c47b10d9 --setup-one-cell` です。

[primitive_lean_kaggle.ipynb](../notebooks/primitive_lean_kaggle.ipynb)をKaggleのImport Notebookで読み込んでください。CPUで使うNotebookです。GPUは不要です。

## 最初の実行

1. 同じ `archive.zip` をKaggleのInputに追加するか、元の原本フォルダがある環境でNotebookのセルを実行します。
2. 設定セルは最初のまま `Run All`。自動検出できない場合だけ `SOURCE_PATH` にZIPまたは原本フォルダのパスを指定します。
3. `source: passed`、`setup: not_run`、`proofs: not_run` と、対応コミット・117ファイルの照合結果・結果ZIPを確認します。

別Notebookや別セッションの `/kaggle/working` に原本がある場合、そのパスが現在のセッションにも存在するか確認してください。見つからなければ原本ZIPをInputに追加します。元Notebookをそのまま使う場合は、このNotebookの6つのコードセルを同じ順序でコピーしても使えます。

初期状態のファイル照合にはInternetもGitHubトークンも不要です。GitHubから直接読み込む場合だけ `SOURCE_MODE="github"` とし、Kaggle Secretsで `GITHUB_TOKEN` をNotebookに許可します。対象リポジトリのContents読み取り権限だけを使います。トークンをセルの本文へ貼り付けません。

## 次の段階

| 目的 | 設定セル | 実行内容 |
|---|---|---|
| ファイルの対応確認 | 初期設定のまま | 原本を検出、固定ハッシュを照合、アダプターを適用、結果保存 |
| Lean環境を用意 | `RUN_SETUP=True`、Internet On | 原本のLean版・mathlib revisionを保持、依存キャッシュ取得とrevision照合 |
| 実ビルド・公理監査 | `RUN_SETUP=True`、`RUN_PROOFS=True` | `python -X utf8 tools/verify.py --proof-only` |

各段階の成否は別々に記録します。環境準備やファイル照合の成功を証明検査の成功として表示しません。初回の依存取得には時間がかかります。Kaggleの作業フォルダに使える同じ依存キャッシュがあれば再利用します。キャッシュのrevisionは検査します。

`REBUILD=True` はこのプロジェクトの `.lake/build` だけを再作成する設定です。依存キャッシュや原本ZIPを削除しません。

## GitHubと一致させる範囲

初期版が対応するソースコミットは `2e058f2d76e7c7d1fb0f811bcb26a990c47b10d9` です。
Notebookはそのコミットの検査対象ソースの部分集合を扱い、リポジトリ全体をcloneしたとは記録しません。

- 原本116ファイルのパスとSHA-256を照合します。
- 原本ZIPにある旧 `tools/verify.py` を受け入れ、Notebook同梱の固定版に置き換えます。`tools/proof_only.py` も配置します。
- 結果の117ファイルを再照合します。65個の証明原稿と元の個別検証器は変更しません。
- 実検査の直前・直後にも同じハッシュを照合し、途中で書き換わったソースを固定コミットの合格とは扱いません。
- `notebook_run.json` に対応コミット・全対象ハッシュ・実行段階を記録します。

ソースを更新した場合、古いNotebookはそのまま最新版と一致するとは限りません。更新したcheckoutで次を実行して固定版を再生成します。

```bash
python scripts/build_kaggle_notebook.py --source-ref <アダプターを含むソースコミットの40桁SHA>
```

## 証明検査と保存監査の違い

新しい `--proof-only` は元の統合入口から、既存の `linear_input/verify_lean.py` と `tools/verify_main_result.py` を順に呼びます。今回生成されたレポート・終了コードを使います。前回の成功レポートは退避してから実行するため、その流用による合格を防ぎます。

このモードは、欠けている `archive/before_unification_2026-10-20.zip` による過去版保存監査を実行しません。レポートに `historical_preservation: not_checked` と明記します。元の全体検証・`--lean-only` は従来どおり別に残ります。過去ZIP、描画用vendor、配送用資材の不足は、証明検査とは別の条件です。

`--proof-only` の `passed` は、その実行のLeanライブラリビルドとjoint/supplementの証明・公理検査の範囲だけを指します。

## 結果の受け渡し

Notebookが `/kaggle/working/primitive_lean_result.zip` に保存する結果ZIPをOutput欄からダウンロードして、この対話へ添付できます。失敗時にも今回のログ・段階別状態を保存します。古い成功記録、依存キャッシュ、ソースZIP、認証情報は結果ZIPに含めません。NotebookからGitHubへの書き戻しやKaggleコンペへの提出は行いません。

## 初期版で確認した範囲（2026-10-25）

- 添付原本ZIPからの取り込み、117ファイルの再照合、未実行状態の区別、結果ZIP生成をローカルで実行しました。
- Notebookの全コードセルを構文検査しました。
- 古い成功レポートの拒否、非零終了コードの拒否、追補失敗時の扱い、途中のソース変更の拒否、失敗ログの保存について5テストが成功しました。
- Kaggle実機の操作・環境準備・Leanコンパイルはユーザーが実行しました。その結果ZIPを受け取り、494定理・538宣言の成功と生ログ・固定ソースの対応を照合済みです。こちらでの独立したビルド再実行は行っていません。

## 参照

- [Kaggle公式のSecretsクライアント](https://github.com/Kaggle/docker-python/blob/main/patches/kaggle_secrets.py)
- [Lean公式の環境構築手順](https://lean-lang.org/install/manual/)
- [固定したElanインストーラー](https://github.com/leanprover/elan/blob/9605b24b08cf68b78dce0014b6fa01be1f8e2cee/elan-init.sh)

## 結果リンクが404になる場合

Kaggleでは絶対ファイルパスを使ったIPython FileLinkが正しく解決されないことがありました。Notebookはその形式のリンクを使わず、結果ZIPのコピーを作業フォルダ直下の `primitive_lean_result.zip` に作成するよう修正しました。右側のOutput欄を更新し、このファイルのメニューからDownloadします。

既に完了した検査の結果を取り出す際は、元のタイムスタンプ付きZIPを `primitive_lean_result.zip` にコピーすればよく、証明検査の再実行は不要です。元のZIPが残っていることを確認してからコピーしてください。

## GitHub ActionsからKaggleへ固定版を渡す

`.github/workflows/lean-kaggle-validation.yml` は push、`main` 向けPull Request、手動起動で動きます。1回のActions実行はイベントのソースコミットをcheckoutし、Pythonテスト、固定Lean toolchainとMathlibキャッシュの準備、`python -X utf8 tools/verify.py --proof-only` の順に実行します。Lean検査ログは成功・失敗どちらでもActions artifact `lean-proof-evidence-<run id>-<attempt>` に保存されます。

証明検査が成功したときだけ、同じcheckoutから2つのNotebook、結果ZIP監査器、`handoff.json` を含む `kaggle-handoff-<run id>-<attempt>` artifactを作ります。

- `primitive_lean_proof_check.ipynb`: 原本照合、環境準備、証明検査を一セルで実行
- `primitive_lean_setup_one_cell.ipynb`: 原本照合と環境準備までを一セルで実行
- `handoff.json`: ソースコミット、NotebookのSHA-256、Actions run URLと権限範囲
- `audit_kaggle_result.py`: Kaggle結果ZIPを固定ソースコミットに照合する標準ライブラリだけのCLI

Actions生成Notebookの既定は `SOURCE_MODE="auto"` です。Kaggle Inputへ既存の `archive.zip` を追加し、InternetをOnにして実行します。必要ソースを固定コミットのSHA-256一覧と照合するため、この既定モードではGitHub Secretは不要です。`SOURCE_MODE="github"` を明示した場合に限り、対象repoのContents読み取り権限を持つ `GITHUB_TOKEN` をKaggle Secretsで許可します。SecretはNotebook本文にもActionsにも渡しません。NotebookはGitHubへ書き戻さず、Kaggleコンペにも提出しません。

Kaggle実行後、Outputから `primitive_lean_result.zip` を取得します。Actions artifact内の `handoff.json` に記録された `source_commit` と照合して結果を監査します。

handoffを展開した場所では、同梱された監査器を使います。

```bash
python -X utf8 audit_kaggle_result.py primitive_lean_result.zip --expected-source <handoff.jsonのsource_commit> --out audit.json
```

監査器はZIPのパスとCRC、ソースコミット、ファイルハッシュ記録、source/setup/proofs各段階、proof-onlyの新規レポートと終了コードを確認します。Actionsの合格はGitHub runnerでの証明検査、Kaggle保存VersionとそのログはKaggle上での実行証拠、ZIP監査は返された保存記録の整合性検査です。監査器はLeanやKaggleを再実行しません。これらを互いの代わりにはせず、2026-10-25の保存済み記録も新規実行として扱いません。
