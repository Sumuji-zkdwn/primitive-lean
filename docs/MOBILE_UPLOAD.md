# スマートフォンからファイルを追加する

初回コミットと現行ソース116ファイルの登録・照合は完了しました。以後は GitHub にログインしたスマートフォンのブラウザで追加できます。ブラウザからの操作には Personal Access Token の入力は不要です。

## 一番手数が少ない継続方法

今後変更した Lean ソースを含む小さな ZIP またはファイル群をこの対話に渡してください。こちらでソースの相対パスと除外対象を確認し、GitHub 連携で段階的に登録します。ZIP 自体を Git 履歴に追加する方法ではありません。

今回の添付 archive.zip は5,469,476 bytes・585ファイルと実測しました。現行ソース等116ファイルを原本と同じ相対パス・同じバイトで登録済みです。以後は変更したファイルだけで十分です。1.3 GB の環境全体や依存キャッシュは不要です。GitHub への送信が止まった以前の処理を再開する必要はありません。

## ブラウザだけで1ファイルずつ作成する

1. [新規ファイルの画面](https://github.com/Sumuji-zkdwn/primitive-lean/new/main)を開きます。
2. ファイル名に元の相対パスを入力します。`lean/lean-toolchain` は登録済みなので重複作成しません。スラッシュでフォルダも作成できます。
3. 元ファイルの内容をそのまま貼り付けます。バージョン番号を推測して書きません。
4. Preview とパス・差分を確認し、Commit changes で確定します。初期の小さな追加は main へ直接コミットできます。
5. 確定後、GitHub のファイル画面を開き直し、パスと内容が存在することを確認します。コミット画面で変更ファイルも確認します。

同じパスが既にある場合は新規作成せず、そのファイルの編集画面を使って差分を確認します。ボタンが見えない場合はブラウザの「PC版サイト」を試してください。端末上での表示・操作はこの作業では未検証です。

## スマホ内の実ファイルをまとめて追加する

1. ZIP がある場合、先にスマホ上で展開します。ZIP を GitHub に上げてもソースへ自動展開されません。
2. GitHub で追加先フォルダを開き、Add file → Upload files → choose your files を選びます。
3. 同じフォルダに属するファイルを 10〜30 個程度ずつ選びます。サブフォルダが違うものは分けます。
4. アップロード一覧のパスとファイル名を確認します。例えば `lean/Elastica/Geometry.lean` をリポジトリ直下の `Geometry.lean` にしないでください。
5. コミットし、ファイル画面とコミット差分で実際の登録を確認してから次へ進みます。

追加先フォルダがまだ無い場合は、先に「新規ファイルの画面」で、その中に置く実ファイルを1つ作ります。スマホのファイル選択ではフォルダ階層を保った一括選択ができないことがあるため、同一フォルダ単位にします。

GitHub 公式のブラウザ追加上限は1回100ファイル、1ファイル25 MiBです。本手順の10〜30個は確認しやすさを優先した目安です。

`.gitignore` があることを理由に、ブラウザで選択したファイルが自動除外されるとは考えないでください。`.lake/`、依存物のコピー、コンパイル結果、認証情報、ZIP、過去保存版は選択しません。ソースの `.inc` や固定依存の `lake-manifest.json` は残します。今回の `All.lean`・`MainResult.lean` は既存検証器が再生成するため除外済みです。`work*`・`before`・過去のprovenance保存版も通常の追加対象にしません。

## 登録済みの構成と次の確認

| 段階 | 確認・追加する候補 | 完了判定 |
|---|---|---|
| 1 設定 | `lean/lean-toolchain`、`lean/lakefile.toml`、`lean/lake-manifest.json` | 実物を読み、GitHub側に同じ内容で存在 |
| 2 Elastica | `lean/Elastica.lean`、`lean/Elastica/*.lean` | 原本一覧と登録済みパスを照合 |
| 3 線形入力 | `linear_input/lean_check/*.inc`、`linear_input/verify_lean.py` と実際の補助ソース | 原本一覧・相対パスを照合 |
| 4 検証入口 | `tools/verify.py`、`tools/verify_main_result.py`、必要な設定・参照データ | スクリプトが読むファイルも含めて不足を確認 |
| 5 検査 | 対象コミットで実ビルド・検証 | コミットSHA・実行コマンド・終了コード・ログを記録 |

実際の原本も Lean プロジェクトを `lean/` に置きます。`lakefile.lean` を新造して `lakefile.toml` を置き換えません。現行原本の36原稿・5追補はすべて登録済みです。

上表の設定・証明原稿・検証スクリプトは登録済みです。実ビルドは未実行です。全体の `tools/verify.py` は保存版の照合も行い、添付に存在しない `archive/before_unification_2026-10-20.zip` が必要です。本文描画用vendorなども未登録のため、全体監査の再実行条件は[転送状況](TRANSFER_STATUS.md)で別途確認します。

## 記録

[転送状況](TRANSFER_STATUS.md)で登録済みと未転送を区別します。登録だけで証明検査合格とはしません。GitHub Actions はまだ追加していません。

## 公式手順

- [新しいファイルの作成](https://docs.github.com/en/repositories/working-with-files/managing-files/creating-new-files)
- [ファイルのアップロード](https://docs.github.com/en/repositories/working-with-files/managing-files/adding-a-file-to-a-repository)
