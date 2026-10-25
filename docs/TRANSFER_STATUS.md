# 登録状況と残る検証条件

2026-10-25（日本時間）

## 完了した登録

初回登録前は size=0、コミット取得は `Git Repository is empty`（409）でした。
初回コミット `04863df1363f04a0b8195c32b0e826bedfd4c5e0` を作成した後、今回の添付ZIPから現行ソースを登録しました。

| 区分 | 今回の状態 |
|---|---|
| 添付 archive.zip | 5,469,476 bytes、585ファイル、展開後22,654,971 bytes |
| 登録対象 | 116ファイル、988,501 bytes |
| 設定 | lean/lean-toolchain、lakefile.toml、lake-manifest.json を原本どおり登録 |
| Elastica | 24モジュール、Elastica.lean、Audit.lean、説明文を登録 |
| 線形入力 | 既存36原稿と追補5原稿、READMEを登録 |
| 検証入口 | tools/verify.py、tools/verify_main_result.py、linear_input/verify_lean.py を含む既存スクリプトを登録 |
| 本文・出典 | 2つの本文Markdown、現行の出典記録・抜粋を登録 |
| 内容の照合 | 各段階で全対象をGitHubから取得し、Git blob SHAを原本と比較。116件すべて一致 |
| 元のmanifestとの照合 | 登録対象116件すべてSHA-256一致 |
| Python文法 | 登録対象のPythonスクリプトを構文解析。構文エラーなし |
| Leanビルド・公理監査 | Kaggleで494定理・538宣言が成功。117ソースと生の公理監査ログを照合済み |

[添付全ファイルの区分・SHA-256](import/archive_inventory.json)と[7段階の登録コミット・GitHub照合](import/registered_commits.json)が詳細記録です。
初回登録時は原本の内容・改行を保持しました。Kaggle対応では統合入口に `--proof-only` を追加しました。証明原稿・既存の個別検証器・Lean設定は変更していません。

## 登録から外したもの

469ファイルは意図して登録していません。元ZIPは変更していません。

- 過去版の複製、before ディレクトリ、過去provenance保存版。
- 検証器が生成する All.lean / MainResult.lean、実験用workファイル。
- 過去の検証ログ・結果JSON、スクリーンショット、描画済みHTML等。
- Lean検査に不要なvendor描画依存物・Web UI。
- 元のREADMEと配布物全体のmanifest。現在のREADMEはこのリポジトリの状態を示すため別途更新。

原本全585ファイルのパス・サイズ・ハッシュ・各除外理由は inventory に残しています。
履歴や生成物を除外したことを、証明ソースの欠落や転送失敗とは扱いません。

## 実行済みのLean検査と残る全体監査

ユーザーのKaggle環境で `tools/verify.py --proof-only` が成功しました。対象コミットは `2e058f2d76e7c7d1fb0f811bcb26a990c47b10d9`、494定理・538宣言、終了コード0、所要235.365秒です。提供された結果ZIPの538件の生の公理監査、117ファイルの固定コミットとの一致、2つの生成コンパイラ入力のハッシュ、9依存revisionを確認しました。

[実行結果と証拠](verification/2026-10-25-kaggle.md)を保存しています。今回こちらで行ったのは結果の照合であり、別環境でのLean再実行ではありません。

元の統合検証入口 tools/verify.py を保持しています。ただし、この入口は保存版のバイト照合も行い、
verification/before-unification.json に指定された
`archive/before_unification_2026-10-20.zip` を必要とします。この保存ZIPは添付にありません。
期待されるSHA-256は `56869910154e94de5f98705d77e14f87ed64c88bfbe74c01e32a0c0b0b14d287` です。
記録だけから保存ZIPを捏造したり、照合を無言で省略したりしません。

全体の配送・描画検査には追加の描画依存物・過去資材も必要です。Leanの核検査と、過去版保存・配送監査は別の結果として記録します。
GitHub Actionsのワークフローは今回追加していません。

## 今後の追加

[スマホ用手順](MOBILE_UPLOAD.md)から変更したファイルだけを追加できます。
この対話への小さなZIP添付からGitHub連携で追加する経路も、今回の7段階の登録で動作確認できました。


## Kaggle対応の追加

[Kaggle Notebookと手順](KAGGLE.md)を追加しました。初回は原本の照合だけを実行し、環境準備・証明検査を段階的に有効にできます。元の統合入口に追加した `--proof-only` は、今回のjoint/supplementの検査だけを実行し、過去版保存・配送・描画監査を未検査として明示します。

原本ZIPを使ったNotebookの取り込み・117ファイルの照合・結果保存をローカルで実行し、アダプターの5テストも成功しました。その後、ユーザーのKaggleで環境準備とLeanコンパイル・公理監査が成功し、結果ZIPを照合済みです。
