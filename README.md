# primitive-lean

原始の形式化に関する Lean ソースと検証入口を管理する非公開リポジトリ。

**初回の116ファイルを原本と照合済みです。Kaggle用の段階実行Notebookを追加しました。Lean実ビルド・証明検査はまだ実行していません。**

- [Kaggle Notebook](notebooks/primitive_lean_kaggle.ipynb)・[実行手順](docs/KAGGLE.md)
- [統合本文の原稿](原始の形式化.md)
- [全定理の対応・条件・再実行](検証と再実行.md)
- [Elastica の入口](lean/Elastica.lean)
- [線形入力の原稿構成](linear_input/lean_check/README.md)
- [登録状況と残る検証条件](docs/TRANSFER_STATUS.md)
- [スマートフォンからの追加手順](docs/MOBILE_UPLOAD.md)

## 登録したもの

添付 `archive.zip` は5,469,476 bytes、585ファイル、展開後22,654,971 bytesでした。
そのうち、固定設定、Elasticaの24モジュールと入口・監査ソース、線形入力の36原稿と5追補、既存の検証スクリプト、本文原稿・出典資料など116ファイルを7コミットに分けて登録しました。
初回取り込みでは証明・設定・検証スクリプトの内容や元の改行を保持しました。その後、統合入口に明示的な `--proof-only` を追加しています。65個の証明原稿と既存の個別検証器は変更していません。

過去版、生成済みの結合Leanファイル、実験用workファイル、ログ、描画結果、任意の描画依存物など469ファイルは登録対象から外しました。元ZIPは変更していません。
[全585ファイルのSHA-256・登録区分](docs/import/archive_inventory.json)と[登録コミット・照合記録](docs/import/registered_commits.json)を参照できます。

## 検証の状態

登録内容の一致と、Leanによる証明検査は別です。この環境にはLean/Lakeがなく、今回の実ビルドは未実行です。
原稿内の過去の合格記述や定理件数を、このGitHubコミットの新しい検証結果として扱いません。

統合入口 `tools/verify.py` の `--proof-only` で、保存版監査を別扱いにして今回の証明検査だけを実行できます。元の全体検査・`--lean-only` の保存版照合で必要な
`archive/before_unification_2026-10-20.zip` は添付に含まれていません。
描画用vendorや過去出力も移していないため、全体の配送・描画監査は別途資材を整えてから実行します。
固定したLean設定は `lean/` に置いています。

## スマートフォンから続ける

[ファイル追加画面](https://github.com/Sumuji-zkdwn/primitive-lean/upload/main)から少量ずつ追加できます。
変更したソースや小さなZIPをこの対話に添付して、GitHub連携で登録を継続することもできます。
ZIP、`.lake/`、ビルド生成物、認証情報をGit履歴に入れない方針です。

