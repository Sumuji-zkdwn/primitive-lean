# 5点合流追補の検査と名前空間修正

2026年10月30日（日本時間）。PR #3 の head `0631517c076b073063d981397bc3a39c6e59136e` を独立した Windows 作業コピーで検査した。以前の717定理・836宣言の検査記録はそのまま保持する。

## 修正前

`python -B -X utf8 tools/verify.py --proof-only` は終了コード1。joint検査は成功したが、追補検査が失敗した。`F0MergeChains.inc` は追補の前で `LinearInputF0Merge` 名前空間を閉じており、後続の `Merge` と `Chain` をLeanが解決できなかった。[修正前の追補検査ログ](../../evidence/local/2026-10-30-five-state-followup/original-main-result.log)にエラーを保存した。

## 修正と結果

`end LinearInputF0Merge` を追補の末尾へ移動し、既存の証明内容は変更せず、追加宣言と `Merge` / `Chain` を同じ名前空間に収めた。検査したファイルのGit blob IDは `a1971e6fdc6adf327fffbaca44c7787995077f4a`、Windows作業コピーのSHA-256は `fc2ce40986fa8db72487264bb371739503f7096a96490eb29b9b846c4b957d74`。

同コマンドを再実行し、終了コード0、jointおよび追補検査の終了コード0、警告なし。**733定理・861宣言**、全861宣言の公理監査と既存基線の公理照合が成功し、許可外公理・禁止トークン・検査中の対象ソース変更は検出されなかった。9依存のrevision照合はすべて一致した。Lean 4.30.0-rc2、Windows x86_64、依存キャッシュ利用の実行で、クリーンビルドではない。

- [proof-only結果](../../evidence/local/2026-10-30-five-state-followup/proof-only.json)
- [追補監査の詳細](../../evidence/local/2026-10-30-five-state-followup/main-result.json)・[Leanログ](../../evidence/local/2026-10-30-five-state-followup/main-result.log)
- [joint結果](../../evidence/local/2026-10-30-five-state-followup/joint.json)・[Leanログ](../../evidence/local/2026-10-30-five-state-followup/joint.log)・[ビルドログ](../../evidence/local/2026-10-30-five-state-followup/elastica-build.log)

公開するログ・JSONでは作業ディレクトリの絶対パスだけを `<workspace>` に置換した。元のファイルはローカルに保持し、検査結果、ソースハッシュ、依存revisionは変更していない。

これは明記された修正を含む作業コピーでのローカル検査であり、元headそのものの成功ではない。GitHub Actions・Kaggle実行、過去の配送物やHTML再描画は今回検査していない。任意の合流チェインの写像列への一般的な持ち上げや、既存のbranch写像との一般対応はこの結果からは導かれない。
