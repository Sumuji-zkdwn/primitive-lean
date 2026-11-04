# ARC・Kaggle ツールの統合（2026-11-02）

## 取り込み元

原本の PR と実行記録は保持し、現在の研究ブランチに次を追加した。

| 領域 | 元 PR / 固定コミット | 取り込んだ範囲 |
|---|---|---|
| ARC Explorer | #1 / `abc413de1369d94fbe486065d779cf8b3bc22c9f` | experiments/arc3、3 個の tools/arc3_*、2 workflow、改行保護、ignore、`--arc3-only` |
| 494 定理 handoff | #2 / `0298d2092c60a52fb39fad10c396f907253a8f74` | builder、packager、2 auditor、tests、workflow、KAGGLE.md、履歴監査ノート |
| 717 定理 handoff | #4 / `2d9269a9e7f6fa0bb4e555e3d04a652b3c42fda5` | 717 用 builder、packager、auditor、support、tests、workflow、KAGGLE_717.md |

元の証明、公開探索器のソース・LICENSE・provenance、履歴レポートは変更していない。
README と統合入口は追加のみ。Kaggle workflow の対象コミットと起動条件は以下の理由で変更した。

## 現在の検査と歴史的 handoff の区別

`python -B -X utf8 tools/verify.py --arc3-only` は 61 個の既存証明原稿の
Git blob と 475 定理の歴史的索引を照合し、ARC のローカルテストを実行する。
この 475 は現在の Lean 定理総数ではなく、ARC 接続元の固定索引の件数である。
Lean の再検証とゲームのプレイは行わない。

494 用と 717 用の Notebook は固定されたファイル集合・期待定理数・期待宣言数を持つ。
追加モジュールを持つ統合 HEAD をそのまま渡す配布器ではない。
717 workflow は証明ソース `185a1713f2fca219e5f9fb1c5aa11955925cb97f` との
バイト一致を要求するため、現在の研究ソースで実行すると意図的に失敗する。
494 用も 494/538 の固定集合を対象とし、統合版の証明成功を検証・配布できない。

このため両 workflow は **workflow_dispatch のみ**とし、検査対象を上表の
歴史的 handoff コミットへ固定した。これは手動で過去版を再検証・包装する入口であり、
現在の統合ソースの CI として扱わない。統合版の検証は現在の `tools/verify.py --proof-only`
と通常の研究用 CI を使う。Notebook の生成テストは構造・ハッシュ・設定の検査であり、
Kaggle 実行や拡張ソースの証明検査ではない。

## ローカル検査

Windows / Python 3.14 で `--arc3-only` が成功した。
61 ソースの blob 一致、173 passed / 8 skipped / 3 subtests passed。
利用した pytest は 9.2.0、numpy は 2.5.4。SDK 未導入のため SDK 関連はスキップ。
これは固定 Linux runtime 全体での実行結果ではない。

リポジトリ unittest は統合コミット後に再実行し、21 tests が成功した。
新しい Lean 実行、公開ゲーム実行、Kaggle Saved Version、競技提出はこの追補では行っていない。

## 改行と原本

Windows の自動 CRLF 変換で、内容が同じでも blob 照合が失敗することを確認した。
取り込み元 #1 の `.gitattributes` は Lean/inc と vendored 探索器を `-text` として保持する。
今回のローカルコピーは元の Git blob バイトへ復元して照合した。
索引の期待ハッシュの書換えや、検査の弱体化は行っていない。
