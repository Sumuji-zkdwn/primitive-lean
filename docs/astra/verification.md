# Astra 初回導入の検証記録

2026-11-09 に、実装コミット **`e71438c5d017058f413a542b827a4529bb90b7c9`** を未変更の作業ツリーで検査した。`python -B -X utf8 tools/verify.py --integration-only --rebuild` は **25 段階すべて成功**した。機械可読の結果、使用版、各ログと入力の SHA-256 は [validation.json](validation.json) に保存する。

この記録を追加するコミットでは証明・検証器を変更しない。検査対象の 221 入力（生成原稿・基礎検証レポートを含む）は、記録の追加時にもハッシュ一致を確認した。生成物は通常の検証で再生成されるため、その後の別の実行では実行時間を含むレポートのハッシュは変わり得る。

## 実行結果

| 検査 | 結果 |
|---|---|
| 初回導入 | 10 原稿、126 定理、154 名前付き宣言。既存 29 定理を再利用 |
| 共通 Lean 検証 | **2,646 定理・3,581 名前付き宣言**、`--trust=0` |
| 公理監査 | 既存の公理集合と一致。使用公理は `propext`・`Classical.choice`・`Quot.sound` のみ |
| 警告・禁止記法・想定外公理・途中変更 | すべて 0 |
| 固定依存 | mathlib を含む 9 パッケージのリビジョン一致 |
| 原始の定理の直接利用 | elaborated proof value 内の **11 定理・12 参照**を確認 |
| 原本・登録監査 | 248 retained files、133 supplement groups。追加原本 14 モジュールは source commit の Git blob とも一致 |
| リポジトリ unittest | **161 件成功**。Astra の 14 検査を含む |
| CI 指定の別枠 pytest | 27 ファイル、**128 件成功**。unittest と対象が重なるため合算しない |
| 有限検算 | 16 本成功 |
| ARC3 オフライン検査 | 173 passed、8 skipped、3 subtests passed。ゲームの再実行はしていない |
| 独立 Lean モジュール | MovingCurve の核検査・公理監査、Okanohara bridge、FiniteMarkov transport が成功 |

2,646 / 3,581 は共通 joint assembly の件数であり、独立モジュールや自動生成された補助宣言を足したリポジトリ全体の件数ではない。追加定理数 126 とも区別する。

独立した Astra の focused compile でも、新規 126 定理と既存 29 定理を新たに検査した。生成補助宣言を含む対象名前空間の 283 宣言の公理監査、12 直接参照の検査、警告・エラーなしを確認した。この独立検査だけで統合成功とは判定せず、上記の全体再ビルドを実行した。

## 再実行

Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持する。今回のローカル環境は Windows、Python 3.14.5、pytest 9.2.0、NumPy 2.5.4。リモート CI の Python 版とは別に記録する。

```bash
python -B -X utf8 tools/check_astra_physics.py
python -B -X utf8 tools/verify.py --integration-only --rebuild
```

mathlib の取得と Python 依存の準備は [README](../../README.md) の手順を参照。Windows で原本のバイト監査を再現する場合は、Git の `core.autocrlf=false` で新しく checkout する。新しい保存原本には `.gitattributes` の `-text` を設定し、改行変換を防ぐ。

追加した proof-edge 検査は、元の定理が参照先に**論理的に依存せざるを得ない**ことを示すものではない。今回の証明値が原始の定理を実際に利用していることを検査する。`tests/test_astra_physics.py` は原本改変、import 除去以外の変換、再利用先の改変、依存の欠落、登録順序、参照の欠落・重複などを拒否する。

## 本文の再生成

原始の本文・検証案内・旧線形入力の入口の 3 HTML を、既存 renderer と既存出典の Markdown 3.11.1 / KaTeX 0.16.11 で再生成した。依存物は Research から読み取り専用でコピーし、ローカルだけに置いた。

本文には Astra の 16 数式を追加し、計 1,221 数式となった。検証案内は 48 数式、旧入口は 0 数式のまま。既存数式の脱落、KaTeX error、未展開 placeholder、重複 anchor はなく、ローカルフォント参照 60 件も存在する。ブラウザーのスクリーンショットによる外観確認は実施していない。

既存 main の本文で、単一 display に `tag{A}` と `tag{B}` があるため renderer が失敗した。数式と両ラベルを保って二つの display に分ける最小修正を行った。本文比較では、この修正だけを施した旧版を同じ renderer で生成して比較した。HTML と vendor は再生成物・ローカル依存として、今回の Git 変更には含めていない。

## 初回の失敗と修復

作業フォルダー隣の `evidence/` に、成功記録とともに失敗の原記録を残している。

- 新しい Windows checkout の 38 ファイルに CRLF 変換によるハッシュ不一致があった。全件で HEAD blob との改行以外の一致を確認し、HEAD の元バイト列に復元した。既存の保存台帳や証明内容は変更していない。
- 旧 Python 環境には pytest がなく、既存テスト 1 モジュールの import が失敗した。隔離した `.venv` に固定依存を準備し、最終検査では全テストを通した。
- 最初の全体 Lean compile 自体は成功したが、検証器を実装中に実行したため、入力変更検出が最終結果を拒否した。その記録は成功と扱わず、コミットを固定して全体を再ビルドした。
- 既存の二重式番号による renderer の失敗は、上記の最小修正で解消した。

この記録はローカルで確認したソース・証明・検査の記録である。GitHub Actions の成功や main へのマージは別に確認する。一般の周期非線形 PDE の閉じた解、非局所 RKHA や全モードのスペクトル収束を証明したという結論も含めない。数学的な導入範囲は [Astra の入口](README.md) にある。
