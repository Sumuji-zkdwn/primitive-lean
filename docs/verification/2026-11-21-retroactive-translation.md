# 追加列による解釈更新：検証記録

2026年11月21日（日本時間）。研究本文と定理の対応は
[研究入口](../research/2026-11-21-retroactive-translation.md)を参照。

## 実行対象

基準は `main` の `8ed4c9347609ff350f947da7e44101abcd993ed9`。
その上に追加した作業中のソースを検証した。
したがって基準コミットだけを新証明の識別子として使わず、
[機械可読のローカル証跡](retroactive-translation-20261121/local-evidence.json)
に、実際に読んだLean・Python・基準JSON・依存設定・検証入口のSHA-256を記録した。

固定環境はLean `4.36.0-rc2`（commit
`b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`）、mathlib
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`。
リポジトリのtoolchain、lakefile、依存manifestの固定値を使用した。

## 実行結果

```bash
python3 -B -X utf8 tools/verify.py --retroactive-translation-only
```

**終了コード0、`passed: true`。** 2モジュールの実ソースを新たに
`--trust=0` でコンパイルし、28個の明示的定理と、自動生成補題を含む30件を監査した。
コンパイル・監査の警告は0件。
公理依存は `propext`・`Classical.choice`・`Quot.sound` の範囲内で、
`sorryAx` や独自の未証明公理は含まれない。

| 検査対象 | 結果 |
|---|---|
| `Research.RetroactiveTranslation` | 明示的16定理、コンパイル成功 |
| `Research.RetroactiveWorkBounds` | 明示的12定理、コンパイル成功 |
| 両モジュールのローカル定理公理監査 | 自動生成補題込み30件、すべて許可公理内 |
| 4本のPython検算と4個の保存JSON | 一時ディレクトリで再生成し、全フィールド一致 |
| 既存 `tools/check_pr_integration.py` | 成功。保持対象478ファイルのソース監査 |
| 既存 `test_pr_integration.py` | 44テスト成功 |
| 新しい検証入口・workflow | Python構文とYAML構造を確認 |

ここでの成功はこの追加の検証と上表の範囲を表す。
リポジトリ全体のLean統合検査をローカルで再実行した結果ではない。
全体の統合CIと専用CIの結果は、対象PRの実際のhead SHAに結び付いたActionsを参照する。

## 有限検算

Python標準ライブラリだけを使用する。整数・集合・写像・有理数の判定は厳密計算で、
乱数標本は使わない。第1段階のエントロピーと一部の表示小数だけ浮動小数点を使う。

| 検算 | 実行件数 |
|---|---:|
| 直接列挙した置換履歴 | 14,424 |
| ビット暗号化・復号の往復 | 131,072 |
| 秘密表と観測prefix | 1,280 |
| 4状態上の二値写像対 | 256 |
| 全値付き適応DPの予算組 | 28 |
| 大きい例の対称性DPの予算組 | 65 |
| 最適方策の表・列再生 | 3,584 |
| 期待予算の反例 | 64 |
| 反復二乗と指数削減の算術一致 | 34,580 |
| 差分更新の恒等式 | 10,640 |
| 関連基点の恒等式 | 13,300 |

検査器は保存JSONを検査中に上書きしない。
隔離したコピーで、保存結果の改変・欠落を拒否することを確認した。
検証入口と4本の検算器は、assertが無効になる `-O` を拒否する。
実験ディレクトリの入力ハッシュは検査前後で一致した。

## 形式証明の境界

次の事項は、このLean監査の結果に含めない。

- 適応的照会履歴に条件づけた独立性や、確率戦略全体に関する最適成功率。第2段階の手証明と有限DPで扱う。
- 一般の情報エントロピーの不等式。
- RSA型の指数削減に対する一般の数論的証明。この追加では、再利用の代数的等式をLeanで証明し、小さな法で指数削減を検算した。
- 一般攻撃者の逐次計算量、秒数で測る期限、新規暗号の意味的安全性。

有限例の合格や、候補を更新する一実装の費用を、一般攻撃者に対する下界として扱わない。
元のPython結果にある `lean_verification: not performed` は、元の有限実験がLeanを実行しないという記録として保持している。
今回追加したLean証明の実行結果は、この検証記録と機械可読証跡が担当する。

## 再実行とCI

有限検算だけを実行する場合：

```bash
python3 -B -X utf8 tools/check_retroactive_translation.py
```

固定環境を準備し、Leanも含めて確認する場合：

```bash
cd lean
lake exe cache get Mathlib.Data.Set.Function Mathlib.Data.Fintype.Card \
  Mathlib.Data.Fintype.BigOperators Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Algebra.Group.Basic
cd ..
python3 -B -X utf8 tools/verify.py --retroactive-translation-only
```

新モジュールはGitの追跡対象として取得した状態で実行する。
既存の汎用監査器は `git ls-files` から対象を特定し、未追跡モジュールを成功扱いしない。

専用workflowは
[`.github/workflows/retroactive-translation.yml`](../../.github/workflows/retroactive-translation.yml)。
PRのhead SHAをcheckoutし、同一の検証入口を実行する。
生成結果は `verification/retroactive-translation/` と
`verification/retroactive-translation-lean/` に置き、Actions artifactにも保存する。
`tools/verify.py --integration-only` にも同じ追加検証を登録した。
