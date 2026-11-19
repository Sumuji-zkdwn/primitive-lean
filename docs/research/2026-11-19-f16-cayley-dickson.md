# F16：符号表 epsTable は Cayley–Dickson 倍化から生成される

## 位置づけ

[F16 階数証明書の検証記録](../verification/2026-11-01-f16-rank-certificate.md) の「今回は証明していないこと」に「Cayley–Dickson 再帰による `epsTable` の生成の Lean 内検証」があった。F16 の一連のファイル（`F16Holonomy.inc` 以降）は 16×16 の符号表 `epsTable`（基底の積 \(e_ae_b=\varepsilon(a,b)\,e_{a\oplus b}\) の符号）を直接書き下して使っている。この追加は、その表が Cayley–Dickson 倍化で作られる十六元数の符号表そのものであることを Lean で示し、あわせて全次数の Cayley–Dickson 代数について基本的な符号の恒等式を証明する。

- Lean：[lean/Research/F16CayleyDickson.lean](../../lean/Research/F16CayleyDickson.lean)（名前空間 `F16CayleyDickson`、12定理）
- 独立検算：[tests/test_f16_cayley_dickson.py](../../tests/test_f16_cayley_dickson.py)
- 専用CI：[.github/workflows/f16-cayley-dickson.yml](../../.github/workflows/f16-cayley-dickson.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

## 倍化の規約

表と一致する倍化は

\[
(a,b)(c,d)=(ac-\bar d\,b,\ da+b\,\bar c)
\]

である（四つの象限の符号と引数の順序を総当たりで探して、一致するものはこの規約だけだった）。基底 \(e_i\)（\(i<2^k\)）と \(e_{i+2^k}=(0,e_i)\) について、符号は

| 象限 | 符号 |
|---|---|
| 下位×下位 | \(\varepsilon_k(i,j)\) |
| 下位×上位 | \(\varepsilon_k(j',i)\) |
| 上位×下位 | \(\bar\jmath\,\varepsilon_k(i',j)\) |
| 上位×上位 | \(-\bar\jmath'\,\varepsilon_k(j',i')\) |

（\(i'=i-2^k\)、\(j'=j-2^k\)、\(\bar\jmath=1\)（\(j=0\)）、\(-1\)（それ以外））。Lean の `cdSign k i j` はこの再帰そのもの。

## 結果

| 内容 | Lean 宣言 |
|---|---|
| **表の一致**：`F16Holonomy.inc` の `eps a b` は全256成分で `cdSign 4 a b` に等しい | `eps_eq_cdSign`（`decide`） |
| 全次数で \(e_0\) は両側単位元 | `cdSign_zero`、`eps_zero_left`、`eps_zero_right` |
| 全次数で虚単位の平方は \(-1\) | `cdSign_self`、`eps_self` |
| 全次数で異なる虚単位は反可換 | `cdSign_anticomm`、`eps_anticomm` |
| 次数を上げても下位の符号は変わらない（下位8成分は八元数） | `cdSign_succ_low`、`eps_low_octonion` |

`epsTable` と `eps` の本文は `F16Holonomy.inc` から変更せずに写した。バイト列の一致は独立検算が確認するが、joint 検査の宣言とこのモジュールの宣言を一つの Lean 環境で同一視する定理ではない。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 Research/F16CayleyDickson.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。全12定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内（表の一致は `propext` のみ）。
- `python -B tests/test_f16_cayley_dickson.py`：4テスト合格。写した本文の一致、係数ベクトル上の実際の Cayley–Dickson 乗法（符号の再帰ではない別実装）で計算した \(e_ie_j\) が \(\pm e_{i\oplus j}\) で表の符号と一致すること、次数 0〜5 で上の恒等式を確認。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 示したのは基底の積の符号の一致と、符号の恒等式だけである。非結合性・交代性の欠如・零因子など、代数全体の性質は扱わない。
2. 元資料の「あらゆる表現の `leftPencil` との同一性」や「21断面の曲率分類」は対象外。
