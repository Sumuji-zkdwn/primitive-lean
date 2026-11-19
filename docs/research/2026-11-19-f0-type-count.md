# F0：塊サイズ型ごとの冪等写像の個数（型別階乗公式）

## 位置づけ

F0 の会話資料（[02_partitions_and_chains.md](../../sources/f0_math_chat_2026-10-29/02_partitions_and_chains.md)）の表は、\(N\) 点集合上の冪等写像を塊サイズ型ごとに有限計算で数えていた（7点で型 \((4,3)\) は 420 個、\((3,2,2)\) は 1,260 個など）。[検証と再実行.md](../../検証と再実行.md) の F0 の項は「原資料の型別階乗公式の一般Lean証明 … は、この追加には含まない」としていた。この追加はその一般式を Lean で証明する。

- Lean：[lean/Research/F0TypeCount.lean](../../lean/Research/F0TypeCount.lean)（名前空間 `F0TypeCount`）
- 独立検算：[tests/test_f0_type_count.py](../../tests/test_f0_type_count.py)
- 専用CI：[.github/workflows/f0-type-count.yml](../../.github/workflows/f0-type-count.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

## 結果

有限集合 \(\alpha\)（\(\lvert\alpha\rvert=N\)）上の冪等写像 \(K_0\) の塊サイズ型を \(\lambda\)、各固定点 \(a\) の塊の大きさを \(m_a\)、型の中の値 \(k\) の重複度を \(c_k\) とする。型が \(\lambda\) の冪等写像の個数 \(I(\lambda)\) について

\[
I(\lambda)\cdot\prod_a (m_a-1)!\cdot\prod_k c_k! \;=\; N!
\qquad\Bigl(I(\lambda)=\frac{N!}{\prod_a(m_a-1)!\,\prod_k c_k!}\Bigr).
\]

| 内容 | Lean 宣言 |
|---|---|
| 第1段（多項係数）：ファイバーの大きさが \(f\) と同じ写像 \(g:\beta\to\iota\) の個数 × \(\prod_i \lvert f^{-1}(i)\rvert!\) = \(\lvert\beta\rvert!\) | `card_sameFibers_mul`（mathlib の `DomMulAct.stabilizer_card` と `exists_perm_comp_eq`） |
| 型が等しい ⇔ プロファイル（固定点では塊の大きさ、他は 0）のファイバー数が等しい | `type_eq_iff`、`type_eq_iff_fin` |
| 置換による共役でプロファイルが移る | `conj_idempotent`、`profile_conj` |
| 同じプロファイルの冪等写像 ≃ 非固定点から固定点への写像（ファイバー数 \(m_a-1\)） | `profileEquiv` |
| **型別階乗公式** | `card_type_mul` |
| 7点：型 \((4,3)\) は 420 個、\((3,2,2)\) は 1,260 個 | `seven_points_43`、`seven_points_322` |

## 手書きの証明

冪等写像 \(K\) のプロファイル \(s_K(a)\) を、\(a\) が固定点なら塊 \(K^{-1}(a)\) の大きさ、そうでなければ 0 とする。型 \(\lambda\) の重複度 \(c_k\)（\(k\ge1\)）は \(\lvert s_K^{-1}(k)\rvert\) に等しく、\(\lvert s_K^{-1}(0)\rvert=N-r\)。したがって型 \(\lambda\) の冪等写像は、ファイバー数が \((N-r, c_1, c_2,\dots)\) のプロファイル \(s\) ごとに分かれる。そのような \(s\) は第1段により \(N!/((N-r)!\prod c_k!)\) 個あり、どれも置換の共役で \(s_{K_0}\) に移るので、各 \(s\) を持つ冪等写像の数は等しい。\(s_{K_0}\) を持つ冪等写像は、非固定点 \(N-r\) 個を固定点へ送る写像で各固定点 \(a\) への個数が \(m_a-1\) のものと一対一で、第1段によりその数は \((N-r)!/\prod(m_a-1)!\)。掛け合わせて公式を得る。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 Research/F0TypeCount.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。全定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
- `python -B tests/test_f0_type_count.py`：5テスト合格。\(N\le6\) の全冪等写像を型ごとに数えて公式と一致（総数 1, 3, 10, 41, 196, 1,057）、元資料の CSV `partition_counts_N01_to_N12.csv` の 271 行すべての `K_type` 列が公式と一致、多項係数の段を小さな定義域で総当たり確認。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 公式は型 \(\lambda\) を実現する冪等写像 \(K_0\) を一つ与えた形で述べている（与えられた整数分割から \(K_0\) を構成する宣言は含めない）。
2. 割り算の形ではなく、積が \(N!\) になる形で述べている。
