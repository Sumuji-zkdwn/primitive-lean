# F0：条件 B を外したときに区別が復活する場合の完全な分類と個数

## 位置づけ

F0 の会話資料 [03_conjecture_and_cautions.md](../../sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md) 第5節は、「B を外すと区別不能性が壊れる」を「壊れる例が存在する」という意味に限定し、`r=1` や `K` が単射の場合には区別が起こらないと注意していた。ERG-Aout R005 ではこの注意が `cand.f0.drop_b_not_always` として未束縛のまま残り、[R005 handoff](../integration/erg-r005-handoff.md) は「条件 B の不成立が必ずしも区別を復活させないことを形式化する。条件 A の反例で代用しない」と求めていた。

この追加は、その注意を**必要十分条件**として証明し、有限の場合は該当する写像の個数も与える。

- Lean：[lean/Research/F0DropCompatibility.lean](../../lean/Research/F0DropCompatibility.lean)（名前空間 `F0DropCompatibility`、29定理・17定義）
- 独立検算：[tests/test_f0_drop_compatibility.py](../../tests/test_f0_drop_compatibility.py)
- 専用CI：[.github/workflows/f0-drop-compatibility.yml](../../.github/workflows/f0-drop-compatibility.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

条件 A（`C∘S=id`）はこの追加では一切使わない。

## 定義

冪等 \(K:\mathcal B\to\mathcal B\)、出力成分の添字型 \(I\)（\(d=|I|\)）、\(S:\mathcal B\to\mathcal B^I\) について、[F0Retractions.inc](../../linear_input/lean_check/F0Retractions.inc) と同じ本文で

- `liftK K v = fun i => K (v i)`（\(K^{(d)}\)）
- `Compatible K S`：\(\forall x\,i,\ S(Kx)_i=K(S(x)_i)\)（条件 B）

を置く。新しく

- `Respects K S`：\(Kx=Ky\Rightarrow K^{(d)}S(x)=K^{(d)}S(y)\)（K が潰した区別を復活させない）
- `Separates K S`：その否定（\(Kx=Ky\) なのに \(K^{(d)}S(x)\ne K^{(d)}S(y)\) となる \(x,y\) がある）

を定義する。定義はこのモジュールに写して持ち、joint 検査の宣言との同一視は Lean では行っていない。

## 結果

| 内容 | Lean 宣言 | 仮定 |
|---|---|---|
| B ⇒ 区別不能（既知の方向） | `compatible_respects` | なし |
| 区別不能 ⇔ \(K^{(d)}\circ S\) が \(K\) を通る | `respects_iff_factor` | 冪等 |
| B を破る \(S\) がある ⇔ \(K\ne\mathrm{id}\) | `exists_incompatible_iff` | 冪等、\(I\) 非空 |
| B を破るのに区別しない \(S\) がある ⇔ \(K\ne\mathrm{id}\) | `exists_incompatible_respecting_iff` | 冪等、\(I\) 非空 |
| 区別する \(S\) がある ⇔ \(K\) 非単射 かつ 固定点 ≥ 2 | `exists_separating_iff` | 冪等、\(I\) 非空 |
| 「B の不成立 ⇒ 区別の復活」は B が破れうるどの \(K\) でも偽 | `drop_b_not_always` | 冪等、\(I\) 非空 |
| 単射なら \(K=\mathrm{id}\)、どの \(S\) も B を満たし区別しない | `eq_id_of_injective`、`compatible_of_injective`、`respects_of_injective` | 冪等 |
| 固定点が高々1個なら区別しない | `respects_of_fixed_subsingleton` | 冪等 |
| 区別しない \(S\) の個数 \(\prod_a(\sum_b m_b^{m_a})^d\) | `respects_count` | 有限、冪等 |
| B を満たす \(S\) の個数 \(\prod_a(\sum_b m_b^{m_a-1})^d\) | `compatible_count` | 有限、冪等 |
| B を破るが区別しない \(S\) の個数はその差 | `incompatible_respecting_count_eq` | 有限、冪等 |
| その個数が正 ⇔ \(K\ne\mathrm{id}\) | `incompatible_respecting_count_pos_iff` | 有限、冪等、\(I\) 非空 |

ここで \(m_a=|K^{-1}(a)|\)（\(a\in\mathrm{Fix}\,K\)）。`compatible_count` は `F0Retractions.inc` の `compatible_split_count` と同じ式を、このモジュール内で独立に示したものである。

会話資料の例 \(\mathcal B=\{0,1,2\}\)、\(K=(0,0,2)\) では、資料の \(S=(0,2,0)\) が B を破って区別を復活させる一方、同じ \(K\) で \(S=(1,1,2)\) は B を破るが区別しない（`example_separating`、`example_respecting`）。一塊の \(K=(0,0,0)\) ではどの \(S\) も区別しない（`constK_never_separates`）。

## 手書きの証明

**区別不能の特徴づけ。** 冪等性より \(Kx=K(Kx)\) なので、`Respects` は \(K^{(d)}S(Kx)=K^{(d)}S(x)\) と同値。

**B を破るが区別しない構成。** \(Kx_0\ne x_0\) となる \(x_0\) を一つ取り、
\(S(y)_i=x_0\)（\(Ky=Kx_0\) のとき）、\(S(y)_i=y\)（それ以外）とおく。どちらの場合も \(K(S(y)_i)=Ky\) なので区別しない。一方 \(S(Kx_0)_i=x_0\ne Kx_0=K(S(x_0)_i)\) なので B を破る。\(K=\mathrm{id}\) なら B は自明に成り立つので、これで分類1・2が従う。

**区別する構成。** \(K\) が非単射なら \(x\ne y\)、\(Kx=Ky\) が取れ、固定点 \(a\ne b\) があれば \(S(z)_i=a\)（\(z=x\)）、\(b\)（それ以外）が \(x,y\) を区別する。逆に区別が起これば \(K(S(x)_i)\ne K(S(y)_i)\) は二つの異なる固定点で、\(x\ne y\) なので \(K\) は非単射。

**個数。** 一成分の区別しない写像 \(s\) は、固定点の写像 \(g:\mathrm{Fix}\,K\to\mathrm{Fix}\,K\)（\(g(a)=K(s(a))\)）と、各点 \(x\) の行き先を塊 \(K^{-1}(g(Kx))\) から選ぶことの組に一対一に対応する（`respectSigma`）。よって個数は \(\sum_g\prod_a m_{g(a)}^{m_a}=\prod_a\sum_b m_b^{m_a}\)。B を満たす写像では代表点 \(a\) の行き先が \(g(a)\) に固定されるので、指数が \(m_a-1\) になる（`compatSigma`）。B を満たせば区別しないので、差がちょうど「B を破るが区別しない」写像の個数になる。成分ごとに独立なので \(d\) 乗する。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 -o … Research/F0DropCompatibility.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。
- 全29定理の `#print axioms`：20定理が `propext`・`Classical.choice`・`Quot.sound`、2定理が `Quot.sound` のみ、2定理が `propext` のみ、5定理は公理に依存しない。`sorry`・`native_decide`・独自 `axiom` なし。
- `python -B tests/test_f0_drop_compatibility.py`：5テスト合格。1〜4点上の冪等写像 55 個（1, 3, 10, 41）と全ての一成分 \(S\)、1〜3点上の冪等写像 14 個と全ての二成分 \(S\) で、三つの分類と二つの個数公式を総当たりで確認。会話資料の例も確認。

GitHub Actions：専用CI [run 44499910701](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44499910701)（コミット `7c4aa8d`、push イベント）が成功（conclusion `success`）。

## 論理的境界

1. 「区別」は \(K^{(d)}\circ S\) による区別に限る。生の \(S\) の出力が異なることは区別に数えない（元資料第4節の限定を維持）。
2. 更新 \(T=K\circ C\circ K^{(d)}\circ S\) 全体の区別や、条件 A の有無による違いはこの追加の対象外。
3. 個数公式は有限集合についてのもの。無限の場合は存在・非存在の分類だけを主張する。
4. B を破る写像が多いこと・区別する写像が存在することを、表現能力や学習性能と同一視しない。

## ERG-Aout との対応

`cand.f0.drop_b_not_always` は、本モジュールの `drop_b_not_always`（および必要十分条件 `exists_incompatible_respecting_iff`）に relation `proves` で束縛できる候補である。束縛は main への統合後のコミットに固定して ERG 側のレビューで行い、この記録では ERG-Aout を変更しない。
