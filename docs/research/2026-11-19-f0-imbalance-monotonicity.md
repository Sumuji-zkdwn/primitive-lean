# F0 偏在単調性：二塊移動で Φ_d は厳密に増加する

## 位置づけ

F0 の会話資料 [03_conjecture_and_cautions.md](../../sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md) 第1節で**未証明予想**として保持され、本文第8.15節「分割型の合流チェイン」と ERG-Aout R005 の `cand.f0.imbalance_monotonicity`（formal binding では `unbound`）でも未解決として扱われていた命題を、一般に証明した。

- Lean：[lean/Research/F0ImbalanceMonotonicity.lean](../../lean/Research/F0ImbalanceMonotonicity.lean)（名前空間 `F0ImbalanceMonotonicity`、36定理・5定義）
- 独立検算：[tests/test_f0_imbalance_monotonicity.py](../../tests/test_f0_imbalance_monotonicity.py)（Python 標準ライブラリのみ）
- 専用CI：[.github/workflows/f0-imbalance-monotonicity.yml](../../.github/workflows/f0-imbalance-monotonicity.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

証明に使う道具（べき和の対数凸性、x^n の凸性による交換不等式）は古典的な初等不等式であり、新しい手法は主張しない。元資料の原文は変更していない。

## 定義

塊サイズ型を `F0MergeChains.inc` と同じく正整数の多重集合 \(p=\{m_1,\ldots,m_r\}\) で表す。

\[
P_p(e)=\sum_{j}m_j^{\,e},\qquad
\Phi_d(p)=\prod_{i}\bigl(P_p(m_i-1)\bigr)^d .
\]

`powerSum`、`phi` がこれに対応する。二塊移動 `Transfer p q` は

\[
p=\{a,b\}\cup T\ \longmapsto\ q=\{a+1,b-1\}\cup T,\qquad a\ge b\ge 2
\]

で、残り \(T\) には条件を課さない。総量・塊数・正値性は保たれる（`transfer_sum`、`transfer_card`、`transfer_pos`）。最も偏った型は `hook N r` \(=(N-r+1,1^{r-1})\)。

\(\Phi_d\) は元資料第5節の B 適合 S の個数である。Lean では `phi_map_univ` が、塊を有限型 \(\iota\) で添字付けた形 \(\prod_i(\sum_j m_j^{m_i-1})^d\) に一致することを示す。この右辺は [F0Retractions.inc](../../linear_input/lean_check/F0Retractions.inc) の `compatible_split_count`（\(\iota=\mathrm{Fix}\,K\)、\(m_a=|K^{-1}(a)|\)、\(d=|I|\)）の右辺と同じ式である。ただし両者は別の検査単位（独立モジュールと joint 検査）にあり、二つを合成した一つの Lean 定理は今回作っていない。

## 主定理と系

| 内容 | Lean 宣言 | 仮定 |
|---|---|---|
| 二塊移動で \(\Phi_d\) が厳密に増加 | `phi_lt_of_transfer`、`phi_lt_cons` | \(d\ge 1\)、\(a\ge b\ge 2\) |
| 移動を1回以上繰り返しても厳密に増加 | `phi_lt_of_transGen` | \(d\ge 1\) |
| 最も偏った型が一意な最大点 | `phi_lt_hook`、`phi_lt_hook_of_sum_card` | \(d\ge1\)、正整数、\(r\ge 1\)、\(p\ne\) hook |
| 最も偏った型が最大点（非狭義） | `phi_le_hook` | 正整数、\(r\ge 1\)（\(d\) は任意） |
| \(d=0\) では定数 | `phi_zero` | なし |
| 交換不等式 | `pow_exchange_le`、`pow_exchange_lt` | \(c\le a\)／\(c<a,\ n\ge2\) |
| べき和の対数凸性 | `powerSum_mul_le` | なし |
| 元資料の数値例 | `seven_two_chain`、`merge_can_increase`、`merge_chain_endpoints_decrease` | `decide` による有限計算 |

## 手書きの証明

\(X=\{a,b\}\cup T\)、\(X'=\{a+1,b-1\}\cup T\) とおく。\((a+1)-1=a\)、\((b-1)-1=b-2\) なので

\[
\Phi_1(X)=P_X(a-1)\,P_X(b-1)\prod_{t\in T}P_X(t-1),\qquad
\Phi_1(X')=P_{X'}(a)\,P_{X'}(b-2)\prod_{t\in T}P_{X'}(t-1).
\]

**(1) 交換不等式。** \(c\le a\) なら \(a^n+(c+1)^n\le(a+1)^n+c^n\)、さらに \(c<a,\ n\ge2\) なら狭義。\(c=b-1\) とすると、すべての指数 \(n\) で \(P_X(n)\le P_{X'}(n)\)、指数 \(n=a\ge2\) では \(P_X(a)<P_{X'}(a)\)。Lean では \(n\) についての帰納法で示した。

**(2) 対数凸性。** 任意の非負整数の多重集合と \(e,k\) について

\[
P(e+1)\,P(e+k)\le P(e)\,P(e+k+1).
\]

二点 \(x,y\) について \(x^{e+1}y^{e+k}+x^{e+k}y^{e+1}\le x^ey^{e+k+1}+x^{e+k+1}y^e\) を並べ替え不等式（`mul_add_mul_le_mul_add_mul`）で示し、多重集合についての帰納法で足し上げる。\(e=b-2\)、\(k=a-b+1\) とすると \(P_X(b-1)P_X(a-1)\le P_X(b-2)P_X(a)\)。

**(3) 結合。** \(P_{X'}\) はすべて正なので

\[
P_X(a-1)P_X(b-1)\le P_X(a)P_X(b-2)<P_{X'}(a)P_{X'}(b-2),
\]

残りの因子は (1) より \(\prod P_X(t-1)\le\prod P_{X'}(t-1)\)、右辺は正。よって \(\Phi_1(X)<\Phi_1(X')\)。最後に \(\Phi_d=\Phi_1^{\,d}\)（`phi_eq_base_pow`）と \(d\ge1\) で \(x\mapsto x^d\) が狭義単調であることを使う。

**系の証明。** hook でない正整数の型には \(2\) 以上の塊が二つあり（`exists_transfer_of_ne_hook`）、大きい方へ1を移せる。平方和 \(\sum m^2\) は移動ごとに真に増え、\((\sum m)^2\) で上から抑えられるので、測度 \(N^2-\sum m^2\) の強い帰納法で hook に到達し、途中の値は厳密に増える。

## 塊数を固定する条件の必要性

塊数が変わる二塊合流には単調性がない。元資料第3節の値を Lean の `decide` で確認した：\(\Phi_2(4,1,1,1)=18{,}386{,}944<\Phi_2(5,1,1)=31{,}843{,}449\)（合流で増加）だが、端点では \(\Phi_2(1^7)=678{,}223{,}072{,}849>\Phi_2(7)=13{,}841{,}287{,}201\)（全体では減少）。

## 手書きの帰結（Lean未形式化）

同じ \(N,r\) の正整数の型 \(x,y\) で \(x\) が \(y\) を真に majorize するなら、整数版の移動補題（Muirhead による。中間の型はすべて \(x\) と \(y\) の間にあり最小成分は \(\ge\min x\ge1\)）により \(y\) から \(x\) へ \(a\ge b\ge2\) の二塊移動の列で到達できるので、主定理から \(\Phi_d(x)>\Phi_d(y)\)（\(d\ge1\)）が従う。移動補題と majorization 順序は Lean では形式化していない。独立検算では \(N\le16\) の同じ塊数の全組 6,322 件で \(\Phi_1\) の大小が一致することだけを確かめた。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した。

- Lean `v4.36.0-rc2`（GitHub release のバイナリを elan に link）、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`（`lake exe cache get` で9,100ファイル取得）。
- `lake env lean --trust=0 -o … Research/F0ImbalanceMonotonicity.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。
- 全36定理の `#print axioms`：すべて `propext`・`Classical.choice`・`Quot.sound` の範囲内。`sorry`・`native_decide`・独自 `axiom` なし。
- `python -B tests/test_f0_imbalance_monotonicity.py`：10テスト合格。\(N\le20\) の全分割の二塊移動 6,750 件を \(d=1,2,3\) で確認、\(N\le16\) の各 \((N,r)\) で hook が一意な最大点、1〜5点上の冪等写像 251 個すべてで \(\Phi_1\) が \(SK=KS\) を満たす実際の写像 \(S\) の個数に一致、元資料の数値例、上記の majorization 数値確認。
- `python -B -X utf8 -m unittest discover -s tests`：351テスト合格。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 主張は二塊移動 \(a\ge b\ge2\) と、その繰り返しについてのもの。majorization で比較できない型どうしの大小は主張しない（一般に majorization は全順序ではない）。
2. 成分を正の実数へ広げた主張は含まない。定義は自然数上である。
3. \(d\ge1\) が必要。\(d=0\) では \(\Phi_0=1\)（`phi_zero`）。
4. 増加の幅は一様ではない。例えば \((c,6,6)\to(c,7,5)\) の \(\Phi_1\) の比は \(c=119\) で約 \(1.0000138\) で、\(c\) とともに1へ近づく（数値観察）。
5. B 適合 S の個数が多いことを、異なる T の個数・表現能力・計算効率と同一視しない（元資料第4節の注意を維持）。K・S・C の更新が型を二塊移動させるという実現定理も主張しない。

## ERG-Aout との対応

ERG-Aout の [R005 formal binding](https://github.com/Sumuji-zkdwn/ERG-Aout/blob/main/examples/r005/f0_chat.formal_binding.json) は `cand.f0.imbalance_monotonicity` を「未証明予想」として `unbound` に置いている。本モジュールが main に入った後は、そのコミットに固定して `phi_lt_of_transfer`（relation `proves`）を束縛できる。束縛の追加と accepted 層への昇格は ERG 側のレビュー手順に委ね、この記録では ERG-Aout を変更しない。
