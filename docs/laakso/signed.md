# 第一近似の接続反転・到達可能性・Eの整合費用

Research の符号付き接続を、既に構成した Laakso 第一近似の六頂点六辺へ載せる。基底の辺 ID を保持し、中央の二本の平行辺のうち一本だけを反転する。同じ例で、閉路を回った際の層の反転、二重被覆での到達可能性、二成分エネルギーの整合費用を比較する。

これは [Research 原文の保存コピー](../../sources/laakso/signed/SIGNED_CONNECTIONS.md) 第2–4節を、特定のグラフと係数について実装した追補である。[出典の読み分け](signed-source-notes.md)、[ソース台帳](provenance-signed.json)、[検証記録](../verification/2026-11-14-laakso-signed.md)を併記する。

## 1. 対象と変更するもの

頂点は `0=L0, 1=L1, 2=R0, 3=R1, 4=W1, 5=W2`。辺の始点と終点は、既存の `LinearInputLaaksoFiniteGraph.firstSource` と `firstTarget` をそのまま使う。

| 辺 ID | 始点→終点 | 全辺正の接続 | 一本反転した接続 |
|---|---|---|---|
| 0 | L0→W1 | + | + |
| 1 | L1→W1 | + | + |
| 2 | W1→W2 | + | + |
| 3 | W1→W2 | + | − |
| 4 | W2→R0 | + | + |
| 5 | W2→R1 | + | + |

`firstGraph` は単なる似た図ではなく、一般の細分構成の第一段と頂点・辺の同型で結ばれている。ここでの反転は接続データだけを変更する。基底の頂点や辺は取り除かない。

二重被覆の頂点は `(v,b) : Fin 6 × Bool`、辺は `(e,b) : Fin 6 × Bool` で、始点 `(source e,b)` から終点 `(target e,b XOR τ e)` を結ぶ。これは辺による接続であり、頂点の同一視ではない。基底の細分で二枚の分点を接合する既存の商とも、別の操作である。

## 2. 閉路と到達可能性

中央の辺2を進み辺3を戻る閉路の偶奇は `τ 2 XOR τ 3`。全辺正では偽、一本反転後では真になる。全辺正の場合、被覆上の二点が到達可能であることと層番号が同じであることが一致する。反転後はすべての被覆頂点の間を移動できる。

| 固定した第一近似での比較 | 全辺正 | 辺3だけ負 |
|---|---:|---:|
| 基底の頂点数・辺数 | 6・6 | 6・6 |
| 二重被覆の頂点数・辺数 | 12・12 | 12・12 |
| 二重被覆の連結成分 | 2 | 1 |
| 一つの被覆頂点からの到達数 | 6 | 12 |
| 全辺と整合する二値ラベル | 存在 | 不存在 |

二値ラベルの不存在は、中央の二辺が同じ頂点対に同時に一致と反転を要求することから生じる。空間や任意の実数状態が存在しないという主張ではない。

## 3. 既存のEとの接続

状態は各頂点に置いた `qᵢ=(xᵢ,yᵢ)∈ℝ²`。Research の共通係数を `λ=κ=1`、外部入力を `u=0` と固定し、局所費用を

\[
P(x,y)=\frac14(x^2-1)^2+\frac12(y-\sqrt2x)^2
=\operatorname{LinearInputDesign.E}(1,-1,0,x,y)+\frac14
\]

と定める。総費用は

\[
\mathcal F_\tau(q)=\sum_{i=0}^{5}P(q_i)
+\frac12\sum_{e=0}^{5}\|q_{s(e)}-\sigma_e q_{t(e)}\|^2,
\qquad \sigma_e=(-1)^{\tau_e}.
\]

各ラベル付き無向辺を一回ずつ数える。二本の中央辺は二つの項として残る。この同一性を既存の `E` の定義から証明することで、名前だけでなくエネルギー式を接続する。以前の有限非線形反例で選んだスカラー反応式と、この二成分模型を同じものとは扱わない。

全辺正の接続では全頂点を `q*=(1,√2)` に置くと総費用は零になる。一本反転後には、任意の実数状態について

\[
\mathcal F_{\mathrm{flip}}(q)\ge\frac12
\]

が成り立つ。下限の要点は、中央二頂点の x 座標を `a,b` とすると

\[
\frac14(a^2-1)^2+\frac14(b^2-1)^2
+\frac12(a-b)^2+\frac12(a+b)^2
=\frac12+\frac14a^4+\frac14b^4+\frac12a^2+\frac12b^2
\ge\frac12
\]

となり、残りの局所費用・辺費用・y 座標の寄与も非負であることである。`1/2` を最小値と断定せず、最小値の達成も主張しない。固定したこのグラフと係数の全状態に通用する下限であり、全グラフ・全係数に共通の定数ではない。

固定した状態で接続だけを反転する費用差は

\[
\mathcal F_{\mathrm{flip}}(q)-\mathcal F_{\mathrm{positive}}(q)
=2\,q_4\cdot q_5.
\]

したがって個々の状態での費用差は正にも負にもなる。零費用の実現可能性が失われることと、各状態で必ず費用が増えることは別である。

## 4. 証拠と区切り

| 本文の内容 | Lean の宣言 |
|---|---|
| 実際の第一近似の二重被覆 | `LinearInputLaaksoSigned.liftGraph`（既存 `firstSource` / `firstTarget` を使用） |
| 一本だけを反転 | `flipped_only_middle` |
| 同層内だけの到達、反転後の全到達 | `untwisted_reach_iff`, `flipped_fully_connected` |
| 任意の始点からの到達数6と12 | `untwisted_reachable_card`, `flipped_reachable_card` |
| 中央閉路の偶奇 | `untwisted_middle_parity`, `flipped_middle_parity` |
| 二値ラベルの可解性・障害 | `untwisted_has_spin`, `flipped_no_spin` |
| 既存のEとの式の一致 | `LinearInputLaaksoSignedEnergy.localPotential_eq_design_energy` |
| 非負性と全辺正の零費用状態 | `energy_nonneg`, `energy_untwisted_constantWell` |
| 反転後の全状態下限 | `middle_energy_decomposition`, `energy_flipped_lower_bound` |
| 固定状態での差、正負の両例 | `flip_energy_jump`, `flip_can_increase_energy`, `flip_can_decrease_energy` |

接続の宣言は [LaaksoSignedConnection.inc](../../linear_input/lean_check/LaaksoSignedConnection.inc)、費用の宣言は [LaaksoSignedEnergy.inc](../../linear_input/lean_check/LaaksoSignedEnergy.inc) にある。

Lean は有限標本に限定せず、定義された到達関係と任意の実数状態についての命題を検査する。独立の標準ライブラリ Python 検査は、全64個の辺符号、二値ラベル、被覆の幅優先探索、x,z を有理数とする座標 q=(x,√2 z) での費用恒等式を調べる。グラフ生成は既存 builder を共有し、被覆探索・spin 判定・費用係数検査は Lean から独立に実装する。後者は実数全体の形式証明の代用ではない。

今回の区切りは、同じ第一近似上で、局所的な一辺変更と到達可能性・整合費用の変化を結ぶところに置く。無限極限への接続の伝播、一般の符号付きグラフの分類、ゲージ変換の一般定理、勾配流、距離・測度・Hausdorff次元・Poincaré不等式は今回の追加定理に含まれない。マクロ語の拡大やホモロジーでの穴の充填とも同一視しない。
