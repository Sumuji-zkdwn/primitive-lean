# Laakso 有限グラフの区間実現と幾何的逆系

この追加段階では、既存の有限 Laakso 多重グラフの各辺を実数の閉区間として実現し、三分割を戻す連続全射を定義する。その実際の空間と写像を、既存の互換列による逆極限に代入する。各有限段のコンパクト性、互換列の存在、基底区間への連続全射を扱う。

[README.md](README.md) は、有限グラフ、非線形更新の反例、同期部分系、抽象的な逆系を導入した第一段階の説明である。そこで未導入としていた「辺の区間実現」と「実際の幾何的な bonding map」を、ここで追加する。第一段階の更新則がこの幾何的逆系と可換であるという新しい主張は含めない。

## 閉区間を端点で接合する

`LaaksoRealization.inc` の出発点は、頂点集合と各辺の閉区間の非交和である。

```text
Raw V E = V ⊕ (E × unitInterval)
unitInterval = {t : ℝ | 0 ≤ t ∧ t ≤ 1}
```

`normal G` は、辺 `e` の座標0を始点へ、座標1を終点へ送り、内部の点では辺IDと実数座標をそのまま保持する。`endpointSetoid G` はこの写像の核、`Realization G` はその商である。同じ頂点に接続する端点は一致する一方、異なる頂点、異なる辺の内部、辺の内部と頂点は区別される。ループや同じ端点を持つ平行辺についても、内部の辺IDは消さない。

位相は、生の非交和から誘導される**商位相**である。正規形の集合に非交和位相を直接入れるわけではない。この違いによって、辺の座標が0や1へ近づくことと頂点への接合が対応する。

`lift` は、頂点上の写像と各閉区間上の写像が端点で一致するとき、それらを商空間上の一つの写像へ降ろす。`continuous_lift` は、生の非交和上で連続なら降ろした写像も連続であることを与える。有限の頂点型・辺型の場合には `compact_realization` がコンパクト性を与える。

## 三分割を戻す連続全射

旧グラフを `G` とし、その辺の点を `[e,t]` と書く。既存の `refine G` は、旧頂点を二枚へ複製し、各辺を三分割し、新しい二つの分点だけを二枚の間で同一視する。`LaaksoGeometricProjection.inc` は、この同じ `refine G` の実現から `G` の実現へ写像を定義する。

\[
\begin{aligned}
\operatorname{bond}_G(v,b)&=v,\\
\operatorname{bond}_G(e,r)&=[e,(r+1)/3] &&(r=0,1),\\
\operatorname{bond}_G[(e,b,k),t]&=[e,(k+t)/3] &&(k=0,1,2).
\end{aligned}
\]

旧頂点では sheet `b` を忘れ、新しい分点は旧辺の内部へ送る。新分点を旧頂点集合だけへ送る写像ではない。例えば第一段の高さ `1/3` の分点に対応する点は、初期区間の内部にある。

`edgeImage_zero` と `edgeImage_one` は、この式が細分辺の端点で頂点像と一致することを証明する。従って `lift` により商の上の `bond` が定義できる。離散位相を持つ頂点型・辺型に対して `continuous_bond` が連続性を与え、`thirdParam_cover` と `bond_surjective` が閉区間全体を覆うことを与える。いずれも有限個の有理数標本ではなく、任意の実数座標についての命題である。

辺が一つでもあれば、`bond_not_injective` は二枚の相異なる辺内部の点を証人として非単射性を示す。平行辺の内部を保持する `edgePoint_interior_eq_iff` が、この証人の相異なることを保証する。

`thirdParam_difference` は、同じ細分辺内で正規化座標の差が `1/3` になることを示す。この定理自体は距離の定理ではない。標準構成の辺長の尺度 `3⁻ⁿ` を座標差に掛けると、

\[
3^{-(n+1)}|t-s|=3^{-n}\left|\frac{k+t}{3}-\frac{k+s}{3}\right|
\]

という代数式になる。独立した有限検査ではこの式を有理数で計算する。今回の Lean 原稿にはグラフの path metric を導入しておらず、この計算から大域的な距離保存や非拡大性を結論しない。

## 実際の空間を並べた逆系

`LaaksoGeometricTower.inc` は、第一段階の `level n` に今回の実現を適用する。

```text
Space n = Realization (level n)
bonding n : Space (n+1) → Space n
Tower = LinearInputInverseTowerObservation.Limit Space bonding
```

頂点と辺の添字型には、積・非交和による再帰定義と整合する離散位相を与える。`compact_space`、`continuous_bonding`、`bonding_surjective` は、それぞれ各有限段のコンパクト性、各段間写像の連続性、全射性を述べる。

`Tower` の点は、次の条件を満たす、実際の区間実現上の点の列である。

\[
x_n\in\mathrm{Space}(n),\qquad
\operatorname{bonding}_n(x_{n+1})=x_n.
\]

その位相は積空間の部分空間位相である。`project n` は第 `n` 座標への連続な射影であり、`project_compatible` が上の整合条件を表す。

全射性から選択公理を使って各点の逆像を一つ選び、`successor` として固定する。これを再帰的に適用した `threadFromBase x` は、任意の基底点 `x : Space 0` を第0座標に持つ互換列である。`project_zero_surjective` と `threadFromBase_injective` が、この右逆性と単射性を表す。**この選んだ持上げの連続性は主張しない。** 全射から任意に選ぶ操作と、連続な section の構成は別の証明義務である。

初期の一辺の実現から閉区間へ戻す `baseCoordinate` と、逆向きの `basePoint` は互いに逆である。`baseCoordinate_basePoint` と `basePoint_baseCoordinate` が両方向の恒等式を与え、両写像の連続性を合わせた `baseHomeomorph : Space 0 ≃ₜ unitInterval` は、第0段の実現が閉区間と同相であることを表す。

この `baseCoordinate` を第0射影と合成したものを `evaluation : Tower → unitInterval` とする。`evaluation` は連続かつ全射である。逆向きには、各 `u : unitInterval` の基底点から選んだ互換列 `intervalThread u` があり、

```text
evaluation (intervalThread u) = u
```

が成り立つ。従って `intervalThread` は単射であり、`0` と `1` からの互換列は相異なる。ただし `intervalThread` の連続性、位相的埋込みであること、区間と逆極限の同相は主張しない。

`heightAt n` は、`Space n` から実際の bonding map を繰り返して基底区間の座標を読む連続関数として定義する。互換列上では

```text
heightAt n (project n x) = evaluation x
```

が全ての自然数段 `n` について成り立つ。ここでは高さを bonding map による引戻しとして定義している。独立に定義した全段の頂点高さ・辺補間式と一致するという追加の一般定理を、この式に含めない。

## 命題と原稿の対応

| 内容 | 原稿 | 主な宣言 |
|---|---|---|
| 閉区間端点の接合、内部の辺IDの保持 | [LaaksoRealization.inc](../../linear_input/lean_check/LaaksoRealization.inc) | `endpointSetoid`, `edgePoint_zero`, `edgePoint_one`, `edgePoint_interior_eq_iff`, `edgePoint_interior_ne_vertex` |
| 接合と整合する写像の降下・連続性 | 同上 | `rawLift_respects`, `lift`, `lift_unique`, `continuous_lift` |
| 有限グラフの実現のコンパクト性 | 同上 | `compact_realization` |
| 三分割の実数座標式と端点整合 | [LaaksoGeometricProjection.inc](../../linear_input/lean_check/LaaksoGeometricProjection.inc) | `thirdParam`, `newParam`, `edgeImage_zero`, `edgeImage_one`, `bond_edgePoint` |
| 幾何的射影の連続・全射・非単射 | 同上 | `continuous_bond`, `bond_surjective`, `bond_not_injective` |
| 正規化された辺座標の差 | 同上 | `thirdParam_difference` |
| 実際の有限段と bonding map | [LaaksoGeometricTower.inc](../../linear_input/lean_check/LaaksoGeometricTower.inc) | `Space`, `compact_space`, `bonding`, `continuous_bonding`, `bonding_surjective` |
| 実際の幾何的互換列と連続な座標射影 | 同上 | `Tower`, `project_compatible`, `continuous_project` |
| 基底点ごとの互換列の存在 | 同上 | `threadFromBase`, `project_zero_surjective`, `threadFromBase_injective` |
| 第0段の実現と閉区間の同相 | 同上 | `baseCoordinate_basePoint`, `basePoint_baseCoordinate`, `baseHomeomorph` |
| 基底区間への連続全射と選んだ単射 | 同上 | `continuous_evaluation`, `evaluation_surjective`, `evaluation_intervalThread`, `intervalThread_injective`, `interval_threads_zero_one_distinct` |
| 全段で整合する引戻し高さ | 同上 | `continuous_heightAt`, `heightAt_project` |

追加した三原稿の宣言数は、実現が25宣言・16定理、射影が23宣言・18定理、逆系が41宣言・22定理で、合計89宣言・56定理である。ビルド結果、公理監査、全体の宣言数、検証対象ソースのハッシュは[検証記録](../verification/2026-11-14-laakso-geometric.md)で扱う。

## 独立した有限有理数検査

[check_laakso_geometric.py](../../tools/check_laakso_geometric.py) は、既存の `check_laakso_finite.refine` で頂点高さとラベル付き辺を構成し、端点正規形、射影、標本の逆像を Python の `Fraction` で計算する。辺の座標0と1だけを頂点へ正規化し、平行辺の内部を端点対でまとめない。

対象は `n=0,1,2,3` に対する `G_(n+1) → G_n` である。端点、新しい thirds、有理数の内部点を含む標本について、次の検査を行う。

| 検査 | 件数 |
|---|---:|
| 細分辺の端点と頂点像の整合 | 3,108 |
| 細分頂点の高さ保存 | 822 |
| 細分辺の標本点の高さ保存 | 10,878 |
| 辺長を掛けた座標差の式 | 32,634 |
| 相異なる全射検査対象点 | 2,224 |
| 同像を持つ相異なる sheet の点対 | 259 |

各標本の逆像候補も列挙し、新しい thirds では一点、それ以外では二点になることを検査する。third offset を忘れた写像は4段階で、平行辺を早期にまとめる処理は平行辺が存在する3段階で不正と検出する。合計7件の変異検出を記録する。

この検査は有限の厳密有理数計算である。実数全体での全射性や連続性は上記 Lean 定理が扱う。標本の fiber の個数や、辺長を掛けた座標差の計算を、無限空間の距離・測度に関する定理へ読み替えない。

## 再現と証拠

共通の検証入口は引き続き `tools/verify.py` である。

```console
python -B -X utf8 tools/verify.py --proof-only
python -B -X utf8 tools/verify.py --integration-only
```

幾何部分の独立有限検査だけを再実行するには、次を使う。

```console
python -B -X utf8 tools/check_laakso_geometric.py
```

結果は `verification/laakso-geometric.json` に保存され、検査スクリプトと共有グラフ builder の SHA-256 を含む。統合結果、公理監査、使用環境、キャッシュやビルドの条件は[幾何段階の検証記録](../verification/2026-11-14-laakso-geometric.md)を参照する。出典と追加ソースの対応は [provenance-geometric.json](provenance-geometric.json)、第一段階の保存原本の情報は [provenance.json](provenance.json) に記録する。

## 一次資料とこの段階の境界

Kauffman らの [Quantum Mechanics on Laakso Spaces, §2.1](https://arxiv.org/html/1011.3567v2) は、各辺を等分して複製し、新しい対応分点だけを同一視する有限近似を説明する。今回の一定三分割と幾何的射影は、この構成および Research から保存した [laakso.py](../../sources/laakso/laakso.py) の内部点への射影を参照している。Lean での接続先は、既に導入したラベル付き有限グラフ `refine` と `level` である。

Cheeger–Kleiner の [Inverse limit spaces satisfying a Poincaré inequality](https://arxiv.org/html/1312.5227v1) では、Definition 2.10 の admissible system に距離、fiber の定量的制御、測度の pushforward と頂点での整合などを要求する。その仮定の下で Theorem 1.1 の Poincaré 不等式や Proposition 2.17 の measured Gromov–Hausdorff 収束へ進む。§8.2 と Lemma 8.4 の辺置換構成は将来の接続候補であるが、その仮定全体を今回満たしたとは主張しない。

今回の範囲は、区間実現、連続全射、各有限段のコンパクト性、第0段と閉区間の同相、実際の互換列、基底区間への連続全射である。任意段や逆極限に関する一般の Hausdorff 性・道連結性、逆極限全体のコンパクト性、path metric、極限距離、測度、Hausdorff 次元、Ahlfors 正則性、Poincaré 不等式、Dirichlet 形式は追加の証明義務として残す。
