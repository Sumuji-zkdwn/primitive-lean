# Laakso接合点からの多価観測遷移 — 観測商の交換可能性の具体模型

**日付:** 2026-11-15
**対象:** PR #142（PR #141にスタックしたドラフト）。main未統合。
**既存一次資料:** \`linear_input/lean_check/LaaksoFiniteGraph.inc\`、\`LaaksoNonlinearObstruction.inc\`、\`FutureObservations.inc\`、\`LaaksoGeometricProjection.inc\`、\`LaaksoGeometricTower.inc\`。
**追加証明:** \`linear_input/lean_check/LaaksoVoidRelationalBridge.inc\`。
**追加検算:** \`tests/test_laakso_void_relational_bridge.py\`。

## 0. 既存結果との重複を避ける

- \`LaaksoFiniteGraph.inc\` の \`RawVertex\`, \`RefinedVertex\`, \`rawProjection\`, \`refineSource\`, \`refineTarget\`、および新分点におけるsheet接合は **既に形式化済み**。
- \`LaaksoNonlinearObstruction.inc\` の \`pairMean_step_does_not_descend\`、\`witnesses_same_mean\`、\`witnesses_different_next_mean\` も **既に形式化済み**。
- PR #141の多価二項積および観測飽和の定理も別に存在する。
- このPRで追加するのは **任意の状態更新の最小関係的観測、合成時の過大近似・厳密性の一般条件、それらのLaakso具体例への接続**。新規性を文献全体に対して主張していない。

## 1. 決定的に降りない更新を、最小の多価写像として降ろす

観測 \(\pi:X\to Q\)、元の状態更新 \(U:X\to X\) を固定する。観測類 \(q\) から次に得られる観測集合を

\[
R_U(q)=\{\pi(Ux)\mid \pi(x)=q\}
\]

と定義する。これは常に存在する。任意の音響的（sound）な多価観測更新 \(F:Q\to\mathcal P(Q)\) が \(\pi(Ux)\in F(\pi(x))\) を満たすなら、必ず \(R_U(q)\subseteq F(q)\) となる。すなわち **最小の音響的（sound）な関係的模型** である。

\[
R_U(\pi(x))=\{\pi(Ux)\}\quad(\forall x)
\iff
[\pi(x)=\pi(y)\Rightarrow\pi(Ux)=\pi(Uy)].
\]

右辺は決定的な商更新の必要十分条件（従来のF0降下や観測合同の条件）。ここは既存理論の別表現。

観測ラベル集合 \(B\subseteq Q\) への拡張を

\[
R_U(B)=\{\pi(Ux)\mid \pi(x)\in B\}
\]

と書く。また、元の具体候補集合 \(A\subseteq X\) を直接更新した出力集合を
\(E_U(A)=\{\pi(Ux)\mid x\in A\}\)
とする。必ず \(E_U(A)\subseteq R_U(\pi(A))\)。

**全ての任意具体集合 \(A\) で等号が成立することは、決定的降下と同値。** 単元集合 \(A=\{x\}\) を許すと、同じ観測類の他の状態が異なる出力を持つ場合はすぐ反例になる。

## 2. 関係的更新と演算の交換

元の更新 \(U,V\) を連続実行するとき：

\[
R_{V\circ U}(B)\subseteq R_V(R_U(B)).
\]

常に成り立つ包含だが、一般に等号ではない。中間段階で観測類への丸めによって実際には到達できない内部状態が混入する。

等号の十分条件は **互いに異なる二つ** ある。

1. **後段 \(V\) が観測ファイバーに対して決定的に降りること。**
2. **前段 \(U\) が観測ファイバー全体を、観測ファイバーの和集合に写すこと。**

後者を \`FiberImageClosed π U\` と呼ぶ。任意の \(B\subseteq Q\) について

\[
U(\pi^{-1}B)=\pi^{-1}(R_U(B))
\]

という飽和性を要求する。これは **Uが決定的な商更新を持つこととは違う**。一つの入力観測類から複数の出力観測類が現れてもよいが、各出力類の内部状態が漏れなく得られる必要がある。

このとき \(R_{V\circ U}=R_V\circ R_U\) が **任意のV** に対して成立する。合成反復に関する特別な安定化条件を与える。


### 2.1 何にでも交換できるための必要十分条件

観測に少なくとも二つの異なる値 \(\pi(a)\ne\pi(b)\) があるなら、上の「前段のファイバー像が飽和している」という十分条件は、**任意の後段更新との交換**に対して必要条件にもなる：

\[
\boxed{
\operatorname{FiberImageClosed}(\pi,U)
\iff
\forall V,B,\quad R_V(R_U(B))=R_{V\circ U}(B).
}
\]

逆向きの証明は反証法。もし \(U(\pi^{-1}B)\) がある観測類の内部状態 \(x\) を取りこぼしたなら、更新 \(V\) を「\(x\) だけを \(\pi(a)\) に送り、それ以外を \(\pi(b)\) に送る」と選べる。丸め後には \(x\) が混入するので左辺に \(\pi(a)\) が現れ、具体状態から直接更新する右辺には現れない。これは等号に矛盾する。

実装名：\`fiberImageClosed_iff_all_continuations\`。後段を任意とすること、および少なくとも二つの観測値があることが本質的な仮定である。

### 2.2 全有限時刻の正確性

\(U\) が \`FiberImageClosed\` で、\(\pi\) が全射なら、最初の観測集合 \(B\) を入力とした関係的更新の \(n\) 回反復は、厳密な具体更新の \(n\) 回反復と一致する：

\[
R_U^{\,n}(B)
 =
 \{\pi(U^n x)\mid \pi(x)\in B\}\qquad(n\in\mathbb N).
\]

証明は直前の合成定理を帰納法で使う。Leanでは \`concreteIter\`、\`observedIter\`、\`observedIter_exact_of_fiberImageClosed\` で実装している。既存の \`Function.iterate\` と同じ左からの更新順序を、証明用に明示的に定義した。Laakso第一段の特殊化が \`first_all_times_exact\`。

ここでの正確性は「**初期に観測ラベルしか指定せず、そのラベルの全ファイバーを内部候補として採る**」場合である。特定の内部状態 \(x\) だけを指定した場合の全情報復元を主張しない。

## 3. Laakso第一段階の、厳密な8→6の接合

既存の \`RawVertex (Fin 2) (Fin 1)\` は **8状態**：

- 古い左/右頂点のそれぞれに2枚のsheet：4状態
- 新しい接合点 \(W_1,W_2\) それぞれに2枚のsheet：4状態

\`rawProjection\` で古い頂点のsheetは区別され、新しい二接合点だけ同一視されるため **6観測状態** になる。

\`advanceRight\` という明示的な離散更新を追加する。
- 古い頂点は固定する。
- \(W_1^{(b)}\to W_2^{(b)}\)（既存の平行中辺、ラベル付き）
- \(W_2^{(b)}\to R_b\)（既存の右側の辺）

source/targetとの一致は \`middle_edge_incidence\` と \`right_edge_incidence\` で、旧定義を直接使ってLean証明する。

観測可能な分割を未来まで伸ばすと：

| 観測時刻 | 区別可能な状態数 |
|---|---:|
| \(0\)（今だけ） | 6 |
| \(0,1\) | 7 |
| \(0,1,2\) | **8** |
| それ以上 | 8 |

\`w2_one_step_split\`、\`w1_two_step_split\`、\`depth_two_separates\` はLean検証対象。時刻1までは \(W_1^0\) と \(W_1^1\) が区別不能だが、時刻2でそれぞれ右端 \(R_0,R_1\) となる。現在の同一視のままでは決定的更新は無理（\`first_no_deterministic_quotient\`）。

一方、

\[
R_U(L_0)=\{L_0\},\quad R_U(L_1)=\{L_1\},\quad
R_U(R_b)=\{R_b\},\quad
R_U(W_1)=\{W_2\},\quad
R_U(W_2)=\{R_0,R_1\}.
\]

各元の観測類からの **具体到達状態の集合** は完全な観測ファイバーの合併である（\`first_fiber_images_closed\`）。

したがって **決定的には降りないが、多価遷移は任意の次の更新との合成に関して厳密**、という一般定理の実例になる。

ただし、具体状態を一つだけ指定した \(\{W_1^0\}\) からは、最初に観測類へ丸めると \(W_1^1\) まで混入する。任意の内部部分集合に対する厳密性を言っているわけではない。ここは **飽和初期集合 / 任意内部集合** を区別する。


### 3.1 各段の忘却区別数

一般の有限頂点型 \(V\)、辺型 \(E\) に対し、旧原稿にある raw/refined 頂点型をそのまま用いると

\[
|\operatorname{RawVertex}(V,E)|-
|\operatorname{RefinedVertex}(V,E)|=2|E|.
\]

Laakso既存定理 \`edge_card n : |E_n|=6^n\` から

\[
\boxed{\Delta_n=2\cdot6^n}
\]

が従う。これは第 \(n\to n+1\) 段で接合によって同一視される raw頂点の**個数差**であり、Shannonエントロピーや独立な情報ビット数を意味するものではない。

| 接合段 | raw→商で失われる状態個数 |
|---:|---:|
| 0→1 | 2 |
| 1→2 | 12 |
| 2→3 | 72 |
| 3→4 | 432 |

Lean名：\`raw_gluing_cardinality\`、\`gluing_gap_at_level\`。既存の \`edge_card\` を再利用した形式化で、幾何空間全体の情報次元についての結論ではない。

## 4. 非線形Laakso状態での第二実例

旧モジュールの六頂点場 \(F_\lambda\)、離散Euler更新 \(U_{\lambda,h}\)、端点平均 \(P\) を **再定義せず参照**する。旧証明の二状態 \`uniformWitness\`, \`splitWitness\` は

\[
P(x)=P(y)=(1/2,1/2),\qquad
P(U_{\lambda,h}x)\ne P(U_{\lambda,h}y)\quad(h\ne0)
\]

を満たす。従って \(R_{U_{\lambda,h}}((1/2,1/2))\) は少なくとも2元を含む（\`nonlinear_two_outputs\`）。さらに \`relSet_global_exact_iff\` によって、任意内部集合からの完全予測は不可能（\`nonlinear_no_global_exactness\`）。

この結果は、非線形更新の**正確な一価の平均縮約が不可能でも、関係的な更新を導入すること自体は常に可能**という主張にとどまる。将来の複数ステップを有限の観測類だけで正確に予測できるかは、この模型については未証明。

## 5. 幾何的逆系・ボイド幾何との境界

既存の \`LaaksoGeometricProjection.inc\` は各近似間の \`bond\` を連続全射として構成し、その非単射性も証明している。また \`LaaksoGeometricTower.inc\` はcompatible threadsと連続射影を構成している。

したがって各射影 \(p_n:X_{n+1}\to X_n\) でも、任意の選択した高解像度更新 \(U_{n+1}\) に対して上記の最小関係的更新

\[
R_{n,U}(q)=\{p_n(U_{n+1}(x))\mid p_n(x)=q\}
\]

は **集合論的に定義可能**。ただし、これだけでは「距離・測度を持つ連続Laakso空間上での流れ」とは言えない。必要な追加検証は、更新の連続性、射影の互換性、全段の隠れた状態の相関（compatible threads）であり、これらはこのPRでは未実証。

また「ボイド」という語に確立した数学的定義を与えたわけではない。これは **観測商と合成の失敗、および多価演算による修復** に対する具体的な候補表現である。

## 6. 検証

- Python: \`python -m unittest discover -s tests -p test_laakso_void_relational_bridge.py -v\`
- Lean: 専用ワークフロー \`.github/workflows/laakso-void-relational.yml\`。従来の三つの\`.inc\`を改変せず順序通り組み立て、\`lake env lean --trust=0\` で新モジュールを検査し主要宣言の\`#print axioms\`を取る。
- 検証状態はPRの最新ヘッドに対応するrunのみを数える。PRはドラフト、main自動マージ禁止。
