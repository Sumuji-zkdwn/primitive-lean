# 遅延硬化エーテル模型・第31回：2–3 Pachner移動で現れる曲率自由度と記憶緩和

日付：2026-11-23（JST）  
範囲：有限の**三次元空間断面**のRegge幾何。四次元重力の創発・二偏極の伝播・既存物理学の復元は未達。

## 目的と既存の結果との関係

第29回では、7本の局所距離を6成分の定数計量で表現しようとすると1つの整合条件が生じ、通常の6成分弾性波では余分なモードが消えないことを確認した。第30回では、既存の**四次元Regge作用を採用**した1–5単体パッチに、頂点移動に相当する4つの零モードがあることを調べた。しかし1–5パッチ自身は伝播する2偏極を持たない。

そこで今回は「新しい内部辺の長さ1本が、座標では消せない曲率の自由度を運ぶ最小の例」を、三次元の2–3 Pachner移動で厳密に調べる。これは4D canonical Regge calculusにおける2–3 moveの自由度計数と接続するが、今回の有限計算そのものは3D空間断面の幾何・1自由度の緩和模型に限る。先行研究: Philipp A. Höhn, *Canonical linearized Regge calculus: Counting lattice gravitons with Pachner moves*, Phys. Rev. D 91, 124034 (2015), https://doi.org/10.1103/PhysRevD.91.124034 。

## 1. 固定境界を持つ2–3単体組替え

頂点を A,B,C,D,E とする。最初は四面体 ABCD、ABCE が共通三角形 ABC を共有する。組替え後は ABDE、ACDE、BCDE の3つが新しい内部辺 DE を共有する。

- 前：四面体2個、辺9本、内部三角形ABC。
- 後：四面体3個、辺10本、内部三角形ADE,BDE,CDE、内部辺DE。
- 境界の6つの三角形と9本の境界辺は前後で完全に一致する。Python標準ライブラリの `Counter` と組合せ列挙で検査した。

境界辺の長さ9本をすべて1に固定し、新しい内部辺DEだけを \(x>0\) とする。各四面体は「5辺が1、残る一辺がx」の合同な四面体になる。\(s=x^2\) と置くと、頂点Dを原点として辺DE, DA, DBのGram行列は

\[
G=\begin{pmatrix}
 s&s/2&s/2\\s/2&1&1/2\\s/2&1/2&1
\end{pmatrix},\qquad
\det G=\frac{s(3-s)}4.
\]

第1,第2主小行列式は \(s\) と \(s(4-s)/4\)。したがって **\(0<s<3\)** が四面体の非退化・正定値Gram条件である。

辺DEに垂直な2つの辺ベクトルの角度から、二面角 \(\theta\) は

\[
\cos\theta=\frac{2-s}{4-s},\quad
\delta(x)=2\pi-3\arccos\frac{2-x^2}{4-x^2}.
\]

\(0<s<3\) で \(\delta(x)=0\iff \cos\theta=-1/2\iff s=8/3\)。さらに

\[
\frac{d\delta}{dx}=-\frac{6x}{(4-x^2)\sqrt{3-x^2}},\qquad
\left.\frac{d\delta}{dx}\right|_{x=\sqrt{8/3}}=-9\sqrt 2.
\]

正のxに対し角度欠損は狭義単調減少。曲率がゼロとなる内部辺は一意。\(s=1\) では \(\cos\theta=1/3\) で正の欠損、\(s=11/4\) では \(\cos\theta=-3/5\) で負の欠損。これらは**すべて同じ境界辺9本**を持つ。

この「1本の新しい内在的曲率座標」は一般の時空での独立した重力波と同一ではない。3D空間スライス上での単体組替えであり、Hamiltonian/運動量拘束、時間発展、二つのテンソル偏極を証明していない。

## 2. 元の「遅れて硬くなるゲル」との最小の結合

現在の曲率\(\delta(x)\)に内部の記憶\(m\)を結合する**新規に選んだ縮約力学**を試す：

\[
E(x,\dot x,m)=\frac{M}{2}\dot x^2+
\frac{\kappa}{2}(\delta(x)-m)^2+
\frac\mu2m^2,\quad M,\kappa,\mu>0.
\]

辺長に関する運動はラグランジュの変分から決め、記憶場だけは勾配緩和する：

\[
M\ddot x=-\kappa(\delta(x)-m)\delta'(x),\quad
\dot m=-\gamma[(\kappa+\mu)m-\kappa\delta(x)],\quad\gamma\ge0.
\]

したがって外部入力がないとき、**厳密に**

\[
\frac{dE}{dt}=-\gamma\left[\frac{\partial E}{\partial m}\right]^2\le0.
\]

この緩和は**追加した非共変な模型上の規則**であり、一般共変性・Einstein拘束・熱力学の完全なエントロピー方程式を満たすことは示していない。ここでの「硬化」は記憶とのずれによる復元力の模型化であり、実在のダイラタンシー流体の再現ではない。

平坦解 \((x,m)=(\sqrt{8/3},0)\) まわりでは \(d=\delta'=-9\sqrt2\)、二次エネルギーのHessianは

\[
H=\begin{pmatrix}\kappa d^2&-\kappa d\\-\kappa d&\kappa+\mu\end{pmatrix},\qquad
\det H=\kappa\mu d^2=162\kappa\mu>0.
\]

\(\kappa>0\) なのでHは正定値。**この一自由度の局所幾何模型は平坦状態に対して復元的**であり、安定な非零曲率の「粒子」を生んだわけではない。

## 3. 実行した検証と再現性

- `verify_v31.py` はPython標準ライブラリのみ。2–3移動の境界面一致、辺数、内部三角形、すべての有理数二面角値、差分恒等式、Gram行列の正値性、角度欠損の導関数を検査。
- \(M=1,\kappa=0.15,\mu=0.5,\gamma=2\)、初期 \(x=\sqrt{8/3}+0.035\)、速度と記憶は0、模型時間12のRK4を実行。刻み幅0.005/0.0025で比較。
- 0.005刻みの \(E(0)=0.020414277015128948\)、\(E(12)=0.0006849048200368747\)、散逸総量0.019729372205253948、エネルギー収支最大誤差 \(1.0782860\times10^{-10}\)。0.0025刻みでは最大誤差 \(6.2144\times10^{-12}\)。\(\gamma=0\) の対照条件では理論通り散逸が0。
- 別実装 `independent_audit_v31.py` はSymPyによるGram行列式、角度式、\(d=-9\sqrt2\)、記憶Hessianの行列式、エネルギー恒等式を直接検算し PASS。
- `curvature_scan_v31.csv` / `memory_dynamics_v31.csv` に全出力を保存。プロットは `make_plots_v31.py` で再生成可能。
- Lean `lean/Research/DelayedAetherPachner31.lean` は**辺集合の有限計数と有理数の二面角代数、記憶の二次形式**のみを形式化する。三角形の二面角の導出・曲率の微分・非線形時間発展はLean未証明。

## 4. 達成、追加仮定、未達

**達成（限定的）:** 固定境界を持つ3D Pachner 2–3組替えが、非零の角度欠損を作る内在的な距離自由度を1個導入する。平坦値\(x^2=8/3\)が唯一である。曲率を記憶する追加模型に対し、正値エネルギー・散逸恒等式・有限時間の数値安定性が成立する。

**借用・追加仮定:** Reggeの角度欠損の幾何学、内部辺の運動エネルギー、記憶の勾配緩和。これはまだ四次元時空のRegge作用そのものではない。

**未解決:** 4Dでの伝播する二重力波の数え上げ、非線形のゲージ拘束、記憶項を含む因果的・共変な作用、重力の普遍結合、元のゲルの法則からのEinstein–Hilbert項の必然的導出。

## 参考文献

- Höhn (2015), *Canonical linearized Regge calculus: Counting lattice gravitons with Pachner moves*, https://doi.org/10.1103/PhysRevD.91.124034
- Dittrich, Freidel & Speziale (2007), *Linearized dynamics from the 4-simplex Regge action*, https://doi.org/10.1103/PhysRevD.76.104020
- Bahr & Dittrich (2009), *(Broken) Gauge Symmetries and Constraints in Regge Calculus*, https://arxiv.org/abs/0905.1670
