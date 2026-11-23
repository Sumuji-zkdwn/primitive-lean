# 遅延硬化エーテル模型・第27回数理検証

**題目：空間依存する非最小記憶–曲率結合の拘束代数（1D非一様な3+1縮約）**  
実施：2026年11月23日／プログラム：`verify_v27.py`・`independent_audit_v27.py`。

## 要旨と限定

第26回のスカラー–テンソル模型を、時間だけでなく一つの空間座標 x に依存する3+1次元の平面対称・対角計量部分系へ拡張し、**全5組の正準変数**による `H-H` ポアソン括弧を直接微分した。空間依存する `F(χ)`、その微分 `D_iD^iF`、記憶・状態の場空間計量 `A(q-χ)`、計量–スカラー正準運動量の混合を同時に保持。

- 正しいLegendre変換を用いると、拘束代数の残差は有限差分の格子幅の二乗で減少する。
- `pχ-(Fχ/F)π` という正準混合を省いた同じハミルトニアンでは、残差が非零定数に近づく。
- 共形変換後のEinstein frameのHamiltonianとの等価性を、全微分項込みでSymPyの**厳密恒等式**として確認。
- 二次微分を使う曲率式の直接積分、1階微分への部分積分、完全に別のNumPy有限差分によるPoisson bracketを独立監査。

**重力創発の成果ではない。** 出発点は既存の一般共変なEinstein–Hilbert＋非最小結合の作用であり、局所的なゲルの更新則からこの作用が出現した証明ではない。`χ` は可逆的な動的内部場であり、不可逆な粘弾性記憶ではない。`q` は単一実スカラーで、Skyrme型の位相電荷を持たない。

## 1. 作用

符号 `(-,+,+,+)`、`F=2+0.35tanhχ>1.65`、`A=1+1.8 tanh²((q−χ)/0.5)≥1`、`V=(q−χ)²/2+0.07χ²`。

\[
S=\int d^4x\sqrt{-g}\Big[\tfrac12F(\chi)R
-\tfrac12(\nabla\chi)^2-\tfrac12 A(q-\chi)(\nabla q)^2-V(q,\chi)\Big]+S_{\partial M}.
\]

3次元計量を `diag(exp(2α),exp(2β),exp(2γ))`、各場を `x` の関数とする。5組の正準座標・運動量は

\[
Q=(\alpha,\beta,\gamma,\chi,q),\qquad P=(P_\alpha,P_\beta,P_\gamma,p_\chi,p_q),
\]

`Pα=2γxxπxx`、同様に `Pβ,Pγ`。`J=e^{α+β+γ}`, `W=e^{β+γ−α}`, `\Pi=(Pα+Pβ+Pγ)/2`, `D=1+3Fχ²/(2F)` とする。ラプスを `N(x)`、シフトを0に設定する。拘束の検査には任意の二つのラプス `N,M` を使う。

**運動部分**

\[
\mathcal H_K=\frac{\sum_i P_i^2-\frac12(\sum_iP_i)^2}{2FJ}
+\frac{[p_\chi-(F_\chi/F)\Pi]^2}{2JD}
+\frac{p_q^2}{2JA}.
\]

**空間部分**。`β_x=∂xβ`、`F_x=Fχ χ_x` と記す。周期境界で部分積分したsmearingつきの表現は

\[
\begin{aligned}
H[N]=\int dx\,\Big\{&N\big[\mathcal H_K
-W\big(F\beta_x\gamma_x+F_x(\beta_x+\gamma_x)\big)
+\tfrac W2(\chi_x^2+A q_x^2)+JV\big]\\
&-N_x W\big[F(\beta_x+\gamma_x)+F_x\big]\Big\}.
\end{aligned}
\]

`N_x`項の中に空間依存するラプスと `F` の微分を保存している。これを落とすと拘束代数が変わる可能性がある。直接の未積分形は `√γ[-F R^(3)/2 + ΔF + 1/2|∇χ|²+A/2|∇q|²+V]`。

空間変形の拘束は

\[
\mathcal D_x=\sum_i P_i\partial_x\sigma_i+p_\chi\chi_x+p_q q_x-\partial_xP_\alpha,\quad (\sigma_i=\alpha,\beta,\gamma).
\]

目標となる連続模型のoff-shell拘束関係は

\[
\boxed{\{H[N],H[M]\}=D[e^{-2\alpha}(NM_x-MN_x)]}.
\]

## 2. 厳密な共形変換の検査

`γ̃ij=Fγij`、`Ñ=√F N`、`P̃α=Pα`（残りも同じ）、`p̃χ=pχ-(Fχ/F)Π`。空間の正準1形式は

\[
\sum_i P_i\,d\sigma_i+p_\chi\,d\chi
=\sum_i\widetilde P_i\,d\widetilde\sigma_i+\widetilde p_\chi\,d\chi.
\]

Einstein frameのスカラー場空間計量は `G̃χχ=D/F`、`G̃qq=A/F`、ポテンシャルは `Ṽ=V/F²`。`F_x`を明示的に展開すると、Einstein frameの重力曲率項に出てくる `−3F_x²/(4F)` が、スカラー運動項に出てくる `+3F_x²/(4F)` と打ち消され、**smearingの微分項を含めて** `H_J[N]=H_E[√F N]` が成立する。SymPyで式の差を完全に0へ簡約。

また `D_J=D_E`。標準Einstein-frame ADM拘束の括弧を利用すると、`γ̃xx^{-1}=γxx^{-1}/F` および `Ñ M̃_x−M̃ Ñ_x=F(NM_x−MN_x)` より目標の拘束関係が従う。`√F`という場依存のsmearingからの余剰項は、同じ位置で `NM−MN=0` に比例して相殺される。この論証は**Einstein frame ADM拘束の既知の成立を使う**ので独立の創発定理ではない。

注意：空間計量とスカラーの正準対の変換はここで扱った位相空間についてのものであり、ラプスとシフトの正準運動量まで含む拡張位相空間で同じ変換が無条件に正準的とは主張しない。

## 3. 数値結果

周期空間 `x∈[0,2π)`、5組の滑らかな非一様な初期データ、ラプス二組、中心差分。偏微分はJAX自動微分で全5組の正準変数に対して行い、格子HamiltonianのPoisson bracketを直接評価。標準運動量拘束側も同じ中心差分で評価。

| 分割数 | 正しい混合の残差 | 混合省略の残差 | Einstein frameとJordan frameのH差 |
|---:|---:|---:|---:|
| 64 | −2.96761e−3 | −7.706e−2 | 1.1377e−4 |
| 128 | −7.58343e−4 | −7.597e−2 | 2.891e−5 |
| 256 | −1.90628e−4 | −7.569e−2 | 7.256e−6 |

正しい混合での残差は128→256で約3.98分の1。別の三つの空間依存状態でも、正しい模型の残差は二次収束（256分割で `6.58e−5`, `8.17e−5`, `−2.69e−4`）、省略模型には約 `0.0292`, `0.0528`, `−0.0835` の有限残差。

`R^(3)`, `ΔF` を二次微分から直接計算した空間作用と、部分積分後の空間作用も独立に比較し、差は32・64・128・256分割で `−3.966e−4`, `−9.874e−5`, `−2.465e−5`, `−6.160e−6`。明確な二次収束。これにより `D_iD^iF` の寄与を落とさず取り扱っていることも点検できる。

NumPy独立実装では12分割の全5組に二側有限差分を適用し、JAX自動微分で計算した括弧と、それぞれ絶対差 `1.47e−10`、`3.07e−10` で一致した（正しい模型・混合省略模型）。

なお、この有限格子の括弧は**厳密には閉じない**。中心差分の積の微分法則が厳密に成立しないためであり、精密化に伴う連続拘束への収束を示した。

## 4. 成功・反例・残る問題

**確認済み**： (i) 非一様な計量／記憶への共変結合の正準混合、(ii) 共形写像によるHamiltonianの記号恒等式、(iii) 5組の有限格子Poisson bracketの二次収束、(iv) 混合を意図的に落とすと閉包しない反例。

**未確認／未達成**： 任意の非対角3D計量を含む完全な3+1自由度の直接有限格子検査、局在した位相Skyrmionとの同時結合、不可逆な散逸とエントロピー生成、量子論・電磁気の復元、Einstein–Hilbert作用のエーテルからの独立導出、実験値に対する新規予測。

**次の有限課題**：完全な3Dに直行する前に、空間依存と非対角の偏極を許す模型で混合項を追跡する。さらに現行の`χ`を真の不可逆記憶に置き換える場合、閉じた系の総エネルギー・エントロピーを構成してから拘束を検査する。理論の「成功」には、重力方程式を最初から前提としない原始模型からの導出が必要。

## 5. 関連研究

- Gionti (2021), *Canonical Analysis of Brans-Dicke Theory Addresses Hamiltonian Inequivalence between the Jordan and Einstein Frames*, Phys. Rev. D 103, 024022: https://doi.org/10.1103/PhysRevD.103.024022
- Gionti & Galaverni (2024), *On the canonical equivalence between Jordan and Einstein frames*, EPJ C 84, 265: https://doi.org/10.1140/epjc/s10052-024-12586-z
- Tavakoli & Lewandowski (2026), *Canonical Clock Sectors and Relational Frame Equivalence in Brans-Dicke Theory*, Phys. Rev. D 114, 084067: https://doi.org/10.1103/zkm8-7ghz

## 6. 再現

```bash
python verify_v27.py
python independent_audit_v27.py
```

必要：`numpy`, `sympy`, `jax`, `matplotlib`。`bracket_convergence_v27.csv` 等のデータ、`audit_v27.json` と `independent_audit_v27.json` に監査結果を保存。ZIPとチェックサムで版を固定する。
