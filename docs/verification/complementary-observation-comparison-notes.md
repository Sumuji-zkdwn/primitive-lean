# 補完観測の比較と反例 — 観測核・情報保持・復元条件

## 対象と出典

この比較は、観測写像の値・核・像上の逆写像に限る。異なる状態空間間の同型、時間発展の共役、物理的同一性は主張しない。

- F16: PR #23、コミット `675f2c50cf19e33446eceee24c060eb1a3dc783d` の [F16UnexpectedBridges.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/675f2c50cf19e33446eceee24c060eb1a3dc783d/linear_input/lean_check/F16UnexpectedBridges.inc)、[F16CompleteRank.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/675f2c50cf19e33446eceee24c060eb1a3dc783d/linear_input/lean_check/F16CompleteRank.inc)。既存の `zero_probe_isUnit`、`opposite_probe_sum`、`opposite_probe_joint_injective`、`rank_at_plus_one`、`rank_at_minus_one` を根拠とする。
- 4位相観測: PR #19、コミット `6bd74237f7b1910942988e6f542987857e9dec91` の [WFSMobiusFourier.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/6bd74237f7b1910942988e6f542987857e9dec91/linear_input/lean_check/WFSMobiusFourier.inc)。特に `trace4_values`、`even_fourier_trace`、`odd_fourier_trace`、`fourier1_formula` を参照する。
- 追加証明対象: `linear_input/lean_check/ComplementaryObservationExamples.inc`。このファイルは PR #19 ブランチを取り込まず、その検証済み `trace4_values` が与える明示的な座標形を別名前空間で扱う。したがって、今回のCIが PR #19 全体を再コンパイルしたという意味ではない。

## 共通する条件

線形観測 \(P:V\to Y_+\)、\(Q:V\to Y_-\) を対にして記録すると、

\[
\ker(v\mapsto(Pv,Qv))=\ker P\cap\ker Q.
\]

したがって、両方の観測に同時に隠れる非零の差分が存在しないことが、状態を一意に識別する条件である。各観測の単射性は必要ない。復元写像 \(R\) に要求する等式は、状態側では \(R(Pv,Qv)=v\)、データ側では **実現可能な観測対に対して** \((P,Q)(Ry)=y\) である。

一般の行列束 \(A(t)=B+tC\) では、標数が2でない体上で

\[
\ker A(1)\cap\ker A(-1)=\ker B\cap\ker C.
\]

このため \(B\) の可逆性は十分条件である。必要条件ではない。

## F16と4位相の正確な比較

| 項目 | F16の2観測 | PR #19の4位相座標形 |
|---|---|---|
| 状態 | \(v\in\mathbb R^{16}\) | \(z=(x,u)\in\mathbb R^2\) |
| 個々の観測 | \(P=A(1),\ Q=A(-1)\) | \(E(z)=(x,-x),\ O(z)=(-u,u)\) |
| 個々の核 | 各4次元（既存の階数12と有限次元の階数・退化次数公式から） | \(\ker E=\{(0,u)\}\)、\(\ker O=\{(x,0)\}\) |
| 共通核 | \(\{0\}\) | \(\{(0,0)\}\) |
| 復元 | \(A(0)^{-1}(y_++y_-)/2\) | \((y_{\mathrm{even},1},y_{\mathrm{odd},2})\) |
| 全位相データから | 2本の16次元データを使用 | \(q=(x,-u,-x,u)\) なら \((q_0,-q_1)\) |
| 生の観測平均 | \(B=A(0)\) が可逆 | \((E+O)/2\) は可逆でない |

**共通核がゼロであることと、2つの核が状態空間全体を直和分解することは異なる。** 4位相の2本の核は2つの座標軸であり、その直和は \(\mathbb R^2\) 全体になる。一方、F16では各核が4次元なので、その直和の次元は8であり、16次元の全状態空間を尽くさない。共通の主張は核の交差がゼロであることまでである。

### 生のeven/odd観測を平均するだけでは復元できない

PR #19 の座標形をそのまま同じ \(\mathbb R^2\) 値の観測として平均すると、

\[
\frac{E(x,u)+O(x,u)}2
=\left(\frac{x-u}{2},\frac{u-x}{2}\right).
\]

これは \((0,0)\) と \((1,1)\) を区別しない。したがって、生のeven/odd観測が「可逆な中点から平均で復元する」というF16の十分条件を満たす、とは言えない。観測対を保持すれば直接復元できるため、一般定理の必要条件でないことの具体例にもなっている。追加の `phase_average_collision` はこの衝突を明示する。

### 4位相データの実現可能性

4個の任意の実数がすべて状態の観測列になるわけではない。必要十分条件は

\[
q_2=-q_0,\qquad q_3=-q_1.
\]

この条件の下で \(z=(q_0,-q_1)\) とすれば4位相をすべて再構成できる。追加の `phase_decode_trace`、`phase_trace_decode_of_compatible`、`phase_compatible_iff_realizable` は、状態からの復元と整合データの再観測を分けて述べる。

PR #19の既存 `fourier1_formula` は \(c_1=(x+iu)/2\) を与えるため、その実部・虚部の両方を保持すれば \(x=2\operatorname{Re}c_1\)、\(u=2\operatorname{Im}c_1\) と読める。これはその明示式の代数的帰結である。今回の追加モジュールでは一般のフーリエ復元定理や標本化定理を主張しない。

## 成立しない場合と、過剰な必要条件への反例

以下は定理の仮定や結論の範囲を確認するための例であり、一般定理を否定するものではない。スカラーの例は1次元の線形行列束である。

| 例 | 正確な結論 | 追加定理 |
|---|---|---|
| \(\mathbb R\) 上で \(B=C=0\) | 異なる状態0と1が同じ観測対を持つ | `zero_pencil_collision` |
| \(\mathbb R^2\) 上で \(B(x,u)=(x,0),\ C=0\) | 非零の観測でも共通核があれば復元できない | `repeated_projection_collision` |
| \(\mathbb R\) 上で \(B=0,C=1\) | \(B\) は非可逆だが観測対 \((v,-v)\) は単射であり、第1成分で復元できる | `singular_center_can_be_injective`、`singular_center_alternative_decoder` |
| \(\mathbb F_2\) 上で \(B=C=1\) | \(B\) は可逆でも2つの観測はともにゼロになる。標数2の除外が必要 | `binary_pair_zero`、`characteristic_two_collision` |
| \(\mathbb R\) 上で \(B=1,C=0\)、入力データ \((1,0)\) | 実現不能。復元値は \(1/2\)、再観測は \((1/2,1/2)\) となり、元の任意データには戻らない | `inconsistent_pair_not_realizable`、`inconsistent_pair_not_reconstructed` |

## 新しい座標形の証明対応

| 主張 | `LinearInputComplementaryObservationExamples` 内の定理 |
|---|---|
| even観測が保持する情報はx座標 | `even_observe_eq_iff` |
| odd観測が保持する情報はu座標 | `odd_observe_eq_iff` |
| 個々の観測核 | `even_observation_kernel`、`odd_observation_kernel` |
| 共通核がゼロ | `complementary_phase_kernels` |
| 観測対からの直接復元 | `phase_pair_decode` |
| 生の観測平均の衝突 | `phase_average_collision` |
| 4位相列と復元演算 | `phase_trace_values`、`phase_decode_trace`、`phase_trace_injective` |
| 整合するデータ上の逆と像の特徴付け | `phase_trace_decode_of_compatible`、`phase_compatible_iff_realizable` |

追加の座標形・反例は、コミット `362dd5d286155abeb01c685aa17bbbe9172548f8` の [CI実行41420522608](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41420522608) で、一般定理と合わせて44定理・61宣言の独立コンパイル・公理監査に成功した。F16を含む全体は902定理・1129宣言で成功した。詳細は [検証記録](2026-11-02-complementary-pencil-recovery.md) を参照。

PR #19側の参照コミットについても、[CI実行41232573849](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41232573849) の証明・公理監査成功を確認した。今回の独立検査は、そこで証明された4位相の座標形を対象とする。
