# Astra 物理学の導入：Kerr–Koopman の材料・観測・有限力学

このリポジトリでの「Astra 物理学」の最初の導入対象は、電磁場と尺度変換の研究から得た Kerr–Koopman の Lean 定理群である。原資料は `kerr-koopman-lean` のコミット `51a49be2e8f8b440c891240b574fdf97e08b9e84`。`primitive-lean` の導入元は `e17a3da948221535d0539a21e2f8a7074a72fa49` である。元の証明名を保持し、既存の線形入力の定理に接続する。

初回には **10 原稿・126 定理**を追加した。内訳は物理・観測の 125 定理と、導入元 main にない Koopman 引き戻しの 1 定理。既存の `Design.lean`、`Calculus.lean`、`Observation.lean` にある 29 定理は、そのまま再利用する。

続く[有限系の大域解と分割反復](finite-flow.md)では、5原稿・50定理の解析結果と、新規34定理の有限行列への接続証明を追加した。Astra全体では **16原稿・210定理・263名前付き宣言**となる。任意の固定有限行列と実際の材料逆関数について、全実時間の存在・一意性、既存の分割更新との一致、O(1/n) の誤差評価と収束、物理的なE,Hへの復元後の誤差を扱う。原資料全体の後続 PDE 定理群を導入したという意味ではない。

## 何を接続するか

実数の電場 E、電束密度 D、磁場 H に対し、無次元化した材料則を

```text
D(E) = E + E³/3
U(E) = E²/2 + E⁴/12
W(E) = E·D(E) − U(E) = E²/2 + E⁴/4
```

と定義する。U は構成則を微分で与える共エネルギーであり、保存則に用いる電気エネルギーは W である。この区別を保持する。

「原始」の四次ポテンシャルを係数 λ=1/3、r=1、入力 u=D に特殊化すると、`U(E) − D·E` に一致する。既存の微分・最小化定理を実際に適用して、次を得る。

```text
a が U(E) − D·E の大域最小点  ⇔  D = a + a³/3
E(D) = 2 sinh(asinh(3D/2) / 3)
|E(D₁) − E(D₂)| ≤ |D₁ − D₂|
```

逆関数は全実数上で一意かつ滑らかであり、初期値ごとの枝選択を要しない。ここで解消した計算は、各点での材料則の三次方程式である。空間と時間の連成を解く仕事は別に残る。

| 追補原稿 | 定理数 | 証明する内容 |
|---|---:|---|
| [AstraKoopmanDescent.inc](../../linear_input/lean_check/AstraKoopmanDescent.inc) | 1 | 半共役と既知の固有関数からの引き戻し |
| [AstraRiccati.inc](../../linear_input/lean_check/AstraRiccati.inc) | 8 | 材料則、尺度による微分の相殺、スカラー Riccati 方程式と寿命の条件付き評価 |
| [AstraFiniteEnergy.inc](../../linear_input/lean_check/AstraFiniteEnergy.inc) | 13 | 有限 Maxwell 系の実際の微分、エネルギー保存、磁場・電束の総和の微分 |
| [AstraReconstruction.inc](../../linear_input/lean_check/AstraReconstruction.inc) | 23 | 同じエネルギーを持つ滑らかな周期波列と、点復元の非有界性 |
| [AstraConstitutive.inc](../../linear_input/lean_check/AstraConstitutive.inc) | 23 | 原始の最小化との同値、一意性、Legendre の関係、逆材料則の安定性 |
| [AstraObservation.inc](../../linear_input/lean_check/AstraObservation.inc) | 11 | 二つの入力からの磁場復元、誤差、共通尺度と Koopman 反復式 |
| [AstraDynamicsBoundary.inc](../../linear_input/lean_check/AstraDynamicsBoundary.inc) | 8 | 静的最小性・停留性・エネルギーの瞬時変化だけでは Maxwell 則を決められない反例 |
| [AstraExplicitMaterial.inc](../../linear_input/lean_check/AstraExplicitMaterial.inc) | 9 | sinh/asinh による明示逆関数、両側の逆写像、滑らかさ、微分、Lipschitz 性 |
| [AstraRelativeEnergy.inc](../../linear_input/lean_check/AstraRelativeEnergy.inc) | 10 | 相対電気エネルギーの非負性、誤差と非線形剰余の評価 |
| [AstraExactShear.inc](../../linear_input/lean_check/AstraExactShear.inc) | 20 | 二つの部分流の厳密解、物理時間での分割式、非可換性、連成方程式への残差 |

## 物理時間の有限系

有限添字集合と実行列 Q を固定し、Q を空間微分に対応する演算子として用いる。時間発展は追加の定義として与える。

```text
dEᵢ/dt = −(QH)ᵢ / (1 + Eᵢ²)
dHᵢ/dt = −(QE)ᵢ
```

`energy_conserved_on_Icc` は、Q が反対称で、与えられた E,H が指定区間上でこの微分方程式を満たすことを仮定し、`Σᵢ(Hᵢ²/2 + W(Eᵢ))` の区間両端での一致を証明する。さらに Q の各行の和がゼロなら、磁場と電束密度の総和の時間微分もゼロになる。この追補単独では、任意初期値からの ODE 解の存在や連続体極限を証明していない。

D,H 座標では二つの部分流が

```text
Aₜ(D,H) = (D − tQH, H)
Bₜ(D,H) = (D, H − tQ E(D))
```

となる。`lieStep_explicit_formula` は共通の明示材料逆関数を使って `Bₜ ∘ Aₜ` を評価する式を与える。各部分流の微分は厳密に確認している。一方、`shears_do_not_commute` は非可換係数が非ゼロのときに合成順序を交換できないことを、`lieStep_not_exact_at_nonzero_residual` は非ゼロ時刻で残差係数が非ゼロのときにその合成曲線が連成方程式の解にならないことを証明する。[有限系の追加](finite-flow.md)で、同じ更新を細かく反復する極限を実際の大域解へ接続する。

## 共通尺度・Koopman 観測の範囲

`scaled_eigenfunction_pullback_iterate` は、状態更新 f、縮約更新 g、写像 q が `q ∘ f = g ∘ q` を満たし、観測 ψ が `ψ ∘ g = λψ` を満たすとき、任意の共通な可逆尺度を通じて

```text
ψ(q(fⁿ(s))) = λⁿ ψ(q(s))
```

を保つ。尺度は `Equiv` として任意であり、指数 0.42 に固定していない。ただし半共役・固有関数は仮定で、尺度の連続性や有界性もこの定理からは得ない。非局所 RKHA の構成、生成作用素と随伴の共同解析性、全モードでのレゾルベント・射影の一様収束は、この導入の結論に含まれない。

復元の障害も同じ入口から検査する。`no_bounded_magnetic_encoder` は、同じ平均とエネルギーを持つ滑らかな周期初期波形族について、**一様に有界な符号化と連続線形の点復元を同時には持てない**ことを示す。非線形復元や、より強い初期正則性を課した設計まで否定する定理ではない。

## 出典と再検証

- [原本と変換の台帳](manifest.json)：原本 19 モジュールの依存閉包、SHA-256、15 追補への変換、既存 3 原稿の再利用、新規の有限系接続証明。
- [保持した原本](../../sources/astra_physics_20261109/KerrKoopman/)：元の `.lean` を保存する。追補の生成で除去するのは `import` 行だけで、証明本文・名前空間・定理名を保持する。
- [統合台帳](../integration/manifest.json)：既存と同じソース監査へ登録する。
- [ソース監査](../../tools/check_astra_physics.py)：原本、変換規則、再利用先の対応を検査する。Lean の核検証とは別の検査である。

```bash
python -B -X utf8 tools/check_astra_physics.py
python -B -X utf8 tools/verify.py --proof-only
python -B -X utf8 tools/verify.py --integration-only
```

Lean と mathlib はリポジトリの既存の固定版を使う。新しい追補も既存の `MainResult.lean` 生成・`--trust=0`・全宣言公理監査に含める。許可する公理は `propext`、`Quot.sound`、`Classical.choice` のみ。新しい公理を追加して物理学を導入する構成ではない。

実行記録は [初回の検証記録](verification.md)、[有限系追加の検証記録](verification-finite-flow.md)、[依存関係解析の修正記録](dependency-analysis.md)にまとめる。原資料の過去の成功記録、統合後の実行、リモート CI の成否を区別する。

## 次に導入する順序

1. 原資料の解析的小初期値に対する非粘性 PDE と、正粘性を固定した PDE の定理を、仮定を保って別々に導入する。
2. 復元・空間極限・スペクトルの各主張について、証明済みの依存先を明示して追加する。今回の有限系の誤差定数は行列ノルムに依存し、空間解像度について一様な評価とは限らない。

原資料でも、一般の粘性ゼロ極限における非線形項の同定と衝撃波後の一意性は未完了である。初期値・保存量だけから一般の周期混合波を有限の簡単な式で厳密に解く、という結論はここから主張しない。
