# 平面の伸縮・同期誤差・射影ロックの形式化と検証

作業日：2026年11月22日（日本時間）。

## 対象と出発点

主題は、回転を原始変数にしない記述により、何の計算が簡単になるか。
二つの異なる成果を、別の Lean モジュールで扱う。

- `lean/PlanarSyncMoments.lean`：対応点を持つ二つの平面像から、ずれの二次モーメントを集計し、実際の点更新から三成分再帰を導く。
- `lean/ProjectiveLock.lean`：指定した同次線形場の実際の商微分から Riccati 方程式を導き、逆正接による位相復元を通して一次の Adler 型方程式へ接続する。

元の研究ノートは [2026-11-22-planar-sync-projective-lock.md](../research/2026-11-22-planar-sync-projective-lock.md)。

基底コミット：`8ed4c9347609ff350f947da7e44101abcd993ed9`。

既存の Elastica、linear_input、Research の原本は変更しない。新規二モジュールは
通常の standalone module として既存の全体検証にも自動検出される。

## 散文と Lean 宣言の対応

| 散文の主張 | Lean の主な宣言 | 証明の範囲 |
|---|---|---|
| 共通点別変位は差から消える | `PlanarSyncMoments.common_drive_difference` | 実際の二点の混合・線形変形・共通加算の計算 |
| ずれの三成分が閉じて更新される | `sumMoments_transform`, `meanMoments_pair_step` | 任意の有限対応点集合の和と平均から導出 |
| E は点の二乗距離の平均 | `mean_energy_eq_average_squared_distance` | 非中心化二次モーメントの対角和 |
| 等方的な変形なら E 一つで更新可能 | `energy_update_isotropic` | 明示した等方条件からの更新公式 |
| 全方向の点ノルムが同倍率となる条件 | `point_energy_scaling_iff_isotropic` | 単位結合倍率での必要十分条件。一般のゼロ結合倍率例外は散文に残す |
| 三つの未来プローブで全成分を区別できる | `three_probes_separate`, `all_linear_readouts_eq_iff` | 任意の平面線形 readout の一致と Moment の一致 |
| 非零倍率を固定しても三成分を区別できる | `all_scaled_linear_readouts_eq_iff` | 任意の固定 β≠0 での同じ必要十分条件 |
| 同じ三成分なら同じ操作列に同じ予測を返す | `equal_moments_all_operation_lists` | 供給された有限の線形更新列の後の E の一致 |
| Eだけ・対角二成分だけでは不足する | `scalar_energy_counterexample`, `cross_moment_counterexample` | 明示的な有理数反例 |
| 線に潰れることは同期と同じではない | `line_collapse_not_synchronization` | 垂直成分0かつ非零エネルギーの反例 |
| 同次線形場から比 q=v/u のODEが得られる | `ProjectiveLock.quotient_hasDerivAt` | u≠0 と両成分の導関数を仮定した実際の商微分 |
| 逆数のチャートへ移れる | `reciprocal_hasDerivAt` | q≠0 における実際の逆数微分 |
| Δ=0 の明示的な指数収縮解 | `decay_initial`, `decay_hasDerivAt`, `decay_ne_zero` | 初期値・導関数・有限時刻の非零性 |
| 面の一方向の収縮が同じ比を与える | `plane_contraction_ratio` | 比の代数的恒等式。射影座標としての解釈は u≠0 |
| 有理的な観測が単位円上に乗る | `readout_on_unit_circle`, `sin_phase`, `cos_phase` | 有理式と実際の三角関数の同一性 |
| Riccati 軌道から Adler 軌道を復元 | `phase_ode_hasDerivAt` | φ=2 arctan(q) の連鎖律による実際の導関数 |
| 同次場の二乗はスカラー倍 | `fieldU_squared`, `fieldV_squared` | M²=(K²−Δ²)I/4 の二成分 |
| 無限遠チャートの軸を区別する | `infinity_axis_tangent_iff`, `infinity_zero_detuning` | 同次場の軸上での代数的条件 |
| Δ=0 の無限遠点に対応する明示軌道 | `infinity_trajectory_hasDerivAt`, `decay_ne_zero` | u(t)=0, v(t)=v₀ exp(−Kt/2) の実際の微分と非零性 |
| 閾値を超えると有限固定点がない | `root_discriminant_nonneg`, `no_root_beyond_threshold` | Riccati の固定点から判別式条件を導出 |
| 境界の二重根と具体的な二つの根 | `threshold_double_root`, `sample_root_small`, `sample_root_large` | 多項式の恒等式と具体例 |
| 具体的な根の局所勾配 | `sample_slope_small`, `sample_slope_large` | 実際の HasDerivAt。安定性定理そのものではない |

表で名前空間を省略した宣言は、直前の同じモジュールに属する。

## 実行環境と判定規則

- Lean：`leanprover/lean4:v4.36.0-rc2`。
- Mathlib：`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`。
- 数値検算：Python 3.12、NumPy 2.3.5、SciPy 1.17.0。
- Lean ソースを `--trust=0` で再コンパイル。
- 全所有定理に対して `Lean.Util.CollectAxioms` を実行。
- 既存チェッカーの許容公理は `propext`, `Classical.choice`, `Quot.sound` のみ。
- コンパイルの警告、未証明項、予期しない公理、検証中の入力変更は失敗とする。

統一した実行コマンド：

```bash
python -B -X utf8 tools/verify.py --planar-sync-only
```

数値だけを実行する場合：

```bash
python -B -X utf8 tools/verify_planar_sync.py --numerical-only
```

数値だけの成功は、Lean 成功とは記録しない。

## 実測結果

2026年11月22日（日本時間）、統一コマンドを作業ツリー上で実行し、
`status: passed`、`passed: true`、`errors: []` を確認した。
Python 3.12.14、NumPy 2.3.5、SciPy 1.17.0 を使用した。

| Lean 検証 | 結果 |
|---|---|
| 実行バージョン | Lean 4.36.0-rc2、compiler commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a` |
| `PlanarSyncMoments` | 明示定理27件、`--trust=0` 再コンパイル成功、警告0 |
| `ProjectiveLock` | 明示定理32件、`--trust=0` 再コンパイル成功、警告0 |
| 公理監査 | 自動生成分を含む所有定理103件、監査成功、警告0 |
| 検出された公理の和集合 | `propext`, `Classical.choice`, `Quot.sound` |
| 禁止構文・予期しない公理・入力変更 | いずれも0件 |

この実行の HEAD は上記の基底コミット、`dirty: true`。コミット前の追加・編集済み
ソースを対象とした実測であり、基底コミット自体に新定理が含まれるという意味ではない。
実行IDは数値・統合側 `20261121T181601386084Z`、Lean側 `20261121T181603843912Z`。
検証したソースの SHA-256 は次の通り。

| ソース | SHA-256 |
|---|---|
| `lean/PlanarSyncMoments.lean` | `f119cebea5d55a35acc26abb52b861fd6cab86563f66a0124fe64445f8d1b058` |
| `lean/ProjectiveLock.lean` | `6fd23fd80f21de1bcdc3eca2d1344e4b5cff80fef4efc8ec09a7b7d87785be95` |

数値検算も同じ統一実行内で再実行し、双方のプログラムが成功した。

| 検算 | 値 |
|---|---|
| 一点メッシュの有理数全探索 | 14,580例・完全一致 |
| 複数点メッシュの有理数比較 | 96例・完全一致 |
| 441点×2枚・80更新 | 三成分再帰との最大絶対誤差 約6.94×10⁻¹⁸ |
| 非線形結合の収縮上界 | 有理数10,201組で成立 |
| 射影場の有理数恒等式 | 60条件・完全一致 |
| 元の位相ODEと同次線形系 | 35条件×161時点、観測成分の最大絶対誤差 約1.76×10⁻¹⁰ |

出力は毎回新規ディレクトリに保存し、入力SHA-256、実際のHEAD、dirty状態、依存版を記録する。
公開コミットに対するCIの証拠と、コミット前の作業ツリー上の検算は区別する。

## 未形式化・未検証の範囲

- 天体の潮汐トルク、磁気散逸、電子スピンとの物理的対応。
- 慣性を含む二階模型の大域的な線形化。
- 一般のODEの存在・一意性・大域安定性。今回の軌道定理は供給された導関数か明示式を用いる。
- 射影直線全体の位相的同値、無限遠をまたぐ大域解の貼り合わせ。
- ロック域での一般根の吸引安定性、境界での1/t収束、極限における面の階数低下の解析的定理。
- 画像からの点対応推定、未知の変形入力の推定、既存の最適化済み計算法との速度比較。

定義した二次量の再帰を、そのまま証明の仮定にしたわけではない。有限メッシュの更新からの
導出が `meanMoments_pair_step` の対象である。また、有理的な場の恒等式だけで位相ODEを
証明した扱いにはせず、`phase_ode_hasDerivAt` に実際の微分の接続を持たせた。
