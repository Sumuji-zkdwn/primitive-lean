# WFS 射影共役・周期観測の追補（2026-11-01）

## 対象と位置づけ

追加原稿: `lean/Elastica/WFSObservation.lean`。
名前空間: `LinearInputWFSObservation`。

これは既存の原始・エラスティカのエネルギーから WFS の経験則を導出したものではなく、指定した有理変換と周期観測についての**独立した数学的模型**である。
既存の `lean/Elastica.lean`、`tools/verify.py`、PR #3、および登録済みの証明原稿は変更していない。

## 主張と対応宣言

| 数学的主張 | Lean 宣言 | 明示した条件 |
|---|---|---|
| 斉次座標 `[X:Y] → [X:X+Y]` は可逆 | `gaugeInv_gauge`, `gauge_gaugeInv` | 実数の座標ペア |
| `C ∘ T = R ∘ C`, `T[X:Y]=[-X:2X+Y]`, `R[X:Y]=[-X:Y]` | `gauge_wfsLift` | 斉次座標ペア上の線形恒等式 |
| `T²=R²=id` | `wfsLift_involutive`, `reflection_involutive` | 同上 |
| `x ↦ d x (mod m)` が単射 ⇔ `gcd(d,m)=1` | `sample_injective_iff_coprime` | `m>0`、全状態を観測 |
| 4状態、2ステップの回転方向の別名化 | `four_state_two_step_alias` | `ZMod 4` の元1と3 |
| 4状態、1ステップでは区別できる | `four_state_one_step_separates` | `ZMod 4` の元1と3 |
| 6状態で2ステップ・3ステップの結合が単射 | `six_state_two_three_joint_injective` | `ZMod 6` で有限全数判定 |

プロジェクト全体の一部として使うには、既存の証明群に接続する依存関係・適切な `import` と統合監査を、**単独での Lean 検査後に**追加する必要がある。

## 射影的な解釈

通常の実アフィン座標 `z=X/Y` では、`T(z)=-z/(1+2z)`。ただし `Y=0` または `Y+2X=0` で同じ式をそのまま使わない。
新座標 `w=X/(X+Y)` では `w↦-w`。この関係を示す斉次座標ペア上の恒等式を Lean に記述した。
`ℙ¹(ℝ)` の商型そのものや、WFS という経験則とエラスティカとの同一性は形式化していない。

## 多重間引きの一般化（手計算のみ、Lean 未形式化）

`m>0` の巡回群で観測の集合が `d₁,...,dᵣ` のとき、
`g ↦ (g^d₁,...,g^dᵣ)` の単射性と `gcd(m,d₁,...,dᵣ)=1` は同値。
Bezout 等式から復元できる。非単射の追加センサー `q` を介する場合、この条件だけでは十分ではない。

## 検証方法と現時点の証拠境界

既存の固定環境：`lean/lean-toolchain` = `leanprover/lean4:v4.30.0-rc2`、
`lean/lakefile.toml` の mathlib revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

個別検証コマンド（リポジトリの `lean/` から）:

```sh
lake update
lake env lean Elastica/WFSObservation.lean
```

重要：この記録時点では実行環境に Lean／Lake がなく、**上のコマンドを実行していない**。
したがって 0 エラー、機械検証済み、既存の公理監査への統合、といった主張はしない。
一方、斉次行列の共役・自己逆性と `m=4,6` の有限写像については、独立の整数・記号演算で確認した（Lean ではない）。
ソースやmathlibが更新されれば、固定依存関係に照らした再検査が必要。

### 次の終了条件

1. 上記固定版で単独Lean検査が終了コード0で成功する。
2. 全新定理の `#print axioms` または対応監査を実施し、意図しない公理を含まない。
3. 別途 `gcd(m,d₁,...,dᵣ)=1` の一般的な複数観測版を Lean に導入する。
4. `q` が非単射の場合の十分条件・反例を分けて記述する。
