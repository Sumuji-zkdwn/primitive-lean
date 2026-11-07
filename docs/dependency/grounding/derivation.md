# 初期層からの導出の確認（2026-11-07）

`README.md` の分類で、命題が初期の対象だけで書けるのに、証明が初期の定理を経由していない定理を対象に、初期層からの導出を確かめた。

## 対象の絞り込み

1. **候補**：語彙が `initial_only` で、証明が初期定理を経由しないもの。main の後続 12 定理と、PR #83 の 5 定理。
   - PR #91 の 2 定理は、命題が新しい対象 `historyUnitCost` を含む `mixed` なので、初期層からの導出という問いが成り立たず、対象外とした。
   - `mixed` のうち `energy_eq_primitive` や `chebyshevThree_eq_input` などは、新しい対象と初期の対象の等しさを述べる橋渡しの定理そのもので、証明は定義の展開と `ring` だけである。
2. **回り道の有無**：各候補について、全種類の辺でたどった依存の中に「新しい原始的対象」（初期層に触れずに定義された対象）があるかを調べた。
   - **回り道なし（15 定理）**：初期の定義と mathlib、および同じく初期の語彙で書かれた補題だけで証明されている。初期の定理は使っていないが、初期層（定義）からはすでに導かれている。
     - main：`hidden_state_above_chord`、`minimum_forgets_hidden_state`、`secondXY_eq_iterated`、`secondYX_eq_iterated`、`example_energy_gap`、`example_initial_data`、`minimum_iff_support`、`quartic_minimum_iff_full`、`unique_minimum_iff_strict_support`、`unique_minimum_of_strict_support_interpolation`
     - PR #83：`hasDerivAt_movingX_time`、`hasDerivAt_movingY_time`、`movingX_time_displacement`、`movingY_time_displacement`、`moving_translation_distance_eq_time_sq`
   - **回り道あり（2 定理）**：main の `LinearInputShearCommutator.original_potential_formula`（`LinearInputVariablePairs.energy` を経由）と `original_gradient_formula`（`energy`、`gradXu`、`gradient` を経由）。

## 回り道ありの 2 定理の直接導出

初期層（`lean/Elastica/` と `All.lean` の 36 部品）だけをモジュール `InitialLayer` にコンパイルし、後続層を一切 import しない環境で、2 定理を同じ命題のまま証明した（`tools/deps/derivation/DirectDerivation.lean`）。

| 定理 | 証明に使ったプロジェクトの定数 | 公理（`--trust=0`） |
|---|---|---|
| `original_potential_formula` | `LinearInputDesign.E`、`LinearInputDesign.f` | `propext`、`Classical.choice`、`Quot.sound` |
| `original_gradient_formula` | `LinearInputDesign.E`、上の定理 | 同上 |

元の証明が経由していた新しい対象は不要だった。再実行は `bash tools/deps/derivation/run.sh`。

## 結論（main の後続 984 定理）

| 分類 | 定理数 | 初期層からの導出 |
|---|---:|---|
| 初期の対象だけで書ける | 39 | **すべて確認済み**。27 は初期の定理を経由、10 は初期の定義から回り道なしで証明済み、2 は今回直接導出した |
| 初期の対象と新しい対象の混合 | 10 | 命題が新しい対象を含むため問いが成り立たない（多くは橋渡しの等式） |
| 新しい対象だけ（橋渡しあり） | 416 | 新しい対象が、別の定理で初期の対象と関係づけられている。関係が等式なら、命題を初期の対象の言葉に書き直して導出を問える。未確認 |
| 新しい対象だけ（橋渡しなし） | 489 | 初期の対象と関係を示す定理がなく、問いが成り立たない |
| mathlib の対象だけ | 30 | mathlib の事実で、初期層とは無関係 |

未統合 PR の新定理 1121 では、初期の対象だけで書けるものは 8（3 は初期定理を経由、PR #83 の 5 は回り道なし）。

## 読み方の注意

- 「導出済み」は、Lean が受理した証明が実在するという意味である。初期の**定理**からの導出と、初期の**定義**からの導出は区別した。
- 初期 465 定理は mathlib と定義から証明されているので、論理の意味ではどの定理も「初期定理なしで」証明できる。ここで確かめたのは、命題が初期の対象について述べているか、証明が初期層の外の対象を必要とするか、である。
- 「問いが成り立たない」は、初期の対象について何も述べていないという意味で、内容の価値を判断したものではない。
