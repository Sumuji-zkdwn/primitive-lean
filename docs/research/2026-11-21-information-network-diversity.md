# 情報ネットワーク多様性：6頂点の反例と辺XORの観測商（2026-11-21）

対応するLeanソース：[`lean/Research/InformationNetworkDiversity.lean`](../../lean/Research/InformationNetworkDiversity.lean)

独立検算：[`tools/network_diversity_6.py`](../../tools/network_diversity_6.py)（Python 3.10以上、標準ライブラリのみ）

## 定義上の区別

- 状態：ラベル付き6頂点上の単純無向グラフ。辺は端点を昇順で一度だけ登録する。
- 次数 `degrees` と次数度数 `degreeHistogram` は別の出力。
- `hubNumerator` は Freeman 次数集中度の分子。6頂点では分母が20。
- `reachableWithin` は長さ `k` 以下の歩道の存在をBoolで再帰計算する。`boundedDistance` は0〜5で初めて真となった値を返し、未到達は番兵値6。数値定理の対象は、すべて連結している明示的な6頂点例に限定する。グラフ全般に対する距離の抽象的性質や、アルゴリズムの仕様への精密化定理は追加していない。
- `spatialLongEdges` は頂点の**空間配置**を別入力として要求する。ここでは整数直線上の距離が3以上の辺の本数。最短経路距離とは独立。
- `encode` は頂点値 `Fin 6 → Bool` を辺ごとの XOR リストに写す。元の頂点値を忘れた後に許される問い合わせ・遷移は、符号化写像の同じファイバー上で値が一致するものに限られる。

## Leanに入れた主な命題

| 区分 | 宣言 | 内容 |
|---|---|---|
| 6頂点証明書 | `AB_same_degree_histogram`, `AB_distance_sums`, `AB_distance_histograms` | 次数ヒストグラムは同じ、最短距離和27対29、距離度数は異なる |
| 反例 | `CD_same_degrees_long_different_distance` | ラベルごとの次数と長距離辺数を固定しても距離和が変わる |
| 反例 | `HI_same_distance_long_different_hub` | 距離分布と長距離辺数を固定してもハブ集中度が変わる |
| 反例 | `JK_same_degrees_distance_different_long` | 次数と距離分布を固定しても空間長距離辺数が変わる |
| 配置 | `A_position_changes_long_edges` | 同一グラフAでも空間配置によって長距離辺数0対6 |
| 動的観測 | `AB_current_connected_but_delete_distinguishes` | 現在の連結観測は同一、辺02の削除後は分離 |
| 情報型 | `encode_invertAll`, `encode_not_injective` | 全ビット反転が不可観測であり、絶対値を復元できない |
| 関係の保存 | `edgeBit_chain`, `A_relative_05_observable` | 辺03,35のXORから頂点0・5の関係を復元 |
| 一般条件 | `factorsThrough_iff_range`, `update_factors_iff_range` | 問い合わせ・状態更新が観測商の**到達値**上へ降りる必要十分条件 |
| 変換 | `xorMask_descends`, `resetZero_not_descending` | 頂点XORマスクは降りるが、頂点0の0へのリセットは降りない |

いずれの定理も既存 `relation_pruning.py` の出力を前提とせず、Lean側に独立した定義を与える。有限数値定理は `decide` によるカーネル検査可能な計算証明であり、`native_decide` / `sorry` / 追加公理は使わない。

## Pythonで確認するが、Leanには入れない主張

`python -B tools/network_diversity_6.py` で、全 `C(15,6)=5005` ラベル付き6頂点6辺グラフを検査し、うち連結グラフ3660個を調べる。

固定条件で層別化したとき、(ラベル別次数, 空間長距離辺数)が同じでも距離分布が変わる条件群501個、(距離分布, 長距離辺数)が同じでも集中度が変わる群12個、(ラベル別次数, 距離分布)が同じでも長距離辺数が変わる群633個を検出する。これらの全列挙数は**Pythonの有限計算証拠**であり、今回のLean証明対象には含めない。

辺XOR写像の出力数が連結成分数 `c` に対して一般に `2^(n-c)` になる命題も、現時点のLeanモジュールには含めていない。今回Leanで証明したのは、全体反転による非単射性、A内の0↔5関係の観測可能性、降下条件の一般的な特徴づけである。

## 再現

```bash
python -B tools/network_diversity_6.py > /tmp/network-diversity.json
python -B -m unittest discover -s tests -p 'test_network_diversity_6.py' -v
cd lean
lake exe cache get
lake env lean --trust=0 Research/InformationNetworkDiversity.lean
# 他の独立Leanソースも含めて検査する場合、リポジトリ直下で
# python -B tools/verify.py --toolchain-modules-only
```

Leanのビルドと公理監査についてはPRの該当コミットに対する実際のCIログを優先し、Python側の成功をLeanコンパイル済みとみなさない。mainへの自動マージはしない。
