# ERG `extends_main`：検証器の条件が単一の線形鎖を与えること

## 位置づけ

ERG-Aout の [FORMALIZATION.md](https://github.com/Sumuji-zkdwn/ERG-Aout/blob/main/docs/FORMALIZATION.md) は accepted 層の関係 `extends_main` に「非巡回」かつ「単一の線形な正準鎖（path invariant）」を要求し、検証器 `tool/validate_r001_kernel.py` はこれを、非巡回性、入次数・出次数 ≤ 1、始点と終点がちょうど1つずつ、始点から後続をたどって全ノードに到達、という別々の検査で確かめている。この追加は、その有限グラフとしての意味を Lean で特徴づける。

- Lean：[lean/Research/ErgCanonicalChain.lean](../../lean/Research/ErgCanonicalChain.lean)（名前空間 `ErgCanonicalChain`、11定理）
- 独立検算：[tests/test_erg_canonical_chain.py](../../tests/test_erg_canonical_chain.py)
- 専用CI：[.github/workflows/erg-canonical-chain.yml](../../.github/workflows/erg-canonical-chain.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

ERG-Aout のファイルは変更していない。検証器の Python コードそのものの正しさではなく、それが検査しているグラフの性質についての定理である。

## 結果

主ノードを有限型 \(V\)、辺を部分後続関数 `next : V → Option V`（出次数 ≤ 1 を型に組み込む）で表す。仮定は三つだけ：入次数 ≤ 1（`Injective`）、前任のない始点 \(s\)、すべてのノードが \(s\) から `next` の反復で到達できること。

| 内容 | Lean 宣言 |
|---|---|
| \(s\) からの鎖は同じノードを二度通らない | `iter_injective` |
| 鎖は \(\lvert V\rvert\) 歩で止まる | `iter_card_eq_none` |
| **正準鎖**：\(0,\dots,\lvert V\rvert-1\) 歩目で全ノードをちょうど一度ずつ列挙し、\(\lvert V\rvert\) 歩目で終わる | `canonical_chain` |
| 非巡回（検証器の acyclic 検査は他の条件から従う） | `no_cycle` |
| 始点の一意性、終点の一意性（start/end 検査も従う） | `start_unique`、`end_unique` |
| 逆：\(\mathrm{Fin}(n+1)\simeq V\) で並べたパスは三つの仮定を満たす | `path_satisfies` |

したがって、入次数 ≤ 1・出次数 ≤ 1・前任のない始点からの到達可能性の三条件だけで「単一の線形鎖」が特徴づけられ、検証器の非巡回性・始点終点の個数の検査は（主ノードの集合が空でない限り）論理的には冗長である。冗長な検査を残すこと自体は、エラーメッセージを分ける実務上の意味がある。

## 手書きの証明

鎖 \(w_k=\mathrm{next}^k(s)\) で \(w_i=w_j\)（\(i<j\)）とすると、入次数 ≤ 1 から \(w_{i-1}=w_{j-1}\) と一歩ずつ戻れて、最後に \(s=w_{j-i}\)（\(j-i\ge1\)）となり、\(s\) が前任を持つことになって矛盾。よって鎖は単射で、有限なので \(\lvert V\rvert\) 歩以内に止まる。全ノードが鎖上にあるので、ちょうど \(\lvert V\rvert\) 個を列挙する。閉路があればその上のノードが鎖上に二度現れることになり、終点（後続のないノード）は鎖の最後の一つに限られる。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 Research/ErgCanonicalChain.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。全11定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内（2定理は公理に依存しない）。
- `python -B tests/test_erg_canonical_chain.py`：3テスト合格。1〜5ノード上の全ての部分後続関数を列挙し、三つの仮定を満たすものは深さ優先探索で閉路なし、始点・終点がちょうど1つ、鎖が全ノードを一度ずつ列挙することを確認。仮定を満たす組はちょうど \(n!\) 個（ラベル付きパスの数）で、逆にすべてのパスが仮定を満たす。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 同じ辺の重複（多重辺）は `next` では表せない。重複辺は入次数 2 として検証器が拒否する場合に当たり、ここでの仮定の外にある。
2. ERG の層・型・端点の層の検査（`L_accepted` 内であること等）は扱わない。
3. ERG 側のノードの昇格・束縛は行わない。必要なら R005 の手順で、この宣言を path invariant の定義ノードに束縛できる。
