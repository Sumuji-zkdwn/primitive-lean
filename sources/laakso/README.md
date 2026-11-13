# Laakso拡張の保存原本

このディレクトリはResearchの有限検算と、導入評価時の独立Lean試作を変更せずに保存する。正式な証明は `linear_input/lean_check` の三つの新規原稿、現在の有限検査は `tools/check_laakso_finite.py` に置く。

| ファイル | 原本の役割 |
|---|---|
| `laakso.py` | bitとwormhole階層による標準有限グラフ、辺ID・有理辺長・有限射影検査 |
| `verify_laakso_connection.py` | 再帰的な三分割・二枚化・新規分点接合と、経路のsignature/relay反例 |
| `verify_scale_flow.py` | 四次反応の平均非閉包、同期部分系、有理係数多項式の検査 |
| `TowerBridge-probe.inc` | 導入評価時の集合逆系とscalar平均非降下の独立Lean試作 |

各原本の保存元とSHA-256は [出典台帳](../../docs/laakso/provenance.json) に記録する。これらは過去の入力資料であり、保存するだけで今回検証したことにはならない。Python原本を直接実行すると隣接位置へ結果を書き込むため、通常の再現には統合された検査入口を使う。
