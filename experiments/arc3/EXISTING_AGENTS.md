# 公開ARC-AGI-3実装の再利用

2026-10-27。個人リポジトリの検索に加え、公開実装を調査しました。
ここでいう「既存」にはLLMを使うエージェント、実行基盤、探索アルゴリズムを含みます。
調査したREADMEの識別子は `public-agent-sources.json` に記録しています。
公開READMEの成績を今回の実測成績として扱っていません。

| 既存実装 | 確認した構成・再利用する部分 | 今回の状態 |
|---|---|---|
| [公式Agents](https://github.com/arcprize/ARC-AGI-3-Agents) | エージェントの実行例とSDKの入口 | README確認。新しい推論モデルそのものではない |
| [Explore It Till You Solve It](https://github.com/dolphin-in-a-coma/arc-agi-3-just-explore) | 画面処理とグラフの未探索先への経路探索 | 固定ソースのMITコードを接続し、CPUで公開3ゲームを実測 |
| [The Duck](https://github.com/Tufalabs/duck-harness) | Pythonツール、実験記録、LLMによる操作、TAAF基盤 | README確認。モデルサーバーまたはOpenRouterが必要。未接続 |
| [Daniel Franzen版](https://github.com/da-fr/arc-agi-3-solution) | Duckを基にした計算配分、長文脈、実行保護 | README確認。競技再現は専用のGPU・推論環境。未接続 |
| [Retrodict](https://github.com/ryanbbrown/Retrodict) | 記録で仮説を反証し、行動前に予測する構成 | README確認。LLM実行は未実施 |
| [Tycho](https://github.com/NIMI-research/Tycho) | `State/init_state/transition/render/outcome` の実行可能モデル、検証・計画 | README・アーキテクチャ確認。モデルAPIとコンテナが必要。未接続 |
| [DreamTeam](https://github.com/NVIDIA/dream-team) | 共有の実行可能モデルを観測・実験・検証で更新 | README確認。LLMゲートウェイを使う実行は未実施 |
| [Arcgentica](https://github.com/symbolica-ai/ARC-AGI-3-Agents) | Agentica SDKを使うエージェント | README確認。詳細実行仕様・APIとの接続は未確認 |

## 今回接続した既存ポリシー

出典は `dolphin-in-a-coma/arc-agi-3-just-explore` のコミット
`c2d98318ecca38c8ee9fb49b5af159e51770bad7` です。
`vendor/explore/provenance.json` に元ファイルと導入後のSHA-256を記録し、MIT LICENSEを同梱しました。
`graph_explorer.py` は変更せず、`heuristic_agent.py` はパッケージ内importと明示的seedだけ変更しました。
新しい `compat.py` と `explore_agent.py` が旧PreviewのHTTPループを現在のオフラインSDKに接続します。

- `score` と `levels_completed`、リセットとレベル変更時の処理を接続。
- 最終画面とアニメーションの枚数を保存。既存ポリシーが使うのはこの2点です。
- 旧HTTP用の待機を無効化し、乱数の状態を他のエージェントから独立。
- 元の `main()` にある例外後の直前操作再試行を接続部に実装。回復回数と種類を測定。
- こちらの `InteractionModel` は生の操作・観測を別に記録するモニタとして接続。
  その予測で既存ポリシーを改善したとは主張しません。

既存の画面分割、色の優先順位、ステータスバー除去はそのまま仮説として残ります。
これらを意味づけ前の核や475定理の帰結にはしません。
このPreview由来ポリシーはACTION7の選択を実装していません。
対応外の操作選択はエラーにし、別方式へ無言で置き換えません。

```bash
python experiments/arc3/run.py --agents explore model structure random --games ls20 ft09 vc33 --seeds 3 --budget 500 --environments /path/to/environment_files --output experiments/arc3/runs/public-comparison
```

結果は `reports/explore-summary.json` と `reports/explore-metadata.json` に保存します。
同じseed・上限で、既存探索器の突破レベルはls20=0、ft09=0、vc33=2でした。
旧自作モデルの比較記録は1・1・1、構造版とランダム版は0・0・0です。
全方式とも完全クリアは0でした。既存探索器のKeyErrorからの回復は3・0・3回です。
元の公開成績を再現した実験ではなく、移植した既存探索器の小規模な接続検証です。

## 475定理との接続方針

既存エージェントが候補の表現・遷移・方策を作る部分を再利用し、こちらは
仮定の明示、記録との整合、反例、忘却してよい情報の条件を検査する部分を担当します。
今回実装した接続は探索ポリシーと記録モニタまでです。
Tychoなどの候補モデルから定理の前提を証明し自動適用する部分は未実装です。
