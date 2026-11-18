# Claude Code 単発接続試験

## 実行結果（2026-11-08 JST）

[PR #114](https://github.com/Sumuji-zkdwn/primitive-lean/pull/114) の単発接続試験は認証段階で終了した。構造化候補と候補の artifact は生成されなかった。

| 実行 | 記録 |
| --- | --- |
| [初回ヘッドの run 42422784716](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/42422784716) | 初回は認証情報が渡らず終了。再実行では認証情報が渡ったが候補を取得できなかった。 |
| [最終ヘッドの run 42423804853](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/42423804853) | OAuth 入力は非空。Claude が HTTP 401 を返した。認証失敗の根本原因は未特定。 |

[当時の設定](archive/114/claude-one-shot-pilot.yml) は最終ヘッド `7106ecb626e0c240c64002a4d130f33193d8df60` のファイルをそのまま保存したもの。現在の配置では GitHub Actions の実行対象外である。

## 試験当時の計画と途中経過

この積み重ねたドラフトPRは、既存の Claude Code GitHub Actions を使って、PR #111 に関するパス引用の修正候補を 1 件生成する試験である。対象PRの opened または workflow 自体を変更した synchronize イベント、同じリポジトリの指定ヘッドブランチ、指定ベースブランチにのみ限定する。Claudeには候補生成だけを依頼し、組込みツールとMCPツールを無効にする。GitHub権限はcontents・pull-requestsのreadのみで、mainへのpushやマージを行わない。API使用の上限は0.50 USD、最大2ターンに制限する。

候補はActions artifactにJSONとして保存し、Codexがソースとの一致・空白を含むパス・既存のLEAN_PATH継承・回帰テストを独立に検査する。候補を証明済みや実装済みとして扱わない。

対象PRの実行に `ANTHROPIC_API_KEY` または `CLAUDE_CODE_OAUTH_TOKEN` のどちらも渡されない場合、秘密値を表示せずエラー終了し、Claudeを起動しない。OAuth、Claude App、クラウドプロバイダその他の設定状況はこの試験から一般化できない。認証情報をリポジトリ・成果物・台帳へ保存しない。

このワークフローは接続試験専用であり、継続運用に採用するには起動条件と権限を改めて検討する。mainへの自動マージは禁止。

2026-11-08 の最初の再実行では認証情報が渡されたが、Claude実行は `is_error: true` で構造化結果を返さなかった。原因は未確認。失敗時は実行記録の数値HTTP状態と定型分類だけを出力し、生の応答や秘密値は表示しない。
