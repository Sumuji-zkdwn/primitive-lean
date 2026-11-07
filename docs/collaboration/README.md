# Claude・Codex・Actions・Work・Sites 協調プロトコル v1

## 目的と境界

`Sumuji-zkdwn/primitive-lean` を成果物と来歴の中心に置き、引継ぎを記録する。研究ソース・定理・既存検証器をこのプロトコルの導入だけで変更しない。対象ブランチと PR を使い、main には自動マージしない。PR の合否は各ヘッドと実行範囲に結び付ける。README、AGENTS.md、および `tools/verify.py` を含む既存の運用を優先する。

| 役割 | この構成での責任 |
|---|---|
| Claude | 明示された課題の実装・証明候補・整理を独立ブランチで作る。仮定、変更ファイル、検査コマンド、未確認事項を引き継ぐ。 |
| Codex | 対象 SHA と差分を固定し、独立レビュー・反例探索・実行結果の照合を行う。生成側の結論を追認しない。 |
| GitHub Actions | 対象ヘッドに対し、該当ワークフローに記載されたチェックを行う。run ID・結論・検査範囲を記録する。 |
| ChatGPT Work | 権限・依存関係・記録を照合して課題を選び、次の担当へ渡す。自動で Claude を呼び出せるという保証はない。 |
| Sites | 既存の Primitive Research Ledger を再利用し、引継ぎを表示する。記録の真偽判定や自動実行はしない。 |

## 一回の引継ぎ

1. Claude は課題と仮定を確認し、変更を別ブランチでコミットして PR にする。main には直接反映しない。
2. `handoffs/` に本書の形式に沿う JSON を追加する。少なくともリポジトリ、PR、完全な対象ヘッド SHA、生成者の出自、主張、証拠の種類と URL、未確認事項、次の担当と終了条件を記録する。PR の本文や生成者による検査報告はその出典を明記し、独立確認とは区別する。
3. Codex は対象 SHA のソースを読み、可能な反例・境界条件を独立に調べる。実行した検査の対象、コマンド、結果、検査していない範囲を別項目にする。
4. Actions の実行結果を API または実行画面で照合する。`success` はそのジョブと対象 SHA の範囲のみを意味する。`action_required`・未実行・失敗・中断を成功に変換しない。Lean `--trust=0`、公理監査、Python 検算はそれぞれ確認された場合だけ記す。
5. Work は JSON の形式検査を実行してから Sites に取り込む。Sites の取り込みは一時表示であり、GitHub への書込みや既存ブラウザメモの置換は行わない。main が進んだ場合や PR のヘッドが変わった場合は古い成功を流用せず再検証する。
6. 必要なら Claude にレビュー結果を渡し、別コミットを作る。実際の応答を確認するまで「未着手」のままとする。完成した PR は人が判断する。

### 記録の検査

```sh
python3 docs/collaboration/check_handoff.py
python3 docs/collaboration/probe_shell_path.py
```

最初のコマンドは形式とヘッドの整合だけを検査し、リンク先や主張の真偽は検証しない。2 番目は偽の実行ファイルを使うシェル引数分割の再現であり、Lean のビルド・数学的証明は検査しない。追加したワークフローもこの二つだけを実行し、既存の統合 Lean 検証を代替しない。

## 接続と認証の実測（2026-11-08 JST）

- Work の GitHub 接続では対象リポジトリの読み書きが可能で、リポジトリは public。Work の GitHub 接続と Claude の認証は別であり、一方から他方の利用権限は推定できない。Site に GitHub の書込みトークンを埋め込まない。
- 作業環境で `claude`、`gh`、`netlify` コマンドは見つからなかった。Claude Code が別の環境で利用可能かは未確認。PR #111 本文は Claude Code が生成したと記載するが、今回の新規 Claude 実行を意味しない。
- Netlify の Agent Runner は別の接続経路になりうるが、今回の環境では CLI・プロジェクトの対象リポジトリ接続・課金枠・実行認証を確認していない。利用の可否は未確認。
- [Claude Code GitHub Actions の公式手順](https://code.claude.com/docs/en/github-actions)では、Claude GitHub App、認証用の Actions secret または対応クラウド認証、ワークフローを構成できる。Claude の認証方式と GitHub アプリの権限は別々に確認する。`main` の確認範囲に Claude 用 workflow は存在せず、アプリのインストールと secret の有無は未確認。この PR は接続権限や secret を変更しない。workflow の導入は別 PR で確認し、人が判断する。秘密値はチャットや Site に記録しない。
- PR #111 の履歴では、既存の Codex GitHub レビューが候補 `5e909f5` に指摘し、Claude Code が `fb049ad` で修正した後、同ヘッドの統合 Actions が成功している。新規 PR すべてで同じ連携が有効とは仮定しない。
- [GitHub の GITHUB_TOKEN に関する説明](https://docs.github.com/en/actions/concepts/security/github_token)によると、ワークフローからの操作は後続実行が抑止または承認待ちになる場合がある。今回の PR #112 の `action_required` との因果関係は未確認。
- 既存 Site は Site 独自のソースとバージョンを使う。今回の台帳画面は、GitHub の引継ぎ JSON を同梱するか、利用者が JSON を一時的に開く方式であり、GitHub からの自動同期、Site からの GitHub 書込みや Claude 起動はしない。Site は既存のアクセス範囲を変更しない。
- リポジトリ設定の `allow_auto_merge` は false。main の保護は確認時点で無効だった。設定によるマージ禁止を保証するものではないため、運用としてマージしない。権限や保護設定の変更は行っていない。

## 最初の実例と現在の限界

`handoffs/pr111-path-review.json` には、実際の過去の Claude → Codex → Claude → Actions の往復を、各段階の SHA と一次記録付きで記録する。さらに今回の Codex による独立シェル境界検査と Sites 表示を追加した。今回新たに Claude を呼び出したわけではない。

対象は PR #111 の `fb049ad18b3a6cb2de325fddb0180f2a3cae6fa5`。Actions run [42414035348](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/42414035348) は success。Codex の独立検査では、元のコードと同じシェル組立てが空白入りパスで失敗する反例を見た。これは Lean の数学的正当性や、空白のない当時の CI の成功を否定しない。PR #111 はその後 main にマージ済みで、今回の作業ではマージしていない。

別の Claude Code 統合候補 PR #112 の確認時ヘッドは `12ffd3293dad437a57dd877f7f8912ba2c53becb`。統合ワークフロー [42417954837](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/42417954837) は `action_required` で、ジョブが確認できなかった。原因・その後の変化は未確認。PR #111 の成功を PR #112 の成功として扱わない。さらに、[Codex の未解決レビュー](https://github.com/Sumuji-zkdwn/primitive-lean/pull/112#discussion_r4503887478)は、コンパイル失敗時に等式が `proved_equal` と集計されうる問題を指摘する。指摘対象の `tools/deps/copy_ring_stage.py` と `tools/deps/copy_report.py` は、レビュー時 `6073c14` と確認時ヘッド `12ffd32` で Git blob SHA が一致した。ここではその不具合を独立再現していない。

`site-ledger.patch` は既存 Site ソースに対する変更をレビューするための差分で、Site の通常のソースバージョン管理とは別にこの PR に収める。適用には既存 Site の ID とアクセス範囲を維持する。既存の台帳データは固定スナップショットで、現在の GitHub と同期済みとは限らない。
