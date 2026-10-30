# ft09 の RESET 後のエッジ再記録（2026-10-29）

対象は PR #1 の `7e53dc5212ddb6d5fc444762203fbc78b26b0ec4` と
[失敗した45試行](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/40745980582)。
このft09修正は `core.py` の `solve()` の再帰深度問題とは別件です。ft09修正時点では同ファイルを変更していません。後続で `solve()` と証明書検査を深い方策に対応させました。

## 原因と状態不変条件

上流 `NodeInfo.record_test()` は初回検査専用です。入口でエッジの
`result == 0`, `target == ''`, `distance == 0` を要求します。
検査後は候補集合から除き、成功なら正逆の隣接表と到達先、失敗なら
`result == -1`, `distance == INFINITY` にします。
一度検査したエッジの移動再現と、新しい検査を区別する必要があります。

seed 0 / 2 / 4 の停止直前では次の同じ連鎖を記録しました。

1. `observe(GAME_OVER)` が `last_transition_suspicious=True` にする。
2. 評価器の外部 RESET は前回の source/action を消すが、そのフラグを残す。
3. RESET 後の最初の本物の操作の到達先も「疑わしい」とされる。
   `choose_action()` は同じ観測について2回 `record_test()` を呼ぶ。
   どちらも閾値3未満で無視され、到達先が未登録のまま `KeyError` になる。
4. 回復処理が前の操作を再実行する。`level_up=True` による再初期化予約は、
   次の `observe()` が古い status mask を見て `False` に戻してしまう。
5. source/action が古いまま次の結果を記録し、そのエッジを「失敗」とする。
   per-frame cache の既存の成功記録とも食い違い `ValueError` になる。
6. 再び古い操作を実行した結果を同じエッジへ記録し、未検査条件に違反する。

| seed | 停止時の呼出し数 | エッジ番号 | 記録直前 result | target | distance |
|---:|---:|---:|---:|---|---:|
| 0 | 433 | 27 | -1 | 空文字 | 2147483647 |
| 2 | 455 | 46 | -1 | 空文字 | 2147483647 |
| 4 | 319 | 15 | -1 | 空文字 | 2147483647 |

これは RESET 自体をグラフに登録する必要があるという問題ではありません。
外部 RESET の前後で操作の帰属が切れているのに、古い遷移フラグと例外回復時の
source/action/cache が残ったことが直接原因です。

## 接続側の修正

`explore_agent.py` のみで探索器との境界を修正しています。

- 外部 RESET で前回の source/action と疑わしさを一緒に消す。
  同一レベルの既存グラフは保持し、RESET を gameplay edge にしない。
- 既存の KeyError / ValueError / IndexError 回復ではグラフ、二つの frame cache、
  source/action、status mask をまとめて初期化する。物理操作の再試行は維持し、
  その結果を古いエッジに帰属させない。証拠 monitor の観測記録は保持する。
- `AdapterGraphExplorer` は既知エッジの同じ結果への再試行を冪等に扱う。
  候補集合、正逆隣接表、frontier、距離を書き換えない。
  異なる結果は `GraphTransitionConflict` として数え、上記の整合した再初期化へ進む。
  矛盾した結果で既存エッジを上書きせず、古い逆辺を残さない。
- 未検査エッジは上流にそのまま渡す。`AssertionError` は捕捉しない。
  予想外の未検査エッジの破損が引き続き assert になることもテストする。

上流の `graph_explorer.py`, `heuristic_agent.py`, `LICENSE`, `provenance.json` は
変更していません。固定出典は `dolphin-in-a-coma/arc-agi-3-just-explore` の
`c2d98318ecca38c8ee9fb49b5af159e51770bad7`、MIT license。
グラフ実装の SHA-256 は
`cebba2ae380e2ece6cff58ddb91f073cceca487e19e12adeb2dc16ab23a0ea0f` のままです。

このグラフの候補は画像の segment 単位で、実際のクリック座標はその内部から選びます。
矛盾はこの抽象化が異なる結果をまとめた場合にも起こり得るため、
再初期化を一般的な決定性の証明とは扱いません。

## 回帰検査と実行証拠

`tests/fixtures/ft09_reset_paths.json` は元の Actions artifact から取り出した
3 seed の GAME_OVER / RESET / 最初の結果です。run ID、元 trace の SHA-256、
artifact SHA-256 を収録しています。実環境での操作結果は45試行の評価で検査し、
この fixture test は記録された segment を選んで境界の処理を検査します。

追加11 tests は3つの失敗場面、開いた／閉じたノードの再試行、結果の矛盾、
予想外の assert、例外後の整合した再初期化、レベル変更 RESET を確認します。
既存の統合入口で合計180 tests / 3 subtests が合格しました。

```bash
python -X utf8 tools/verify.py --arc3-only
python tools/arc3_edge_diagnosis.py --environments /path/to/environments --output build/diagnosis
python tools/arc3_compare_results.py --before /path/to/before --after /path/to/after --output build/comparison.json
```

診断器は既存の `arc3.evaluate.run()` を呼び、各記録の直前状態、例外、RESET、
グラフ世代を保存します。操作方策を変更せず、候補集合と正逆隣接表とfrontierを照合します。
`--source-root` で修正前のcheckoutも指定できます。検査済みグラフが将来の環境を
正しく予測することや、画像による状態同一視が完全であることの証明ではありません。

`.github/workflows/arc3-ft09-regression.yml` は同一ランタイム・同一の取得済み環境を使い、
固定した修正前コミットと候補コードを各45試行で逐次比較します。
条件は公開 ls20 / ft09 / vc33、seed 0–4、explore/model/hybrid、
初回 RESET 込み500呼出し、追加 RESET 上限8です。
修正前の停止集合が ft09/explore/0,2,4、修正後の停止例外が0件であることを検査します。
全45試行の trace、summary、コード・依存版、環境ハッシュと比較結果をartifactに保存します。
時間は評価器内の初期化と操作を含む経過時間で、ダウンロードとテスト時間を除きます。
途中停止した試行も平均に含め、完走した試行だけの平均と混同しません。

### ローカルで完了した45試行の比較

Windows / Python 3.14.5、arc-agi 0.9.9、arcengine 0.9.3、numpy 2.5.4。
修正前・修正後を同じゲームファイルで逐次実行しました。

| 指標（45試行合計） | 修正前 | 修正後 |
|---|---:|---:|
| 停止例外 | 3 | 0 |
| policy recovery | KeyError 42 / ValueError 3 | 0 |
| 突破レベルの合計 | 42 | 42 |
| 完全クリア | 0 | 0 |
| 初期 RESET 込み呼出し | 22052 | 22345 |
| gameplay 操作 | 21771 | 22061 |
| 追加 RESET | 236 | 239 |
| 評価器内の実行時間（秒） | 228.755 | 241.985 |

ft09/explore の seed 0/2/4 は、呼出し数 433/455/319 での停止から、
すべて500まで実行できました。突破レベルはそれぞれ1/0/1のままです。
全試行の突破レベル数は各seedで保持され、model の15試行は操作・画面を含む
trace 全体も一致しました。速度改善やレベル突破率向上を示す測定ではありません。
時間は各1回の実測で、途中停止の解消による追加操作とホスト負荷も含みます。

過去artifactは SHA-256
`891514c8f50093018b0d1dd9be833ce7a8f7148e69e6dbca0db6bfa2ab55c55a`
でGitHub記録と一致しました。手元のゲーム .py / metadata は過去manifestとは
バイトハッシュが異なります。過去と同じファイルだとは認定していません。
ただし、修正前の45試行すべてについて、過去のtraceと操作・画面・状態・理由を含む
全行が改行差を除いて一致しました。新しい実行では手元の実ファイルのハッシュを
別manifestに保存し、GitHub workflowではその実行で取得した環境を両版に共有します。

## 公開25環境への拡張

既存の `ARC3 staged evaluation` の `workflow_dispatch` で
`stage=multi-seed`, `games=all`, `seeds=0 1 2 3 4`, `budget=500` とすると、
その時点のAPIカタログの正確なIDを選び、同じ修正済み接続で実行できます。
カタログが25件なら375試行です。出力の catalog と summary の件数を別々に確認してください。
カタログ取得やこの3ゲームの修正確認は、25ゲームすべてのプレイ成功を意味しません。
本件では未知・非公開環境への一般化、公式提出、最終Private Scoreは検証していません。
