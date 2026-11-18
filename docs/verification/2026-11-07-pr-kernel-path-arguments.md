# カーネル再抽出のパス引数境界（2026-11-07）

PR #113 の引継ぎ記録 `docs/collaboration/handoffs/pr111-path-review.json`（同 PR のヘッド `4ddb26cf6c84d716a57a789ba66127aff3aea212`）の `next_action` に対応する変更の記録。数学的主張・Lean の定理・既存の検証器は変更しない。

## 指摘された問題

`main` = `f348ec7` の `tools/deps/pr_kernel.py` は、作業ディレクトリを `LEAN_PATH` の先頭に置くため、`lake env sh -c` に渡すシェル文字列へパスを引用せずに埋め込んでいた（`compile_probes`、`compile_<module>`、`extract` の3箇所）。空白などを含むパスではシェルが引数を分割し、コマンドが失敗する。PR #113 の `probe_shell_path.py` は同じ文字列の組立てを偽の実行ファイルで再現していた。

## 変更

- 3箇所を `lean_work_first(...)` に置き換えた。シェル側は固定のプログラム `LEAN_PATH="$PR_KERNEL_WORK:$LEAN_PATH" exec lean "$@"` だけを実行し、作業ディレクトリは環境変数 `PR_KERNEL_WORK`、その他のパスとモジュール名は位置引数で渡す。`lake env` が設定した `LEAN_PATH` の前に作業ディレクトリを置く順序（PR #111 の修正）はそのまま保つ。
- `status.json` の `cmd` は `shlex.join` で記録する。空白入りの引数の境界を記録から読み取れるようにするためで、この値を読む既存ツールはない。過去の `docs/dependency/pr-inventory/data/status-*.json` は変更していない。
- `compile_main`・`proof_only`・`analyze` はもとから引数配列で、変更していない。

## 検査

`tests/test_pr_kernel_paths.py` は偽の `lake`（`lake env` として固定の `LEAN_PATH` を設定してコマンドを実行）と偽の `lean`（引数・`LEAN_PATH`・作業ディレクトリを記録し、`-o` の出力を作る）、偽の `tools/verify.py` を使い、`pr_kernel.py` 本体を実行する。ワークツリー・作業ディレクトリ・ツールのコピー先・lake のライブラリパスが、空白を含まない場合と、空白・`$HOME`・`'`・`;` を含む場合の2通りで、Lean 呼出し5回の引数列と `LEAN_PATH` が意図どおり一つずつ届くことを確かめる。

| 実行 | 環境 | 結果 |
|---|---|---|
| 変更後の `pr_kernel.py` | Python 3.13.18、`/bin/sh` = dash、`unittest` | 2件とも成功 |
| 同上 | 同上、pytest 9.2.0（CI と同じ固定版）、`tests/test_deps_analyze.py` も同時実行 | 6件成功 |
| 変更前（`f348ec7`）の `pr_kernel.py` | 同上、`unittest` | 空白なしは成功、空白入りは `compile_probes` が exit 127 で失敗 |

変更前の版が空白なしの場合に同じテストを通ることは、空白のないパスでは各 Lean 呼出しの引数列と `LEAN_PATH` が変更前後で一致することを、この偽の環境の範囲で示す。

## 検査していない範囲

- 実際の Lean・Lake でのコンパイルと依存抽出。この作業環境には Lean がなく、ローカルでは実行していない。実 Lean での確認は、この変更の PR ヘッドに対する統合ワークフローの「Re-extract combined Lean kernel dependencies」ステップの結果で別途確認する（パスに空白を含まない CI 環境での実行）。
- 偽の環境での `analyze` ステップ（本物の `ExtractDeps` 出力が必要）。
- 実 Lean を空白入りパスで動かすこと、`tools/verify.py` など他のツールが空白入りパスを扱えるか。
