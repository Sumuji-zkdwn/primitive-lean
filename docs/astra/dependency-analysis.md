# CI の依存関係解析と組み立て文脈

PR #122 の head `2d11825231afdbead53a71138282e6fdcfadd43b` に対する [CI run 42644090525](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/42644090525) は、25段階の統合検証に成功した後、依存関係の解析で失敗した。`analyze.py` が原稿を無加工で連結した場合の位置計算だけを扱っていたため、HilbertFlow の組み立て文脈で `assembly mismatch` になった。

修正は `tools/deps/analyze.py` と回帰テストに限定する。解析器は、組み立て側と同じ `check_astra_physics.assembly_fragment` を使い、登録した文脈と原本のバイト列を完全照合する。文脈の prefix・suffix・区切り行は原本に帰属させず、その全行数を考慮して後続原稿の位置を求める。

現在の report と manifest の文脈は一致しなければならず、固定 allowlist と記録済みハッシュも検査する。文脈情報がない過去の report は従来どおり無加工のバイト列を要求する。任意の文脈や原本変更を許可する変更ではない。

## 実際に行った再検査

- 関連テスト **19件成功**。既存5件に加え、原本の前後と改行、文脈・原本・区切り・台帳の改変拒否を確認する14件を追加した。
- リポジトリ unittest **188件成功**。初回の有限系導入時の174件と区別する。
- 保存原本・登録監査も成功。証明・公理監査・元の233検証入力は変更していない。
- 失敗した実CIの `raw.json`、`PrimitiveMain.lean`、検証レポートを使う再解析が成功し、**4,001 nodes** のグラフを生成した。これは証明の定理数とは別の件数である。
- CIが要求する3定理を確認し、Astra全16原稿の **210定理・263名前付き宣言**すべてが正しい原本へ帰属することを確認した。文脈と末尾の監査用メタコードは原本に帰属させない。

関連テストは次のコマンドで再実行できる。

```bash
python -B -X utf8 -m unittest discover -s tests -p 'test_deps*.py' -v
python -B -X utf8 -m unittest discover -s tests -v
```

CIの実抽出データによる再解析と独立レビューは、Lean証明の再実行とは別の検査である。CIでは修正版の head について、証明・公理監査から依存関係解析までの通常の全手順を改めて実行する。

失敗時のZIPは SHA-256 `34fd5bf67d8b9f1d19bf92c1dc180f4728977a1240a3d32c8e1ccf9b6cc85785`、修正後に保存データから作ったグラフは `e7ec288bcf46f697159947f2183436bd32b4ce7ac6002cad2a4686a509063c09`。原記録は作業用 checkout 隣の `evidence/finite_flow_20261109/finish_20261110/` に保存する。元の [有限系の検証記録](verification-finite-flow.md) は対象コミットを固定した過去の記録として保持する。
