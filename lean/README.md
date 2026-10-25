# エラスティカのLeanライブラリ

曲線と一般密度の変分、拘束付き局所最小、再構成、相似・応答の証明を保持します。本文と利用・検証入口は [原始の形式化](../原始の形式化.html) に統合しました。

```lean
import Elastica
#check Elastica.locallyMinimizing_necessary_conditions
```

このフォルダーで `lake build Elastica` を実行します。線形入力・面積拘束・帰還系の証明は [linear_input/lean_check](../linear_input/lean_check/README.md) が担当し、既存ライブラリをimportして結合検査します。

上位フォルダーから `python -X utf8 tools/verify.py --rebuild` を実行すると、両側のLean証明、数値検算、統合本文の描画とリンク・出典確認をまとめて実行できます。Leanとmathlibの固定版、既存の証明原稿と定理名は変更していません。

[全体の定理対応と条件](../検証と再実行.html)、[両側のLean検査概要](../verification/lean.json)を参照してください。
