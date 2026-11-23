# THEOREM ARCADE — 既存のLean形式化をゲームに使う

**スマホから遊ぶ:**
https://raw.githack.com/Sumuji-zkdwn/primitive-lean/main/games/theorem-arcade/index.html

以前の固定7手ルーターを置き換えるため、primitive-leanにすでに存在する数学的な仕組みから、操作可能な3つの実験室を構成しました。画面はスマホ用のHTML + JavaScriptで、Leanのソースを変更しません。

## 1. 砂山の双子 (Twin sandpiles)

- 8×8 wired square sandpile。両側に同じ粒を投入し、各セルで4粒以上なら上下左右に1粒ずつ送る。端から出た粒はsinkに消える。
- 出典: experiments/sandpile_laakso/formalization/ClockAvalancheExample.lean
- 既存Lean証明: ClockAvalancheExample.balanced_example
- 観測量: (phase mod 9, grouped short bit, grouped long bit)。2配置の観測が一致する具体例。
- Leanで確定した81回の2粒入力を再現すると、80回後の累積崩壊数は(95,95)、81回後は(95,158)。
- プレイヤーは好きなセルをタップできる。その自由入力で現れる他の模様や差は探索結果であり、同じ累積崩壊数の保証はない。

## 2. 空間をつなぐ (Signed Laakso first approximant)

- 実際の最初のLaakso近似の6頂点6辺。中央2本の平行辺を区別する。
- 2枚の層、12のlift頂点・12のlift辺。辺の符号反転をタップで変更できる。
- 頂点のゲージ切替は表示される接続符号を変えるが、中央閉路の偶奇は変えない。
- 出典: linear_input/lean_check/LaaksoSignedConnection.inc
- 既存Lean証明: untwisted_reachable_card、flipped_reachable_card、flipped_no_spin。
- ブラウザの有限検査では64の符号配置をすべて列挙し、中央の奇偶に対応する到達数6/12を確認する。
- ここでの任意符号配置に対する全列挙はJSの有限検査であり、Leanの一般定理であると主張しない。

## 3. 生命の規則 (Rule 481)

- 5セルのvon Neumann型二値局所規則。中心重み1、上下左右重み2、得点0/5/6/7/8で次状態1。
- 3×3 torus: 対称性・2周期がLeanで証明された有限模型。
- 17×17 torus: 同じ局所規則を大きな盤面で試す探索モード。長期挙動の証明は主張しない。
- 出典: linear_input/lean_check/Rule481Symmetry.inc
- 既存Lean証明: reflect_ns、complement、step_mirror、step_two_cycle。
- JavaScriptの全512個の3×3初期状態について反転と補数の操作の整合性を有限検査する。

## テスト

node --test games/theorem-arcade/engine.test.cjs games/theorem-arcade/ui.test.cjs

専用CI: .github/workflows/theorem-arcade.yml。入力の非退化・64符号の連結性・全512状態・81回の崩壊回数・UI起動とスマホ相当の操作をテストします。Leanソース内の宣言名も実際に照合します。

## 保証の境界

Lean証明は、引用したLean上の対象・仮定に対するものです。スマホのJavaScriptはLeanのカーネルではなく、これらの有限遷移の移植です。テスト済みの具体例・有限全列挙と、一般的なLean証明を混同しません。大量の既存定理から自動的にゲームを生成するコンパイラは、現時点では未実装です。

本サイトはindex.html、engine.js、ui.jsからなる静的サイトで、ビルドやユーザー登録は不要。GitHubのソース表示画面では動作せず、上記のraw.githack外部HTML表示サービスを通します。外部サービスの可用性は本リポジトリのCI検査対象外です。
