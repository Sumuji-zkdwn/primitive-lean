# 追加列による解釈更新と計算予算

2026年11月21日。基準は `main` の
`8ed4c9347609ff350f947da7e44101abcd993ed9`。

短い追加列で、過去の記号の現在の読み方を変える構想を扱う。
その際に、以前の要約が使えなくなる条件、保存した候補や計算結果の再利用、
特定の照会予算でどこまで正答できるかを区別する。

**後から必要になる区別を捨てた要約では、新しい読出しに答えられない。**
一方、公開の追加列だけで、保存済みの原記録・候補・計算結果を相手から消すことはできない。
この両側を、一般的な補題、反例、有限計算へ落とした追加である。

## 読む順序

1. [第1段階：要約・候補・情報量の境界](retroactive-translation-stage1.md)
2. [第2段階：照会予算の最適正答率と反復二乗](retroactive-translation-stage2.md)
3. [有限検算と再実行](../../experiments/retroactive_translation/README.md)
4. [実際の検証記録](../verification/2026-11-21-retroactive-translation.md)

## 形式化した範囲

Leanファイルは2本。本文のすべてを形式化したわけではなく、以下の対応を固定する。
各宣言の正確な型と仮定はリンク先のソースを参照する。

### 要約・未来の読出し・公開更新

[`lean/Research/RetroactiveTranslation.lean`](../../lean/Research/RetroactiveTranslation.lean)
の名前空間は `Elastica.RetroactiveTranslation`。16定理。

| 本文の主張 | Lean宣言 | 仮定と範囲 |
|---|---|---|
| 新しい読出しが旧要約から復元できる必要十分条件 | `factors_through_reached_iff_fiber_constant` | 到達した像上のdecoder。有限性、元の終域への全射、終域の非空性は不要 |
| 復元可能なdecoderは到達した像上で一意 | `reached_decoder_unique` | 各入力での復元一致 |
| 旧要約が潰した区別を新読出しが要求すると復元不可 | `collision_prevents_decoder` | 同じ要約・異なる新読出しを持つ二状態 |
| 二ビットの第1座標だけでは第2座標を復元できない | `second_coordinate_not_from_first` | `Bool × Bool` の具体的反例 |
| 許された全未来読出しに十分な要約の条件 | `all_future_decoders_iff` | 読出し族を固定。旧要約の各fiber内で全回答が一致 |
| 全座標を後から読める要約は単射 | `coordinate_decoders_force_injective` | 任意の関数型入力に対する正確な座標decoder |
| dビット全入力に対応する要約には少なくとも2^d状態が必要 | `bit_summary_card_lower_bound` | 有限の要約型。記憶状態数の下界であって時間下界ではない |
| 蓄積観測は固定した候補集合を減らす | `candidates_append`, `candidates_antitone`, `candidates_append_subset`, `discarded_key_stays_discarded` | 時刻・版を含めた固定の整合条件を保持 |
| 固定読出しの候補も増えない | `fixed_reading_candidates_append_subset` | 比較する読出しそのものを途中で変更しない |
| 初期鍵と公開更新で状態軌道が一意に決まる | `public_state_unique`, `public_states_eq_of_initial_eq` | 決定的更新。新たな未知の私的入力を加えない |
| 現在状態が分かれば、その後の公開更新に追随できる | `public_states_future_of_equal_current`, `public_state_suffix` | 完全な現在状態が一致していること。過去prefixの再生は不要 |

中心となる条件は、`P : X → A` と `Q : X → B` に対して

\[
\exists h:P(X)\to B,\quad Q=h\circ P
\quad\Longleftrightarrow\quad
\forall x,y,\ P(x)=P(y)\Rightarrow Q(x)=Q(y).
\]

像 `P(X)` に制限することで、到達しないラベルへdecoderを延長する余計な仮定を避ける。
未来の読出しをすべて座標評価にすると、残すべき区別が全入力の区別になり、
有限状態数の下界へつながる。

### 照会予算と反復二乗

[`lean/Research/RetroactiveWorkBounds.lean`](../../lean/Research/RetroactiveWorkBounds.lean)
の名前空間は `RetroactiveWorkBounds`。12定理。

| 本文の主張 | Lean宣言 | 仮定と範囲 |
|---|---|---|
| 準備済み列は元の列集合に含まれる | `coveredColumns_subset`, `coveredColumns_card_le` | 有限列集合と非負整数の既読セル数 |
| 閾値d以上を読んだ列数×dは事前予算以下 | `coveredColumns_card_mul_le_budget` | 全列の既読セル数の和がp以下。d=0も含む |
| 正閾値での列数上限 | `coveredColumns_card_le_div`, `coveredColumns_card_le_min` | d>0。`min(M, p / d)` が上限 |
| N−qビット以上を事前に読めた列数の上限 | `readyColumns_card_le_min` | q<N。確率的な未読セルの性質はこの補題に含まない |
| 確実性の予算式の自然数上の書換え | `certainty_budget_iff` | q≤Nで `M*(N-q)≤p ↔ N*M≤p+M*q`。戦略の最適性自体は仮定していない |
| 反復二乗の初期値と一段更新 | `repeatedSquare_zero`, `repeatedSquare_succ` | 任意のMonoidにおける `a^(2^T)` |
| 既計算値からの差分更新 | `repeatedSquare_add` | `z_(T+δ)(a)=z_δ(z_T(a))`。最適な計算時間の主張は含まない |
| 関連した基点の結果の再利用 | `repeatedSquare_pow` | 任意のMonoidで `z_T(a^r)=z_T(a)^r` |
| 基点の積からの再利用 | `repeatedSquare_mul` | 追加で可換Monoidを仮定 |

この形式化は、RSA型の特定の法に依存しない代数的な再利用等式を扱う。
因数分解の秘密から指数を減らすEulerの定理の適用は、研究ノートの説明と
全34,580組の有限算術検算の対象であり、この追加Leanファイルの定理ではない。

## 手証明・有限検算・未証明の区別

独立な公平ビットからなるN行M列表で、各実行枝の事前照会数をp以下、
独立一様な列指定後の照会数をq以下に制限すると、最適正答率は

\[
P^*_{\mathrm{succ}}=
\begin{cases}
\frac12+\dfrac{\min(M,\lfloor p/(N-q)\rfloor)}{2M},&q<N,\\[4pt]
1,&q\ge N.
\end{cases}
\]

N,M≥1を仮定する。この式の上界・達成戦略は第2段階で手証明した。
Leanで形式化したのは、そのうちの**決定的な列数上界と自然数の予算式**である。
適応的な観測履歴に条件づけた未読ビットの独立性や、確率戦略全体の最適性まで
Leanで検証したという意味ではない。

| 項目 | この追加での扱い |
|---|---|
| 要約の因子化・座標照会の状態数下界・候補縮小 | 上記Lean定理と小規模全列挙 |
| パリティ照会の一般最適正答率 | 手証明＋独立DP・全表方策再生。確率論部分は未形式化 |
| 情報エントロピーの一般不等式 | 既存理論の参照と本文の議論。Lean未形式化 |
| 置換の履歴数と最終写像数、秘密表、事後解釈反転 | 独立した有限検算 |
| 反復二乗の再利用 | 抽象代数のLean定理＋小さな法での全例検算 |
| 一般攻撃者に対する逐次時間・実時間の下界 | 証明していない |
| 新規暗号の意味的安全性、任意平文の送信機能 | 構成・証明していない |

期待照会数と各枝の最大照会数は異なる。期待予算の反例を同梱した。
また、単発の照会費用を更新回数だけ掛けることはできない。
既に読んだビット、完成したパリティ、既に進めた反復計算は再利用できる。

## 既存研究との接点

mainの観測商・予測商は、区別を残す観測と潰す観測を扱っている。
今回の一般因子化もこの見方に接続するが、曲線・エネルギー・流体の性質を仮定していない。
解析的な依存を持ち込まないように独立した型・写像の補題として実装した。

[PR #170](https://github.com/Sumuji-zkdwn/primitive-lean/pull/170)の
`ForgettingRoundTrips` にある具体的な復元不能例と主題が重なる。
その関係合成の定義や未統合モジュールへのimportは追加していない。
PR #169/#170の変更をこのブランチへ一括で取り込むこともしていない。

暗号理論・時間鍵・INDEX等の一次資料は両研究ノートの出典一覧にまとめた。
この追加は新規暗号の提案としての優先性を主張するものではなく、
構想の成立条件と反例を再利用できる形で保存するためのものになる。

## 検証の入口

固定のLean・mathlib環境を準備したうえで、リポジトリのルートから実行する。

```bash
python3 -B -X utf8 tools/verify.py --retroactive-translation-only
```

この入口は4本の有限検証器を一時ディレクトリで再実行し、保存した4個のJSONと照合する。
続けて2つのLeanモジュールを新たに `--trust=0` でコンパイルし、
ローカル定理すべての公理依存を監査する。許可公理は既存方針と同じ
`propext`・`Classical.choice`・`Quot.sound` のみ。

`tools/verify.py --integration-only` にも同じ入口を登録した。
専用workflowはPRのhead SHAを確認してからこの検証を行い、結果をartifactに保存する。
全体の統合CIの成功と、この追加だけの成功は検証記録で区別する。
