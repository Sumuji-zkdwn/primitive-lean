# 空間モード一様評価と連続体極限の検証記録

2026-11-09 UTC（日本時間2026-11-10）に、実装コミット `c7d55609d3a1038ad4e1d56b425952adc9030ffd` を固定し、未変更の作業ツリーから `python -B -X utf8 tools/verify.py --integration-only --rebuild` を実行した。全25段階の結果と、検査した入力・ログのSHA-256を [validation-continuum.json](validation-continuum.json) に保存する。前段の [有限系の記録](verification-finite-flow.md) と初回の記録は変更していない。

## 証明した結論と条件

[連続体極限の説明](continuum-limit.md)に対応し、共通の指数重み付き初期係数クラスから構成した実際の非粘性 Maxwell 場へ、正しい Fourier–Galerkin 近似と分割反復を接続する。初期条件は、共役対称性、重み付き係数ノルム `≤57/250`、`0≤T≤1/5`。解や尾部評価を入力仮定にしない。背景は `D=4/3,E=1,H=3/10` である。

全 `N`、全 `t∈[0,T]` について、厳密 Galerkin 流れの復元後の誤差は `2 exp(−3(N+1)/20)` 以下となる。時間分割の定数 `C_N(T,r)=(3/2)N²T²r exp(NT)` はモード数に依存するため、区間全体に共通の `n_N=max(N+1,ceil(C_N(T,‖z₀‖)(N+1)))` を選ぶ。有限公式の誤差は `2 exp(−3(N+1)/20)+1/(N+1)` 以下で、閉時間区間に一様にゼロへ収束する。物性則と実PDEは、極限として復元する同じ場について導出する。PDEの微分等式は開区間 `0<t<T`、初期到達と一様収束は閉区間で扱う。

材料作用は空間上の `g(D)` を射影した `P_N(g(D))` である。Fourier係数ごとに `g` を適用する有限模型との混同はしない。具体的な非定数の混合波 `D₀=4/3+cos(x)/25`、`H₀=3/10+3sin(x)/100` が同じ構成の入力条件を満たすことも証明する。

## 検証結果

| 検査 | 結果 |
|---|---|
| 今回の追加 | 58原稿・681定理・927名前付き宣言 |
| 追加内訳 | 原本57原稿が658定理・890宣言、新規接続が23定理・37宣言 |
| Astra累計 | 74原稿・891定理・1,190名前付き宣言 |
| 共通 Lean 検証 | 3,411定理・4,617名前付き宣言、`--trust=0`、project buildを再構築 |
| 公理監査 | 標準の `propext`・`Classical.choice`・`Quot.sound` のみ |
| Astra環境全体 | 1,887宣言を監査。source headerの1,225宣言との照合に再利用35宣言を含む |
| 実際の証明項の参照 | 43 nodes・58 direct referencesがすべて一致 |
| 原本・登録監査 | 76原本、376 retained files、197 supplement groups |
| リポジトリ unittest | 222件成功 |
| CI指定の別枠 pytest | 27ファイル、128件成功。unittestとの対象の重複を含む |
| 有限検算 | 16本成功 |
| ARC3オフライン検査 | 173 passed、8 skipped、3 subtests passed。ゲームの再実行なし |
| 独立 Lean 検査 | MovingCurveの核・公理監査、Okanohara bridge、FiniteMarkov transportが成功 |
| 固定依存 | mathlibを含む9パッケージが固定revisionと一致 |
| エラー・警告・禁止記法・想定外公理・入力変更 | すべて0 |

定理数は source headerのtheorem/lemmaの数である。名前付きinstanceと構造体は名前付き宣言数に含め、Propを返すinstanceがkernel内でtheoremとして表現されてもsource定理数には加算しない。構造体のconstructor・recursorや自動生成された補助定理は、別の環境全体の公理監査に含める。共通原稿の3,411／4,617へ独立モジュールを足して、リポジトリ全体の件数とは呼ばない。

## 組み立て文脈と失敗記録

元の57原稿はコミット `51a49be2e8f8b440c891240b574fdf97e08b9e84` のGit blobと照合し、そのまま保存した。追補への変換は `import` 行の除去だけである。新規接続 `AstraContinuumLimit.inc` は別の役割として登録し、SHA-256は `787e414e6718b3b7edfc434ed6b60136161bbfeb17a90d5f5adc7c7758cd4de7`。

最初の結合試験では、原稿を連結した際の `open` と `set_option` の漏出により、`polynomial`・`tendsto_atTop`・`extend` の解決が変わった。さらに `backward.isDefEq.respectTransparency=false` の漏出が、後続証明の末尾 `rfl` に未使用・未実行の警告を生じさせた。同じ原本とimportsで、オプションだけを切り替える比較により原因を確認した。

修復では原稿の外側に固定のsectionを置いてファイル単位のスコープを再現し、13原稿について元のEOFで暗黙に閉じるsectionの終了を明示した。二つの名前は元の宣言を対象namespace内へexportした。既存のHilbertFlow contextを含めて60個のcontextを固定allowlistで検査する。原本・adapter・nativeの証明本文は変更せず、linterの無効化も行っていない。追加の行を原稿の宣言位置へ誤帰属させない回帰試験も追加した。

その後の全197追補の個別結合試験は、340.778秒、Lean exit 0、エラー・警告0で終了した。ただし実行中の検証器の変更と、Prop-valued instanceを一律definitionと期待したPython監査の不備により、その試験の総合reportはfalseのまま保存した。修正した監査器による同じログの再解析は別の証拠とした。上表は、それとは別に、実装をcommitしてから実行した通常入口のfresh clean rebuildに基づく。

## 出典・復元・再実行の範囲

検証ログと全入力は作業用checkoutの隣の `evidence/continuum_20261110/final_integration_run/` に保存する。原本側の停止中Phase10作業には変更を加えていない。原本・adapter・native・契約のバイト一致を検査し、通常のテキストファイルに残るWindows改行とGit blobの改行差は別に記録する。ローカルの入力hashは実際に検査したバイト列のものであり、リモートCIではコミットからcheckoutした入力を別に検査する。

canonical本文§8.19と検証案内を更新し、同じrendererとローカル依存で3ページを再生成した。本文1,266数式、案内48、旧入口0。既存数式の脱落、KaTeX error、重複anchor、フォント参照の欠落はない。これは静的render検査であり、ブラウザーの画像による外観確認ではない。HTMLは既存の生成物として扱い、mainにはMarkdownとrendererを保持する。

```bash
python -B -X utf8 tools/check_astra_physics.py
python -B -X utf8 tools/verify.py --integration-only --rebuild
```

Lean `v4.30.0-rc2` と mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を使う。今回のローカル環境はWindows、Python3.14.5、pytest9.2.0、NumPy2.5.4。記録追加だけの後続commitでは、検査済みの証明入力hashが変わっていないことを再確認する。

任意の滑らかな大初期値、衝撃波後、一般PDE一意性、一般の粘性ゼロ極限、全モードのKoopmanスペクトル射影の一様収束は、この記録の結論ではない。厳密な非線形Fourier射影の求積・丸め誤差も別に残る。PRとmainのCI、およびダウンロードした証拠artifactの検査は、ローカル結果とは分けて最終配布記録に保存する。

