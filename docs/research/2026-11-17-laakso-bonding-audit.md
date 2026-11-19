# PR #142：段間互換性の独立検証

対象日：2026年11月17日（日本時間）。対象コミット：
`983fa7cffe88463e63fdacdcff1d6f989118a76e`。

対象は [Sumuji-zkdwn/primitive-lean PR #142](https://github.com/Sumuji-zkdwn/primitive-lean/pull/142)。
今回の読み取りでも head は上記 SHA、draft=true、merged=false だった。
この追加ブランチは上記のPR #142ヘッドから分岐する。既存PRのブランチとmainには変更・マージを行わない。以下の成功記録はローカルで実際に実行したもの。新規PRのGitHub Actionsとは区別する。

## 結果

**検証完了：Python有限全列挙はPASS。Lean 4.30.0-rc2 / 指定mathlibで、既存10ソースと追加補題の両方が `--trust=0`、終了コード0で型検査を通過した。追加の主要9定理について公理一覧を出力し、`sorryAx` が無いことを確認した。**

W1の古い頂点コピーは、第二段で更新してから `bonding 1` で戻すと W1 に留まる。
第一段のraw頂点を先に更新して観測すると W2 になる。
この違いは6頂点符号化の 4 と 5 の違いにとどまらず、既存の幾何的実現上の二点の不等式になる。

既存の更新から誘導される多価遷移を使っても、この不一致は残る。
W1における上段からの射影像は `{W1}`、下段の遷移先は `{W2}` である。
したがって、完全な一致だけでなく、上段の遷移が下段の許容遷移に含まれるという前向き健全性も破れる。

## 既存定義を接続する型

`G₀ = level 0 = base`、`G₁ = level 1 = refine base`、
`G₂ = level 2 = refine (level 1)` とする。

| 記号 | 実際の定義・型 | 大きさ |
|---|---|---:|
| R₁ | `RawVertex (Fin 2) (Fin 1)` | 8 |
| V₁ | `RefinedVertex (Fin 2) (Fin 1) = VertexType 1` | 6 |
| R₂ | `RawVertex (VertexType 1) (EdgeType 1)` | 36 |
| V₂ | `RefinedVertex (VertexType 1) (EdgeType 1) = VertexType 2` | 24 |
| q₁, q₂ | 各段の `rawProjection` | raw→観測頂点 |
| j₁, j₂ | `vertexPoint G₁`、`vertexPoint G₂` | 観測頂点→幾何的実現 |
| U₁, U₂ | `advanceRightGeneral G₀`、`advanceRightGeneral G₁` | raw→raw |
| p₁ | `bonding 1 = bond G₁` | `Space 2 → Space 1` |

追加定義 `realizeRaw n` は `vertexPoint (level (n+1)) ∘ rawProjection`。
追加定義 `oldCopy n r c` は `(Sum.inl (rawProjection r), c)`。
これは**観測された頂点**を次段へ持ち上げる操作で、忘れられた第一段のsheetを復元するraw射影の逆写像ではない。

第二段の古い頂点コピーには、既存の `bond_vertexPoint_old` から

\[
p_1(j_2(q_2(\operatorname{oldCopy}(r,c))))=j_1(q_1(r))
\]

が成り立つ。第二段で新しく作る接合点には、既存の `bond_vertexPoint_new` から

\[
p_1(j_2(\mathrm{inr}(e,k)))=
\operatorname{edgePoint}(G_1,e,(k+1)/3)
\]

が成り立つ。後者は親辺の内部であり、親の6頂点のいずれかへ無理に丸めてはいけない。
第二段24頂点の像は、親の6頂点と、6本のラベル付き辺それぞれの1/3・2/3点の計18点になる。
平行な二つの中間辺も別の辺として保持した。

## W1の具体例

第一段のraw頂点を `r_b = w1 b = (Sum.inr (0,0), b)`、
第二段のraw頂点を `x_{b,c} = oldCopy 0 (w1 b) c` とする。
`b,c : Bool` のどの組でも同じ結論になる。

| 経路 | 実際の計算 | 第一段の符号 |
|---|---|---:|
| 第二段を更新→観測→幾何的射影 | `p₁(j₂(q₂(U₂(x)))) = j₁(W1)` | 4 |
| 第一段raw頂点を更新→観測→幾何的実現 | `j₁(q₁(U₁(r_b))) = j₁(W2)` | 5 |

`U₂` は全ての古いraw頂点を固定する。一方、`U₁(w1 b) = w2 b`。
`vertexPoint_injective G₁` により、W1とW2は幾何的実現上でも異なる。

`U₁` は観測商全体の決定的更新へ降りないため、未定義の幾何的更新を使った
`p₁ ∘ U₂ = U₁ ∘ p₁` をそのまま定理文にすることはできない。
追加補題は、上記の**型の合う二経路**の不等式を証明する。
これは段間半共役に必要な整合性の破れであり、W2内部のsheet同一視だけを扱う
`first_no_deterministic_quotient` とは別の障害である。

## 多価遷移でも元の規則のままでは直らない

幾何的頂点上の遷移を、既存の `relStep` をそのまま使って

\[
F_i(z)=\{j_i(q_i(U_i(r)))\mid j_i(q_i(r))=z\}
\]

と定義する。追加コードでは `vertexStep 0` が F₁、`vertexStep 1` が F₂。
頂点以外を入力したときは空集合であり、幾何的実現全体の全域的な力学を作ったわけではない。

第二段のW1の古いコピーを幾何的に埋め込んだ点を z とすると、

\[
p_1[F_2(z)]=\{j_1(W1)\},\qquad
F_1(p_1(z))=\{j_1(W2)\}.
\]

よって `p₁[F₂(z)] ⊆ F₁(p₁(z))` さえ成立しない。
上段の自己ループ z→z を残したまま選択肢を追加しても、そのW1出力が残るので修復できない。
下段の規則も変えるか、上段の自己ループを取り除く必要がある。

## 規則を変更する場合の有限修復

全射 `p : X → Y` と下段関係 `R : Y → Set Y` に対し、

\[
\widehat R(x)=\{x'\mid p(x')\in R(p(x))\}
\quad\Longrightarrow\quad
p[\widehat R(x)]=R(p(x)).
\]

この一段の集合等式は一般の全射について証明できる。
有限模型では `X = V₁ × Bool`（12個の古い頂点コピー）、`p = Prod.fst`、
`R = relStep firstRead advanceRight` に適用した。
12入力すべてで等式が成立し、関係の矢印は28本ある。
W1コピーは二つのW2コピーへ、W2コピーは二つの右端点それぞれの二つのコピーへ進む。

これは `advanceRightGeneral` の検証結果を変更するものではなく、**別の上段関係の構成**である。
W1・W2で元の自己ループは失われる。また、W1古頂点→W2古頂点は第二段の単一辺ではない。
したがって、元の「一回の更新は特定の隣接辺をたどる」という性質もそのまま保存する修復ではない。

実際の `bonding 1` は既に全射なので、同じ構成を幾何的実現上の関係にも適用できる。
ただし頂点にしか遷移を定めない R を使えば、親の辺内部へ射影される入力で遷移は空になる。
この一段の集合等式は、全域性、連続性、経路の持ち上げ、全段での同時選択、逆極限上の力学を含意しない。

## 検証と追加補題

`tools/check_laakso_bonding_finite.py` は標準ライブラリだけを使い、有限集合を全列挙し、有理座標に `Fraction` を使う。
第一段raw状態×追加sheetの16通りでは8通りが不一致。
同一観測をまとめた古い頂点コピー12通りでは4通りが不一致で、W1・W2の各2コピーに一致する。
Python結果は `finite-results.json` に記録した。

保存したローカル結果は `docs/verification/2026-11-17-laakso-bonding/` 内の `lean-results.json`、`Upstream.log`、`LaaksoBondingAudit.log` を参照。
`tools/check_laakso_bonding.py` はPRコミットの13入力（10ソースと3依存設定）をGit blob SHAで照合し、10個の `.inc` を全文・無変更で結合する。新規証明は `linear_input/lean_check/LaaksoBondingAudit.inc` に置き、生成時に `import Upstream` を付ける。
比較用の同型な模型に置き換えてはいない。
結合用ファイルでは必要なmathlibモジュールを明示的にimportした。元の `.inc` 内の定義・証明には手を加えていない。
各実行の時間と生成ソースのSHA-256は保存したJSONに記録する。依存取得・過去の失敗した試行の時間とは区別する。
公理一覧に現れたのは `propext`、`Classical.choice`、`Quot.sound` のみで、独自公理や `sorryAx` は無い。

| 追加補題 | 役割 |
|---|---|
| `bonding_oldCopy` / `bonding_newRaw` | raw・観測頂点・実際の幾何的射影を接続 |
| `first_second_noncommutes` | 指定された第一段・第二段のW1反例 |
| `inherited_w1_noncommutes` | 任意の有限段 n・親辺 e で同じ障害を示す |
| `first_w1_outputs` / `projected_second_w1_outputs` | 二つの遷移先集合をそれぞれ計算 |
| `canonical_relations_not_forward_sound` | 元の規則の多価化でも前向き健全性が破れる |
| `cannot_keep_old_stop` | 自己ループを残す追加だけでは修復できない |
| `pullbackStep_exact` | 全射に沿う別の多価関係の一段互換性 |
| `inherited_relation_repair` | 12個の古いコピー全体での有限修復 |
| `bonding_relation_repair` | 実際のbondingを使った一段の関係等式 |

上の一般化のうち `inherited_w1_noncommutes` と `pullbackStep_exact` は追加Leanコードの検査対象であり、
Pythonの二段検算だけから一般化したものではない。

## 既存の証明との区別

- 既存：`rawProjection` の商としての性質、幾何的頂点の単射性、`bonding` の連続性・全射性、`Tower` の構成。
- 既存：`laakso_every_level_delayed_split`、一段内の `first_no_deterministic_quotient`、第一段の全有限時刻での多価観測の正確さ。
- 今回：実際の `bonding` に接続したW1非可換性、多価化後にも残る不整合、別の関係を選んだ場合の一段修復。
- 未証明・非主張：元の更新から生じる連続Laakso空間上の流れ、逆極限上の力学、連続時間極限、修復関係の連続性・閉グラフ性・全域的な全段整合性。

## 再実行

リポジトリの `lean/lean-toolchain` と `lean/lake-manifest.json` に一致する依存を用意し、ルートから実行する。

```bash
python3 tools/check_laakso_bonding_finite.py --output /tmp/laakso-bonding/finite-results.json
python3 tools/check_laakso_bonding.py --output-dir /tmp/laakso-bonding
```

`--lean /path/to/lean` と `--packages /path/to/.lake/packages` で既存の検証環境も指定できる。
検証器はLean 4.30.0-rc2、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` および依存パッケージのSHAを照合し、
`--trust=0` で既存ソースと追加補題を順に型検査する。生成ファイル・ログ・JSONは指定した出力ディレクトリにのみ書き込む。
主要9定理の公理一覧も出力する。`--assemble-only` はソース照合と生成だけを実行し、型検査の成功とは扱わない。

専用Actionsは `.github/workflows/laakso-bonding-audit.yml`。PRの実際のheadをcheckoutし、有限検算と型検査を実行する。
既存の統合検証入口 `tools/verify.py` は変更しない。

## 固定コミットの出典

- [LaaksoFiniteGraph.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/983fa7cffe88463e63fdacdcff1d6f989118a76e/linear_input/lean_check/LaaksoFiniteGraph.inc)
- [LaaksoRealization.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/983fa7cffe88463e63fdacdcff1d6f989118a76e/linear_input/lean_check/LaaksoRealization.inc)
- [LaaksoGeometricProjection.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/983fa7cffe88463e63fdacdcff1d6f989118a76e/linear_input/lean_check/LaaksoGeometricProjection.inc)
- [LaaksoGeometricTower.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/983fa7cffe88463e63fdacdcff1d6f989118a76e/linear_input/lean_check/LaaksoGeometricTower.inc)
- [LaaksoVoidRelationalBridge.inc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/983fa7cffe88463e63fdacdcff1d6f989118a76e/linear_input/lean_check/LaaksoVoidRelationalBridge.inc)
