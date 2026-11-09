# 有限系の存在・一意性と分割反復の検証記録

2026-11-09 UTC（日本時間 2026-11-10）に、実装コミット **`102af117a7334861645e9300e9538b387335d81c`** を未変更の作業ツリーから検査した。`python -B -X utf8 tools/verify.py --integration-only --rebuild` は **25 段階すべて成功**した。機械可読の結果と入力・ログの SHA-256 は [validation-finite-flow.json](validation-finite-flow.json) に保存する。

この記録を追加するコミットでは証明・検証器を変更しない。検査対象の **233 入力**（生成原稿・基礎検証レポートを含む）のハッシュは、記録追加の際にも一致を確認する。生成レポートには実行時間が含まれるため、後日の再実行ではレポート自体のハッシュは変わり得る。[初回の記録](verification.md)と [validation.json](validation.json) は、前回の検査対象を示す過去の記録として保持する。

## 導入して検証した結論

固定した有限実行列 Q について、実際の材料逆関数 `g(D)=2 sinh(asinh(3D/2)/3)` を成分ごとに用いた系

```text
D' = −QH
H' = −Qg(D)
```

の全実時間の解の存在・一意性を証明した。前回の `ExactShear.lieStep` と同じ更新が解析側の分割式に一致することを証明し、T≥0、n>0 に対する評価

```text
||S_(T/n)^n(z) − Φ_T(z)||₂
  ≤ (3/2) ||Q||₂→₂² T² ||z||₂ exp(||Q||₂→₂ T) / n
```

を接続した。初期ノルムは D,H の成分二乗和による Euclidean norm であり、初期の E,H norm ではない。`restore(D,H)=(g(D),H)` が1-Lipschitzであることから、復元後にも同じ右辺の評価と収束が成り立つ。

構成した解の実際の微分から、復元した E,H が `Eᵢ'=−(QH)ᵢ/(1+Eᵢ²)`、`Hᵢ'=−(QE)ᵢ` を満たすことも証明した。Q が反対称である場合に、既存のエネルギー保存定理をこの解へ適用した。存在・一意性・反復収束には Q の反対称性を要求しない。定理名と仮定の対応は [有限系の説明](finite-flow.md) にある。

## 実行結果

| 検査 | 結果 |
|---|---|
| 今回の追加 | **6 原稿・84 定理・109 名前付き宣言** |
| 追加の内訳 | 原本からの5原稿が50定理・58宣言、新規の有限系接続が34定理・51宣言 |
| Astra の累計 | **16 原稿・210 定理・263 名前付き宣言**。既存29定理の再利用は追加数に含めない |
| 共通 Lean 検証 | **2,730 定理・3,690 名前付き宣言**、`--trust=0`、project build を削除して再構築 |
| 公理監査 | 既存の公理集合と一致。`propext`・`Classical.choice`・`Quot.sound` のみ |
| 警告・エラー・禁止記法・想定外公理・検査中の入力変更 | すべて0 |
| 固定依存 | mathlib を含む9パッケージのリビジョン一致 |
| 証明値内の再利用 | elaborated proof value 内の **25 定理・29 直接参照**を確認 |
| 原本・登録監査 | **260 retained files / 139 supplement groups**。Astra の19原本は source commit の Git blob と一致 |
| リポジトリ unittest | **174 件成功**。Astra の27検査を含む |
| CI 指定の別枠 pytest | 27ファイル、**128 件成功**。対象が重なるため unittest と合算しない |
| 有限検算 | 16本成功 |
| ARC3 オフライン検査 | 173 passed、8 skipped、3 subtests passed。ゲーム再実行なし |
| 独立 Lean モジュール | MovingCurve の核検査・公理監査、Okanohara bridge、FiniteMarkov transport が成功 |

2,730 / 3,690 は共通原稿の件数であり、独立モジュールや自動生成された補助宣言を加算したリポジトリ全体の件数ではない。直接参照の検査は今回の証明値が対象定理を使用していることを確認するもので、論理的な依存の不可避性を主張するものではない。

原本側の commit は `51a49be2e8f8b440c891240b574fdf97e08b9e84`。15 adapters は import 行だけを除去した原本とバイト単位で一致する。新規に書いた [AstraFiniteFlow.inc](../../linear_input/lean_check/AstraFiniteFlow.inc) は別の役割として台帳に登録しており、その SHA-256 は `ce141d5d9e3713e23c1608c04e4a05be2b092b87100c6e65ebf9fc57abdce2a4`。

独立した focused compile でも core と有限系接続を検査し、許可公理・証明参照・警告なしを確認した。説明文と実際の定理の仮定・定数は別のレビューでも照合した。これらに加えて、上記の全体クリーンビルドを実行している。

## 名前衝突による失敗と修復

最初の全体実行（`3b7bcd0e7964a6dbeda8dc7e219926ce380f189b`）では、既存原稿の namespace 外にある `open Finset` によって、後から連結した HilbertFlow の未修飾 `piecewise` と `union_comm` が曖昧になった。単独検査の成功を統合成功とは扱わず、この全体実行を失敗として保存した。失敗時の elaboration から後続定理へ伝わった `sorryAx` も、公理監査が拒否した。

修正は原本や proof adapter の変更ではなく、組み立て時に次の名前を明示することに限定した。

```lean
namespace KerrKoopman.HilbertFlow
export Set (piecewise union_comm)
end KerrKoopman.HilbertFlow
```

これは既存の Set 宣言への namespace 付き alias を登録する。新しい constant・theorem・axiom は作らない。alias は section を閉じても登録が残るため、適用先の namespace と対象ファイルを限定している。固定 allowlist 以外の context、任意コード、別ファイルへの適用、重複、必要な context の欠落は検証器と negative tests が拒否する。

失敗時から **15 adapters と native proof の全16ファイルは同じバイト列のまま**である。Finset が開かれた条件を再現した試験と、修正後の全体検証の両方を通した。失敗記録、修正候補の試験、成功した最終実行は、作業用 checkout の隣の `evidence/finite_flow_20261109/` に分けて保持している。機械可読記録にはそれらのハッシュも保存する。

## 再実行と本文

Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持する。今回のローカル環境は Windows、Python 3.14.5、pytest 9.2.0、NumPy 2.5.4。

```bash
python -B -X utf8 tools/check_astra_physics.py
python -B -X utf8 tools/verify.py --integration-only --rebuild
```

依存準備は [README](../../README.md) を参照。Windows の新しい checkout では `core.autocrlf=false` と保存原本の `-text` 属性を保持する。

canonical 本文 §8.18 と検証案内を更新し、既存 renderer で3ページを再生成した。本文の数式数は1,221から **1,236**、検証案内48、旧入口0。既存数式の脱落、KaTeX error、未展開 placeholder、重複 anchor、フォント参照の欠落はなかった。render 時点では未作成だった本検証記録へのリンクは、記録作成後に実在を確認した。ブラウザーのスクリーンショットによる外観確認は実施していない。

今回の結論は固定した有限 Q についてのもの。誤差定数は Q の作用素ノルムに依存するため、全空間モードに一様な収束や連続体 PDE の極限同定は別の課題である。また、存在定理から選んだ `noncomputable` な流れを、有限回で評価できる閉じた式とは扱わない。この記録が証明するのはローカルのソース・証明・検査の結果であり、リモート CI と main へのマージは別に確認する。
