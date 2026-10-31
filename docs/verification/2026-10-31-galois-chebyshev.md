# ガロア・円分・クンマー接続: 最小追補の記録

作成日: 2026-10-31
対象: chatgpt/galois-chebyshev-20261031（codex/primitive-history-derivation-20261029 から分岐）。

**検証完了 (2026-10-31): GitHub Actions 実行 #41207011344 で Lean 統合コンパイル・全宣言公理監査が成功。746定理・880宣言。** 元の733定理・861宣言は本追補を含まない別版の検証結果として保持する。

## 変更点

- linear_input/lean_check/GaloisChebyshev.inc: 6定義・13定理の代数的追補。
- 追加した代数写像は J(z)=(z+z⁻¹)/2、C(x)=4x³-3x。
- z≠0 で C(J(z))=J(z³) を示す証明原稿。
- a,b≠0 で J(a)=J(b) ⇔ a=b または ab=1 を示す因数分解の証明原稿。
- IsPrimitiveRoot ζ m から Polynomial.cyclotomic m ℂ の根が得られる橋渡し。
- ζ が原始m乗根、z^m=w のとき、(ζ^j z)^m=w となる候補の保存。
- ZMod m の巡回移動、二種の反転 j→−j と j→−j−1、その対合と共役関係。
- 既存の LinearInputF0.branchZero_kernel / branchPi_kernel と LinearInputBranchFibers.candidate_eq_zero_iff / candidate_eq_pi_iff に接続する同値定理。
- tools/verify_main_result.py の SUPPLEMENTS と tools/verify.py のスコープ登録。
- linear_input/verify_lean.py の合成入口に必要なmathlib importを追加。旧証明原稿は変更しない。
- tools/check_galois_bridge.py: Python標準ライブラリだけを用いる有限の有理数・合同式検算。

## 数学的成立条件

- Jの衝突定理は零を除く複素数で成り立つ。
- クンマー候補定理は原始根と z^m=w の存在を仮定する。
- ZModのラベル操作は有限の代数的置換であり、ガロア自己同型と同一視したわけではない。
- +1と−1の既存のFinラベルの等値判定は既存定理からの帰結であり、今回、新規の幾何的同一視を仮定していない。

## 今回の数学的範囲外

- 任意のnでの複素反復 T_(3^n) と J(z^(3^n)) の公式。
- 複素ラベルの網羅性・重複と、Fin/ZModの具体的な同型。
- Galois群 Gal(C(y)(T_(3^n)^−1(y))/C(y)) と二面体群の同型。
- Q(y) 上の算術的ガロア群、円分自己同型を含む記述。
- 拡大体の実体、既存 mathlib.FieldTheory.KummerExtension の一般定理への適用。
- 本追補を含むPR #3の `main` へのマージ。現時点ではPR #3はドラフトで、PR #5はPR #3へ統合済み。

## 固定版Leanでの統合検査成功（2026-10-31 追記）

- GitHub Actions: [Primitive Lean integration verification #41207011344](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41207011344)。
- 対象: PR #5 head \`0ee952740d35d0307c4eb382684d429f9517dba5\`。2026-10-31 13:50 UTC に成功成果物が保存され、同日 13:53 UTC にPR #5を \`codex/primitive-history-derivation-20261029\`（PR #3）へマージ。
- GitHub Actions 結果: \`completed / success\`。job \`Lean proofs and axiom audit\`、job ID \`124554050396\`。該当ジョブのPython有限検算・Lean統合・証拠アップロードは全て成功。
- 検証成果物: \`primitive-galois-lean-41207011344\`（artifact ID \`13045131208\`、84,741 bytes、アーカイブ SHA-256 \`36f7413ad73d1e855d6e3d8939105ea1e7fa896b93dbffa041b8b07241b9cd7b\`）。
- 実行環境: \`Lean 4.30.0-rc2\`（Linux x86_64）、mathlib commit \`5450b53e5ddc75d46418fabb605edbf36bd0beb6\`。固定した9依存リビジョンが検査前後とも全件一致。依存キャッシュ利用、クリーンビルドではない。
- \`python -B -X utf8 tools/verify.py --proof-only\`: \`passed = true\`、jointとsupplementalの終了コードはともに0。
- \`lake env lean --trust=0 ../linear_input/lean_check/MainResult.lean\`: 終了コード0。全746定理・880宣言、880宣言すべての公理監査が完了。\`propext\` / \`Classical.choice\` / \`Quot.sound\` 以外の公理0、未処理 \`sorryAx\` 0、警告0、エラー0、禁止トークン0、検査中のソース変更0。既存基線の公理依存も一致。
- 主要ファイルの保存ハッシュとマージ先ブランチの現行内容を再計算して一致を確認した（以下を参照）。旧Lean原稿・既存追補の本文を再定義していない。

\`\`\`text
GaloisChebyshev.inc     SHA-256 93d474a84e788001a23b26e16ba81e2417406a7b5cc08822ce573e09426c1f9d
F0MergeChains.inc       SHA-256 93a9fda3dd419f6e70c68c1cb99c8448b07a635c30264c146fa43f3201440f59
BranchFibers.inc        SHA-256 35630d8d6f7d65d16a5d81e35d5e8924be43b6a61f8ffe0593a5aa7b559b313a
verify_lean.py          SHA-256 cad63bbe60118974c3e5f92ba53ecb09fd25ea517e9a22f2417ac9f72d644f8c
verify_main_result.py   SHA-256 9dbcf6e6fbb9147e2e7ff8333c50f23d0c35d614f77139814d4b9ee1cfd8d93b
verify.py               SHA-256 2985cde8a513e4b1fcd28fdef781b6b3f7729dae28b453a7541af1e76a94c6dc
\`\`\`

これは保存ログ・GitHub Actionsメタデータ・ソースハッシュの照合であり、この対話の実行コンテナにLeanを新規インストールして再度フルビルドした結果ではない。歴史保存ZIP・描画・Kaggle実機の検査もこの範囲外である。


## 再実行方法

Pythonの有限検算（Leanの代わりではない）:

    python -B -X utf8 tools/check_galois_bridge.py

Lean固定版での統合証明・公理検査:

    python -B -X utf8 tools/verify.py --proof-only

成功条件: Lean --trust=0 が終了コード0、追加宣言を含む全宣言の公理監査が揃い、依存リビジョン一致、警告/禁止トークン/未承認公理なし。検証器が生成する監査結果はこの追補を初めて実行した時点で別途保存する。

## 参照先

- Mathlib.RingTheory.Polynomial.Cyclotomic.Roots: IsPrimitiveRoot.isRoot_cyclotomic
- Mathlib.RingTheory.Polynomial.Chebyshev: チェビシェフ合成の将来の橋渡し先
- Mathlib.FieldTheory.KummerExtension: 拡大体とGalois自己同型の将来の橋渡し先

MathlibのAPIは公開最新版とリポジトリの固定リビジョンで異なる可能性がある。固定したlean/lean-toolchainとlean/lake-manifest.jsonを変えずにコンパイルすること。
