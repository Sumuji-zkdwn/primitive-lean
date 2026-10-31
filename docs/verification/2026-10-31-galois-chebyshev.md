# ガロア・円分・クンマー接続: 最小追補の記録

作成日: 2026-10-31
対象: chatgpt/galois-chebyshev-20261031（codex/primitive-history-derivation-20261029 から分岐）。

**重要: この追補のLeanコンパイルおよび公理監査は未実施。** 既存の733定理・861宣言の検証結果を、この追加が通過した証拠として使わない。

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

## 未実装・未検証

- 任意のnでの複素反復 T_(3^n) と J(z^(3^n)) の公式。
- 複素ラベルの網羅性・重複と、Fin/ZModの具体的な同型。
- Galois群 Gal(C(y)(T_(3^n)^−1(y))/C(y)) と二面体群の同型。
- Q(y) 上の算術的ガロア群、円分自己同型を含む記述。
- 拡大体の実体、既存 mathlib.FieldTheory.KummerExtension の一般定理への適用。
- 本ブランチでのLean実機検査と統合公理監査。

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
