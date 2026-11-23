# 第25回 遅延硬化エーテル模型・検証パッケージ

## 目的

二つの可逆的な内部場（位相場の簡略版 `q` と記憶場 `z`）を標準ADM重力へ最小結合したとき、計量–物質間のPoisson括弧の交差項が消え、狭い重力スライスで全制約に収束することを確認する。加えて、曲率への結合を正準変数の変更なしに付け加える反例を示す。

## 実行

Python 3.11以降、numpy, sympy, matplotlib。

```bash
python verify_v25.py
python independent_audit_v25.py
```

`verify_v25.py` は全計算を再実行し、`audit_v25.json`、CSV、PNGを更新します。`independent_audit_v25.py` は前者をインポートせずに別の記号計算とFFT検査を行います。

## 主な結果

- 一般の対角計量背景における重力–物質交差項の和は厳密に0。
- 背景平坦・一方向空間依存・曲率一次変分の有限検査で、拘束誤差は256点で`1.378e-6`、512点で`3.456e-7`。
- 最小格子の正準偏微分と独立に導いた離散ブラケットの差は`5.56e-10`。
- 素朴な `λ q √γ R` の後付けは、運動量拘束ゼロの配置でも `3π/50` の非零括弧を生む。

## ファイル

- `RESEARCH_NOTE_2026-11-23_v25.md`：日本語研究記録。定義・導出・厳密反例・結果・限界。
- `verify_v25.py` / `independent_audit_v25.py`：二つの独立した検証プログラム。
- `audit_v25.json` / `independent_audit_v25.json`：監査サマリー。
- `full_bracket_convergence_v25.csv`：重力部分、物質部分、合計の格子収束。
- `nonminimal_counterexample_v25.csv`：曲率結合反例の格子収束。
- `nonminimal_strength_scan_v25.csv`：反例の結合強度依存。
- `full_constraint_convergence_v25.png`：全括弧の誤差収束。
- `mixed_terms_cancel_v25.png`：最小結合交差項の相殺。
- `nonminimal_constraint_failure_v25.png`：曲率結合反例。
- `SHA256SUMS.txt`：パッケージ内ファイルの検算値。

## 範囲の制限

標準Einstein–Hilbert重力の運動項と曲率項を仮定しています。非平坦・非線形の一般的な三次元計量について全制約を直接数値実装したわけではありません。内部場は可逆的であり、実際の散逸粘弾性ではありません。重力の創発も未証明です。
