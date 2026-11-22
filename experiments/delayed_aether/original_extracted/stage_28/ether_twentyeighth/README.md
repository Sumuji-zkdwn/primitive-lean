# 第28回：非対角計量・二偏極・遅延硬化

2026年11月23日。既存のスカラー・テンソル共変重力をベースに、場所によって異なる非対角計量と二つの内部場の正準拘束の整合を調べた数値・記号検算。

- `verify_v28.py`：6組の正準変数のオフシェル H-H 括弧、二偏極の非線形項、非対角計量のRicci、frame一致、独立NumPy有限差分、固定背景の二偏極時間発展。
- `verify_bounded_stiffening_v28.py`：現在状態と記憶場の差に応じて F(q−χ) が2から3.2へ変化する模型。正準運動量の二成分混合を含む括弧・frame一致。
- `polarization_amplitude_audit_v28.py`：初期 cross 偏極から誘導される plus 偏極の二次スケーリングと均一媒質の陰性対照。
- `RESEARCH_NOTE_2026-11-23_v28.md`：作用・仮定・数式・計算・失敗する実装・限界。

再現：
```
python verify_v28.py
python verify_bounded_stiffening_v28.py
python polarization_amplitude_audit_v28.py
```

必要：numpy, scipy, sympy, jax, matplotlib。`audit_v28.json`, `lag_hardening_audit_v28.json`, `polarization_amplitude_audit_v28.json` が監査結果。`SHA256SUMS.txt` は配布ファイルのチェックサム。

**重要**：Einstein–Hilbert作用と二つのテンソル偏極を持つ非対角計量を出発点にしており、重力の創発・一般の3+1重力の厳密有限格子閉包・不可逆な物理的記憶を証明していない。
