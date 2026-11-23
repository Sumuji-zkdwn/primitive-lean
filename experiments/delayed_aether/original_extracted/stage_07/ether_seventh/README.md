# 第7回 遅延硬化エーテル: ゲル変位・内在曲率・線形重力波の切り分け

2026-11-22 JST。`RESEARCH_NOTE_2026-11-22_v7.md` に背景、命題、証明、評価、残課題をまとめています。

## 実行

```
python verify_v7.py
python intrinsic_curvature_v7.py
python polarization_rank_v7.py
```

Python 3, numpy, sympy, matplotlib が必要です。主な出力:

- `audit_v7.json`: 4次元線形化Einsteinテンソルの記号的恒等式とTT射影、波動計算の監査
- `intrinsic_audit_v7.json`: 2次元の内在辺長と角度欠損の監査
- `tensor_wave_propagation.png`: 二つのTT波束の移動
- `tensor_wave_energy.png`: 保存離散エネルギーの誤差
- `intrinsic_curvature.png`: 内在辺長から生じる正負の離散曲率
- `tensor_wave_timeseries.csv`, `tt_projection_samples.csv`, `intrinsic_curvature.csv`: 再計算可能な数値データ
- `polarization_rank_v7.json`: 空間計量6成分のうちTTは2成分という厳密な階数検査

## 研究上の重要な制限

この回で用いた線形化Einstein方程式は**既知のGRから借りた基準模型**です。ゲルからEinstein作用、等価原理、素粒子・量子論が導出されたという主張ではありません。不可逆な履歴硬化もこの回の実装には入れていません。
