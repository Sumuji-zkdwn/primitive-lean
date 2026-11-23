# 第27回：空間依存するスカラー・テンソル拘束の有限検算

- **verify_v27.py**: 既存の作用に対応する五つの正準対（対角3D計量3組、記憶スカラー1組、局所状態スカラー1組）の格子Poisson bracketを自動微分で直接検査。曲率・ラプラシアンの二次微分形と部分積分形、Jordan/Einstein frameのHamiltonianも照合。
- **independent_audit_v27.py**: JAXとは独立にNumPyで構築したHamiltonianを、全変数の二側有限差分で微分して括弧を再計算。
- **RESEARCH_NOTE_2026-11-23_v27.md**: 方程式・証明・反例・到達範囲・参考文献。
- **audit_v27.json / independent_audit_v27.json**: 数値監査データ。
- **bracket_convergence_v27.csv / other_profiles_v27.csv**: 異なる格子解像度・空間配置の結果。
- **curvature_crosscheck_v27.csv**: 曲率の二階微分による直接計算と部分積分後の計算の比較。
- **gradient_checks_v27.csv**: 自動微分と直接有限差分の照合。
- **bracket_convergence_v27.png / frame_identity_convergence_v27.png**: 図。

再実行：

```bash
python verify_v27.py
python independent_audit_v27.py
```

注意：本研究は既存のEinstein–Hilbert＋スカラー・テンソル理論の**限定的な検算**。原始的なゲルモデルからの重力の創発証明ではない。また、記憶場は可逆的であり、不可逆なダイラタンシー流体ではない。
