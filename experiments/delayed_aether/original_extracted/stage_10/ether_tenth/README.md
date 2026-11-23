# 遅延硬化エーテル模型・第10回の再現用ファイル

## 内容

- `RESEARCH_NOTE_2026-11-22_v10.md`：今回の定義、有限模型の証明、数値結果、失敗点と限界
- `verify_v10.py`：セル複体の全コホモロジー、四次元閉条件、局所履歴ダイナミクスの検算と描画
- `audit_assert_v10.py`：保存ファイルを独立に読み、コホモロジー・閉条件・履歴・下界を再点検
- `audit_v10.json`：主要な数値、厳密階数、反例の記録
- `dynamics_charge_*`：位相電荷と記憶速度の2×2の時間発展
- `sector_area_bounds.csv`：下界の具体的達成構成（L=2,3,4,5）

## 動かし方

```bash
python -m pip install numpy matplotlib
python verify_v10.py
python audit_assert_v10.py
```

**重要な注意**：この模型はZ2セルコチェインの位相的代理模型であり、ローレンツ時空の幾何・アインシュタイン方程式・粒子の局在化は再現していません。更新スイープは物理的な相対論的時刻ではありません。
