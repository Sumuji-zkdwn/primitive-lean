#!/usr/bin/env python3
"""Render the explicit deforming-patch example; no physical motion is inferred."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties

OUT = Path(__file__).resolve().parents[2] / 'verification' / 'planar-sync'
OUT.mkdir(parents=True, exist_ok=True)
font_path = Path('/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc')
if font_path.exists():
    fp = FontProperties(fname=str(font_path))
    plt.rcParams['font.family'] = fp.get_name()
    from matplotlib import font_manager
    font_manager.fontManager.addfont(str(font_path))
plt.rcParams.update({'font.size': 11, 'axes.spines.top': False,
                     'axes.spines.right': False, 'axes.unicode_minus': False})
heights = [1, .7, 1.2, .45, 0, .65, 1.1, .35, 0, .9, .55]
bends = [.08, .18, .3, .4, .48, .32, .12, -.12, -.32, -.18, .05]
fig, axes = plt.subplots(2, 2, figsize=(10, 8), constrained_layout=True)
u = np.linspace(-1, 1, 151)
grid = np.linspace(-1, 1, 7)
for ax, n in zip(axes.flat, [0, 2, 4, 6]):
    h, bend, ratio = heights[n], bends[n], .5**n
    widths = [1+.7*ratio, 1-.7*ratio]
    for index, a in enumerate(widths):
        color, style, label = ('#254f7d', '-', '面 A') if index == 0 else ('#ba5b29', '--', '面 B')
        for j,v in enumerate(grid):
            ax.plot(a*u, h*v+bend*u*u, color=color, ls=style,
                    lw=1.2 if j in (0,len(grid)-1) else .65,
                    label=label if j==0 else None)
        if h:
            for uj in grid:
                ax.plot([a*uj,a*uj],[-h+bend*uj*uj,h+bend*uj*uj],
                        color=color,ls=style,lw=.65)
    uj,vj=.75,.5
    yy=h*vj+bend*uj*uj
    ax.plot([widths[0]*uj,widths[1]*uj],[yy,yy],color='#555555',lw=.8)
    ax.plot(widths[0]*uj,yy,'o',ms=5,color='#254f7d')
    ax.plot(widths[1]*uj,yy,'s',ms=4,color='#ba5b29')
    ax.set(xlim=(-1.85,1.85),ylim=(-1.45,1.65),aspect='equal',
           xlabel='画面の横座標（任意単位）',ylabel='画面の縦座標（任意単位）')
    kind='曲線' if h==0 else '面'
    ax.set_title(f'{n} 回更新：{kind}　／　RMS のずれ {ratio:.4g} 倍',loc='left')
    ax.grid(alpha=.14)
    if n == 0:
        ax.legend(loc='lower left',frameon=False,ncol=2)
fig.suptitle('共通の伸縮・曲がりと、二つの像の同期は別に計算できる',fontsize=15)
fig.savefig(OUT/'shape-sync-geometry.png',dpi=175)
plt.close(fig)
print(OUT/'shape-sync-geometry.png')
