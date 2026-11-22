"""Numerical figures showing dyad-level variation and both model controls."""
from pathlib import Path
import csv
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager


HERE = Path(__file__).resolve().parent
FONT = "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc"
font_manager.fontManager.addfont(FONT)
plt.rcParams.update({"font.family":font_manager.FontProperties(fname=FONT).get_name(),
                     "axes.unicode_minus":False,"font.size":12})


def read(name):
    with (HERE/name).open() as f: return list(csv.DictReader(f))


def panel(ax,rows,metric,title,ylabel,decimals):
    ax.set_title(title,loc="left",fontsize=14,pad=12)
    meta={}
    values_all=[]
    for x,condition in enumerate(["Comp","Coop"]):
        selected=[r for r in rows if r['condition']==condition]
        values=np.array([float(r[metric]) for r in selected])
        assert len(values)==10
        jitter=np.linspace(-.12,.12,len(values))
        ax.scatter(np.full(len(values),x)+jitter,values,s=50,
                   facecolors="white" if condition=="Comp" else "#222222",edgecolors="#222222",linewidths=1,zorder=3)
        mean=float(values.mean())
        ax.plot([x-.24,x+.24],[mean,mean],color="#888888",linewidth=2.5,zorder=2)
        ax.text(x+.29,mean,f"{mean:.{decimals}f}",va="center",ha="left",fontsize=11,color="#333333")
        values_all.extend(values)
        meta[condition]={"mean":mean,"dyad_values":values.tolist()}
    lo=min(0,min(values_all));hi=max(values_all)
    span=max(hi-lo,.1)
    ax.set_ylim(lo-.06*span,hi+.16*span)
    ax.set_xlim(-.5,1.6);ax.set_xticks([0,1],["Comp","Coop"])
    ax.set_ylabel(ylabel)
    ax.axhline(0,color="#dddddd",linewidth=.8,zorder=0)
    ax.spines[["top","right"]].set_visible(False)
    ax.spines[["left","bottom"]].set_color("#bbbbbb")
    ax.yaxis.grid(True,color="#eeeeee",linewidth=.7,zorder=0)
    return {"metric":metric,"values":meta}


def main():
    base=read("dyad_metrics.csv");control=read("control_dyad_metrics.csv")
    fig,axs=plt.subplots(2,2,figsize=(11.7,9.7))
    meta=[]
    meta.append(panel(axs[0,0],base,"harvest_count","実際の採取数","件／ラウンド",1))
    meta.append(panel(axs[0,1],base,"extra_per_harvest","採取1回あたりの追加崩壊","崩壊回数／採取",3))
    meta.append(panel(axs[1,0],control,"prefix90_v","入力を最初の90採取にそろえる","90採取での追加崩壊回数",2))
    meta.append(panel(axs[1,1],control,"placement_excess_v_per_K","実測配置 − 位置を混ぜた対照","追加崩壊／採取の差",3))
    fig.suptitle("Coopで連鎖が大きい。分布には重なりもある",x=.07,y=.98,ha="left",fontsize=23,fontweight="bold")
    fig.text(.07,.926,"各条件10組  /  Comp 79ラウンド・Coop 78ラウンド  /  砂山の追加崩壊 v = u−K",fontsize=11,color="#444444")
    fig.subplots_adjust(left=.09,right=.96,top=.855,bottom=.19,hspace=.43,wspace=.32)
    fig.text(.07,.045,"1点＝2人組のラウンド平均。灰色の横線と数値＝条件平均。各組を等しく重み付け。\n"
             "下左は採取件数のみ同じで、時間長は異なる。下右は各ラウンド99回の位置置換との差。\n"
             "崩壊は実測採取を入力にした模型の出力。人的独立性は参加者の略号だけでは確定できない。",
             fontsize=10,color="#444444",linespacing=1.5)
    image=HERE/"coop_comp_comparison.png"
    fig.savefig(image,dpi=180,facecolor="white");plt.close(fig)
    (HERE/"figure_metadata.json").write_text(json.dumps({"file":image.name,"panels":meta,"mean_lines_are_not_confidence_intervals":True,
        "jitter":"Fixed equally spaced offsets, no data-dependent reassignment","axes":"Different units in each panel; zero shown in each"},ensure_ascii=False,indent=2)+"\n")
    print(str(image))


if __name__=="__main__":main()
