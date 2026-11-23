#!/usr/bin/env python3
"""Six-triangle metric fan: coordinate displacement vs intrinsic edge lengths.
Curvature is a 2D Regge angle deficit (not an Einstein equation).
"""
from pathlib import Path
import csv,json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
D=Path(__file__).resolve().parent

def angle_from_edges(a,b,c):
    # Vertex angle between the adjacent sides a,b, opposite length c.
    return float(np.arccos(np.clip((a*a+b*b-c*c)/(2*a*b),-1,1)))

def coord_fan_deficit(center):
    ps=np.array([[np.cos(j*np.pi/3),np.sin(j*np.pi/3)] for j in range(6)])
    angles=[]
    for j in range(6):
        aa=np.linalg.norm(ps[j]-center)
        bb=np.linalg.norm(ps[(j+1)%6]-center)
        cc=np.linalg.norm(ps[j]-ps[(j+1)%6])
        angles.append(angle_from_edges(aa,bb,cc))
    return 2*np.pi-sum(angles)

rng=np.random.default_rng(20261122)
# Don't let the displaced center leave the convex hexagon.
coordinate_deficits=[coord_fan_deficit(rng.uniform(-0.25,0.25,2)) for _ in range(1024)]
assert max(abs(x) for x in coordinate_deficits)<1e-12
scale=np.linspace(.85,1.25,81)
def intrinsic_fan_deficit(scale):
    return 2*np.pi-6*angle_from_edges(scale,scale,1.)
deficit=np.array([intrinsic_fan_deficit(c) for c in scale])
assert abs(intrinsic_fan_deficit(1.0))<1e-12
assert intrinsic_fan_deficit(1.1)>0 and intrinsic_fan_deficit(.9)<0
with (D/'intrinsic_curvature.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['central_edge_scale','angle_deficit_rad','angle_deficit_degrees'])
    w.writerows([(float(a),float(b),float(np.degrees(b))) for a,b in zip(scale,deficit)])
fig,ax=plt.subplots(figsize=(8.7,4.6),layout='constrained')
ax.plot(scale,np.degrees(deficit),lw=2,label='intrinsic six-triangle fan')
ax.axhline(0,color='gray',ls='--',lw=1)
ax.scatter([.9,1,1.1], [np.degrees(intrinsic_fan_deficit(q)) for q in [.9,1,1.1]],zorder=4)
ax.set(xlabel='center-to-outer intrinsic edge / outer edge',ylabel='central angle deficit (degrees)',title='Coordinate deformation is flat; independent edge lengths can curve space')
ax.legend(loc='best');ax.grid(alpha=.2)
fig.savefig(D/'intrinsic_curvature.png',dpi=180);plt.close(fig)
results={'coordinate_displacements_tested':1024,'max_abs_coordinate_angle_deficit_rad':max(abs(x) for x in coordinate_deficits),
         'intrinsic_edge_scale_0_90_deficit_degrees':float(np.degrees(intrinsic_fan_deficit(.9))),
         'intrinsic_edge_scale_1_00_deficit_degrees':float(np.degrees(intrinsic_fan_deficit(1))),
         'intrinsic_edge_scale_1_10_deficit_degrees':float(np.degrees(intrinsic_fan_deficit(1.1))),
         'note':'2D intrinsic Regge curvature only. No 4D gravity or Einstein field equations.'}
(D/'intrinsic_audit_v7.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(results,indent=2))
