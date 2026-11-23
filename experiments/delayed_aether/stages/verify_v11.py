#!/usr/bin/env python3
"""Finite box Skyrme degree + independent tetrahedral edge-length geometry.

No claim of deriving Einstein gravity: a constitutive coupling is imposed.
Produces JSON, CSV, PNG; deterministic. Python 3.10+ numpy, scipy, matplotlib.
"""
import itertools, json, csv, math, hashlib
from pathlib import Path
import numpy as np
from scipy.ndimage import gaussian_filter

ROOT = Path(__file__).resolve().parent
EDGES = np.array([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], dtype=int)
COMP = [(2,3),(1,3),(1,2),(0,3),(0,2),(0,1)]


def make_mesh(n: int):
    # Freudenthal decomposition: six tetrahedra in each cubic cell.
    g = np.linspace(-1, 1, n + 1)
    coords = np.stack(np.meshgrid(g, g, g, indexing='ij'), -1).reshape(-1, 3)
    def idx(i,j,k): return (i*(n+1)+j)*(n+1)+k
    templates=[]
    for perm in itertools.permutations(range(3)):
        off=np.zeros((4,3), dtype=int)
        off[1,perm[0]]=1
        off[2]=off[1]
        off[2,perm[1]]=1
        off[3]=[1,1,1]
        if np.linalg.det((off[1:]-off[0]).T)<0:
            off[[2,3]]=off[[3,2]]
        templates.append(off)
    tets=np.empty((n*n*n*6,4),dtype=np.int32)
    k=0
    for i in range(n):
        for j in range(n):
            for l in range(n):
                base=np.array([i,j,l])
                for off in templates:
                    ind=base+off
                    tets[k]=[idx(*s) for s in ind]
                    k+=1
    return coords,tets


def hedgehog(coords,center=(.07,-.055,.046),radius=.7,stretch=(1,1,1)):
    x=(coords-np.array(center))*np.array(stretch)
    r=np.linalg.norm(x,axis=1)
    f=np.pi*np.maximum(0,1-r/radius)
    q=np.empty((len(r),4),dtype=float)
    q[:,0]=np.cos(f)
    q[:,1:]=np.where((r>1.e-14)[:,None], (np.sin(f)/np.maximum(r,1.e-14))[:,None]*x, 0.)
    q/=np.linalg.norm(q,axis=1)[:,None]
    return q


def qmult(a,b):
    return np.concatenate([(a[:,0]*b[:,0]-np.sum(a[:,1:]*b[:,1:],axis=1))[:,None],
      a[:,0,None]*b[:,1:]+b[:,0,None]*a[:,1:]+np.cross(a[:,1:],b[:,1:])],axis=1)


def degree_preimage(coords,tets,q,target=None,ret_info=False):
    # Brouwer degree of the normalized *affine* interpolation q(x)=Q(x)/|Q(x)|.
    # Target is a regular value away from constant boundary, orientation fixed
    # by det([q,dq/dx,dq/dy,dq/dz]) with positive oriented tetrahedra.
    target=np.array([-1.,.073,-.051,.037]) if target is None else np.asarray(target,dtype=float)
    target=target/np.linalg.norm(target)
    qv=q[tets]
    F=qv[:,:,1:]-qv[:,:,:1]*(target[1:]/target[0])[None,None,:]
    # Far from the target negative-scalar hemisphere, do not attempt solves.
    candidates=np.any(qv[:,:,0]<0,axis=1) & np.all((F.min(axis=1)<=0)&(F.max(axis=1)>=0),axis=1)
    indices=np.nonzero(candidates)[0]
    if len(indices)==0:
        result={'degree':0,'regular_preimages':0,'signed_preimages':[], 'candidates':0,
                'min_preimage_barycentric':None, 'preimage_positions':[]}
        return result if ret_info else 0
    A=np.moveaxis(F[indices,1:]-F[indices,:1],1,2)
    detA=np.linalg.det(A)
    valid=np.abs(detA)>1.e-12
    inds=indices[valid]
    if not len(inds):
        result={'degree':0,'regular_preimages':0,'signed_preimages':[], 'candidates':int(len(indices)),
                'min_preimage_barycentric':None, 'preimage_positions':[]}
        return result if ret_info else 0
    abc=np.linalg.solve(A[valid],-F[inds,0,:,None])[:,:,0]
    bary=np.concatenate([1.-np.sum(abc,axis=1)[:,None],abc],axis=1)
    inside=np.all(bary>1.e-10,axis=1)
    Q=np.einsum('ni,nij->nj',bary,qv[inds])
    inside&=(Q@target)>1.e-9
    inds=inds[inside]; bary=bary[inside]; Q=Q[inside]
    if len(inds):
        dQ=np.transpose(qv[inds,1:]-qv[inds,:1],(0,2,1))
        matrices=np.concatenate([Q[:,:,None],dQ],axis=2)
        det=np.linalg.det(matrices)
        # correct for orientation of Euclidean domain tetrahedron
        dx=np.transpose(coords[tets[inds,1:]]-coords[tets[inds,:1]],(0,2,1))
        detx=np.linalg.det(dx)
        signs=np.sign(det/detx).astype(int)
        assert np.all(signs!=0)
        signed=signs.tolist()
        val=int(np.sum(signs))
        xyz=np.einsum('ni,nij->nj',bary,coords[tets[inds]])
    else:
        signed=[];val=0;xyz=np.zeros((0,3))
    result={'degree':val,'regular_preimages':len(signed),'signed_preimages':signed,
       'preimage_positions':xyz.tolist(),'candidates':int(len(indices)),
       'min_preimage_barycentric':float(np.min(bary)) if len(bary) else None}
    return result if ret_info else val


def unique_edges(tets):
    ea=np.sort(tets[:,EDGES],axis=2)
    unique, inverse=np.unique(ea.reshape(-1,2),return_inverse=True,axis=0)
    return unique,inverse.reshape(-1,6)


def source_texture(coords, n, q):
    qg=q.reshape((n+1,n+1,n+1,4))
    # vertex endpoint finite-difference mean squared gradient
    s=np.zeros((n+1,n+1,n+1),float)
    c=np.zeros_like(s)
    for axis in range(3):
        d=np.diff(qg,axis=axis)
        norm=np.sum(d*d,axis=-1)/(2./n)**2
        left=[slice(None)]*3;right=[slice(None)]*3
        left[axis]=slice(None,-1);right[axis]=slice(1,None)
        s[tuple(left)]+=norm;c[tuple(left)]+=1
        s[tuple(right)]+=norm;c[tuple(right)]+=1
    s/=c
    s=gaussian_filter(s,sigma=.15/(2./n),mode='nearest')
    s=s.reshape(-1)
    if np.max(s)>0:s/=np.max(s)
    # zero for boundary source; hedgehog is exactly constant near boundary.
    return s


def metric_geometry(coords,tets,unique, inverse, sigma_v, length_override=None):
    pos=coords[unique]
    midpoint=pos.mean(axis=1)
    euclidean=np.linalg.norm(pos[:,1]-pos[:,0],axis=1)
    sigma=np.mean(sigma_v[unique],axis=1)
    lens=euclidean*np.exp(sigma) if length_override is None else np.asarray(length_override,dtype=float)
    L=lens[inverse]
    l2=L*L
    G=np.zeros((len(tets),3,3),float)
    G[:,0,0],G[:,1,1],G[:,2,2]=l2[:,0],l2[:,1],l2[:,2]
    G[:,0,1]=G[:,1,0]=(l2[:,0]+l2[:,1]-l2[:,3])/2
    G[:,0,2]=G[:,2,0]=(l2[:,0]+l2[:,2]-l2[:,4])/2
    G[:,1,2]=G[:,2,1]=(l2[:,1]+l2[:,2]-l2[:,5])/2
    eig=np.linalg.eigvalsh(G)
    minimum=float(np.min(eig))
    if minimum<=1.e-13:
        raise ValueError(f'Inadmissible tetrahedral metric: min Gram eigenvalue={minimum}')
    p=np.zeros((len(tets),4,3))
    p[:,1:]=np.linalg.cholesky(G)
    normals=np.empty((len(tets),4,3))
    for i in range(4):
        ids=[j for j in range(4) if j!=i]
        n=np.cross(p[:,ids[1]]-p[:,ids[0]],p[:,ids[2]]-p[:,ids[0]])
        flip=(np.einsum('ij,ij->i',n,p[:,i]-p[:,ids[0]])>0)
        n[flip]*=-1
        normals[:,i]=n/np.linalg.norm(n,axis=1)[:,None]
    angles=np.empty((len(tets),6))
    for k,(c,d) in enumerate(COMP):
        co=-np.sum(normals[:,c]*normals[:,d],axis=1)
        angles[:,k]=np.arccos(np.clip(co,-1,1))
    total=np.zeros(len(unique))
    np.add.at(total,inverse.flatten(),angles.flatten())
    # boundary edge iff lies in a face of the cubical domain
    boundary=np.any(np.isclose(np.abs(midpoint),1.0,atol=1.e-12),axis=1)
    deficit=2*np.pi-total
    inside=~boundary
    # Localized curvature indicators, sum edge length times angle deficit.
    center=(0,0,0)
    inner=inside & (np.linalg.norm(midpoint-np.asarray(center),axis=1)<0.5)
    return {'lengths':lens,'deficit':deficit,'interior':inside, 'inner':inner,
            'midpoint':midpoint,'min_gram_eigenvalue':minimum,
            'max_flat_residual':float(np.max(np.abs(deficit[inside]))),
            'regge_scalar_proxy_total':float(2*np.sum(lens[inside]*deficit[inside])),
            'regge_scalar_proxy_core':float(2*np.sum(lens[inner]*deficit[inner])),
            'regge_abs_curvature':float(np.sum(lens[inside]*np.abs(deficit[inside])))}


def main():
    result={'model':'finite-box degree and tetrahedral internal edge metric','date':'2026-11-22'}
    cases=[]
    meshes={}
    for n in (8,12,16,20):
        coords,tets=make_mesh(n)
        meshes[n]=(coords,tets)
        base=hedgehog(coords)
        shifted=hedgehog(coords,center=(.21,.12,-.09),radius=.65)
        elliptical=hedgehog(coords,stretch=(1.15,.86,1.05))
        mirrored=hedgehog(coords,stretch=(-1,1,1))
        vacuum=np.zeros_like(base); vacuum[:,0]=1
        tests=[('vacuum',vacuum),('single',base),('translated',shifted),
               ('elliptical',elliptical),('orientation_reverse',mirrored)]
        if n>=12:
            a=hedgehog(coords,center=(-.39,-.15,0),radius=.33)
            b=hedgehog(coords,center=(.39,.15,0),radius=.33)
            tests.append(('two_disjoint',qmult(a,b)))
        for label,q in tests:
            info=degree_preimage(coords,tets,q,ret_info=True)
            boundary=np.any(np.isclose(np.abs(coords),1),axis=1)
            bnd=float(np.max(np.linalg.norm(q[boundary]-np.array([1.,0,0,0]),axis=1)))
            item={'n':n,'case':label,'degree':info['degree'],
                  'preimages':info['regular_preimages'],'candidate_tets':info['candidates'],
                  'boundary_error':bnd,'preimage_locations':info['preimage_positions']}
            cases.append(item)
    result['degree_cases']=cases
    # Discrete-resolution caution: if the lump shrinks below mesh resolution,
    # vertex sampling fails to protect topological degree.
    collapse=[]
    for n in (8,12,16,20):
        coords,tets=meshes[n]
        for r in (.70,.50,.30,.20,.15,.10,.07):
            q=hedgehog(coords,radius=r)
            collapse.append({'n':n,'radius':r,'degree':degree_preimage(coords,tets,q)})
    result['resolution_failure']=collapse
    for n in (8,12,16):
        coords,tets=meshes[n]
        unique,inv=unique_edges(tets)
        q=hedgehog(coords)
        s=source_texture(coords,n,q)
        geom=[]
        for alpha in (0.,.02,.04,.06):
            geo=metric_geometry(coords,tets,unique,inv,alpha*s)
            info={key:float(geo[key]) for key in ['min_gram_eigenvalue','max_flat_residual','regge_scalar_proxy_total','regge_scalar_proxy_core','regge_abs_curvature']}
            info.update({'n':n,'alpha':alpha,'degree':degree_preimage(coords,tets,q)})
            geom.append(info)
        result.setdefault('metric_cases',[]).extend(geom)
    # Negative control: a smooth coordinate warp changes lengths but not intrinsic curvature.
    n=16; coords,tets=meshes[n]
    unique,inv=unique_edges(tets)
    x,y,z=coords.T
    bump=(1-x*x)*(1-y*y)*(1-z*z)
    warped=coords+.12*bump[:,None]*np.column_stack([y,.3*x,-.2*x])
    flat_warp_l=np.linalg.norm(warped[unique[:,1]]-warped[unique[:,0]],axis=1)
    warp_geometry=metric_geometry(coords,tets,unique,inv,np.zeros(len(coords)),length_override=flat_warp_l)
    result['coordinate_warp_negative_control']={k:warp_geometry[k] for k in
        ['max_flat_residual','regge_abs_curvature','min_gram_eigenvalue']}
    (ROOT/'audit_v11.json').write_text(json.dumps(result,indent=2,ensure_ascii=False),encoding='utf8')
    with (ROOT/'degree_cases.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=['n','case','degree','preimages','candidate_tets','boundary_error'])
        w.writeheader();w.writerows([{k:r[k] for k in w.fieldnames} for r in cases])
    with (ROOT/'metric_cases.csv').open('w',newline='') as f:
        keys=list(result['metric_cases'][0]);w=csv.DictWriter(f,fieldnames=keys)
        w.writeheader();w.writerows(result['metric_cases'])
    with (ROOT/'resolution_failure.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=['n','radius','degree'])
        w.writeheader();w.writerows(collapse)
    print('Coordinate warp:',result['coordinate_warp_negative_control'])
    print('Degree:')
    for row in cases:print(row['n'],row['case'],row['degree'],row['preimages'],row['boundary_error'])
    print('Metric:')
    for row in result['metric_cases']:
        print(row['n'],row['alpha'],row['min_gram_eigenvalue'],row['max_flat_residual'],row['regge_abs_curvature'],row['regge_scalar_proxy_core'])

if __name__=='__main__':main()