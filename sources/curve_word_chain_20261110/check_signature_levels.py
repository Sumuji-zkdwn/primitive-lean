import numpy as np

def signature(word,segments=60,degree=3):
    levels=[np.array(1.,dtype=float)]+[np.zeros((2,)*j) for j in range(1,degree+1)]
    theta=0.
    for a in word:
        turn=np.pi/2 if a=='A' else 3*np.pi/2
        k=turn # h=1
        for t in range(segments):
            ang=theta+k*(t/segments)
            delta_complex=np.exp(1j*ang)*np.expm1(1j*k/segments)/(1j*k)
            dx=np.array([delta_complex.real,delta_complex.imag])
            seglevels=[np.array(1.)]
            for j in range(1,degree+1):
                item=dx
                for _ in range(1,j):item=np.multiply.outer(item,dx)
                seglevels.append(item/__import__("math").factorial(j))
            nxt=[levels[0]]
            for j in range(1,degree+1):
                v=levels[j]+seglevels[j]
                for k2 in range(1,j):v+=np.tensordot(levels[k2],seglevels[j-k2],axes=0)
                nxt.append(v)
            levels=nxt
        theta+=turn
    return levels
if __name__ == '__main__':
    for a,b in [('AABBBA','BAAABB'),('AAAABBBB','AAABBBBA'),('AAAABBBB','AABBBBAA')]:
        x=signature(a);y=signature(b)
        print('pair',a,b)
        for k in range(1,4):print('  level',k,'max diff',np.max(np.abs(x[k]-y[k])))
