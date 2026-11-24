#!/usr/bin/env python3
"""Independent homogeneous-coefficient enumeration for L-gct-228.
Run: python research/gct228_polarized.py (requires NumPy).
Mathematical justification:
  The degree-one coefficient of perm(J+tX) is 2*sum(X).
  On its kernel, twice the degree-two coefficient is
    sum(X_ij^2) - sum(row_sums^2) - sum(col_sums^2).
  The degree-three coefficient is perm(X).
All three must vanish since a cubic vanishing at five points is zero.
For a basis, vanishing of pure, pair and triple terms exhausts every
monomial of a homogeneous polynomial of degree at most three.
The pair tests P(v+w)=P(v+2w)=0 recover both mixed cubic coefficients:
their coefficient matrix has determinant 2, nonzero in F5.
The triple test P(u+v+w)=0 then isolates the three-distinct-variable
coefficient. RREF pivots uniquely enumerate all candidate subspaces.
"""
import itertools
import numpy as np

p=5
perms=tuple(itertools.permutations(range(3)))
def mat(v):
    v=np.asarray(v,dtype=np.int32)
    return np.concatenate((v,(-v.sum(axis=-1)%p)[...,None]),axis=-1).reshape(*v.shape[:-1],3,3)
def cubic(v):
    X=mat(v)
    return sum(np.prod(X[...,range(3),perm],axis=-1) for perm in perms)%p
def quad(v):
    X=mat(v)
    return ((X**2).sum(axis=(-1,-2))-(X.sum(axis=-1)**2).sum(axis=-1)-(X.sum(axis=-2)**2).sum(axis=-1))%p

def run():
    vectors=np.array([([0]*i+[1]+list(t)) for i in range(8) for t in itertools.product(range(p),repeat=7-i)],dtype=np.int32)
    V=vectors[(quad(vectors)==0)&(cubic(vectors)==0)]
    piv=np.argmax(V!=0,axis=1)
    n=len(V)
    print('projective tangent points:',len(vectors),'level lines:',n,flush=True)
    adj=[]
    for i,v in enumerate(V):
        ix=np.flatnonzero((piv>piv[i]) & (v[piv]==0))
        W=V[ix]
        ok=(quad(W+v)==0)&(cubic(W+v)==0)&(cubic(2*W+v)==0)
        adj.append(ix[ok])
    print('compatible RREF pairs:',sum(map(len,adj)),flush=True)
    counts=[0,0,0,0,0]
    def dfs(basis,candidates):
        d=len(basis)
        counts[d]+=1
        if d==4:raise AssertionError('Found a 4-dimensional level space')
        for i in candidates:
            if any(cubic(V[a]+V[b]+V[i])!=0 for a,b in itertools.combinations(basis,2)):
                continue
            nxt=np.intersect1d(candidates,adj[i],assume_unique=True)
            dfs(basis+[i],nxt)
    dfs([],np.arange(n))
    assert counts==[1,4266,8448,54,0],counts
    print('RREF spaces visited by dimension:',counts,flush=True)
    print('No 4-dimensional level space exists.')
    return counts
if __name__=='__main__':run()
