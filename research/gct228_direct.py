#!/usr/bin/env python3
"""Independent exact enumeration for swarm probe L-gct-228.

Pinned snapshot: 3eb0c78ba6004cf194e4ac0b855c9677a1cddd46
Statement: exists a dimension-4 subspace of F_5^(3x3) such that
perm(J+X)=6 for every X. Answer: no; maximum dimension is 3.

Run: python research/gct228_direct.py (requires NumPy).
No solver, random choices, floating point, or external data are used.
This is computational evidence, not a Lean kernel proof or upstream submission.

Completeness: perm(J+tX)-6 has degree at most 3, and vanishes at
all five field elements for X in any level space. Its linear coefficient
is 2*sum(X), so every level vector lies in the total-sum-zero
hyperplane. Identify this hyperplane with F_5^8 by reconstructing
the ninth entry as the negative sum of the other eight.

Enumerate normalized nonzero vectors (first nonzero coordinate 1),
keeping exactly those with constant permanent along their whole line.
Every linear subspace has a unique reduced row echelon basis. Its
basis vectors are among the retained vectors, their pivots increase,
and every previous row is zero at the new pivot. Each prefix span
must itself be level. The recursion checks every element u+t*w in
each extension, all coefficients t in F_5, and prunes exactly when
a required permanent value fails. Thus every level subspace of
dimension at most 4 is visited once, and none can be missed.
"""
import numpy as np

p=5
def permanent(v):
    v=np.asarray(v,dtype=np.int32)%p
    a,b,c,d,e,f,g,h=np.moveaxis((v+1)%p,-1,0)
    i=(1-v.sum(axis=-1))%p
    return (a*e*i+a*f*h+b*d*i+b*f*g+c*d*h+c*e*g)%p

def run():
    # Enumerate integers in base five, normalize the first nonzero entry.
    N=np.arange(5**8,dtype=np.int32)
    allv=(N[:,None]//(5**np.arange(7,-1,-1,dtype=np.int32)))%5
    piv=np.argmax(allv!=0,axis=1)
    V=allv[(N!=0)&(allv[np.arange(len(N)),piv]==1)]
    assert len(V)==97656
    V=V[np.logical_and.reduce([permanent(t*V)==1 for t in range(1,5)])]
    piv=np.argmax(V!=0,axis=1)
    print('direct level lines:',len(V),flush=True)

    def compatible(U,W):
        keep=np.ones(len(W),dtype=bool)
        for u in U:
            for t in range(1,5):
                ids=np.flatnonzero(keep)
                if not len(ids):return keep
                keep[ids]=permanent(u+t*W[ids])==1
        return keep
    counts=[0]*5
    example=None
    def visit(B,U,cand):
        nonlocal example
        d=len(B);counts[d]+=1
        if d==3 and example is None:example=np.array(B)
        if d==4:raise AssertionError('Found a 4-dimensional level space')
        if not len(cand):return
        cand=cand[compatible(U,V[cand])]
        for i in cand:
            nxt=cand[(piv[cand]>piv[i])&(V[i,piv[cand]]==0)]
            newU=np.concatenate([(U+t*V[i])%5 for t in range(5)])
            visit(B+[V[i]],newU,nxt)
    visit([],np.zeros((1,8),dtype=np.int32),np.arange(len(V)))
    assert counts==[1,4266,8448,54,0],counts
    assert len(example)==3
    print('direct RREF counts:',counts,flush=True)
    M=np.c_[example,(-example.sum(1))%5].reshape(3,3,3)
    print('3-dimensional witness:',M.tolist(),flush=True)
    return counts

if __name__=='__main__':run()
