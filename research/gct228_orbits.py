#!/usr/bin/env python3
"""Classify all 54 dimension-3 spaces under row/column permutations
and transpose, using the polarized search's exact predicates.
Run: python research/gct228_orbits.py (requires NumPy).
"""
import itertools
import numpy as np
from gct228_polarized import mat, quad, cubic

def rref(A):
    A=np.asarray(A,dtype=np.int64).copy()%5
    i=0
    for j in range(A.shape[1]):
        k=next((k for k in range(i,len(A)) if A[k,j]),None)
        if k is None:continue
        A[[i,k]]=A[[k,i]]
        A[i]=(A[i]*pow(int(A[i,j]),-1,5))%5
        for k in range(len(A)):
            if k!=i:A[k]=(A[k]-A[k,j]*A[i])%5
        i+=1
        if i==len(A):break
    return tuple(map(tuple,A[:i]))

def run():
    p=5
    V=np.array([([0]*i+[1]+list(t)) for i in range(8) for t in itertools.product(range(p),repeat=7-i)],dtype=np.int32)
    V=V[(quad(V)==0)&(cubic(V)==0)]
    piv=np.argmax(V!=0,axis=1); adj=[]
    for i,v in enumerate(V):
        ids=np.flatnonzero((piv>piv[i])&(v[piv]==0));W=V[ids]
        adj.append(ids[(quad(W+v)==0)&(cubic(W+v)==0)&(cubic(2*W+v)==0)])
    spaces=set()
    for i in range(len(V)):
        for j in adj[i]:
            ids=np.intersect1d(adj[i],adj[j],assume_unique=True)
            ids=ids[cubic(V[ids]+V[i]+V[j])==0]
            for k in ids:
                spaces.add(rref(mat(V[[i,j,k]]).reshape(3,9)))
    assert len(spaces)==54
    perms=list(itertools.permutations(range(3)))
    pending=set(spaces); orbits=[]
    while pending:
        rep=min(pending); M=np.array(rep).reshape(3,3,3); orb=set()
        for r,c,t in itertools.product(perms,perms,(False,True)):
            N=M[:,r,:][:,:,c]
            if t:N=N.transpose(0,2,1)
            orb.add(rref(N.reshape(3,9)))
        assert orb<=spaces
        assert orb<=pending
        pending-=orb
        orbits.append((len(orb),rep))
    assert sorted(size for size,_ in orbits)==[18,36]
    print('orbit sizes:',[size for size,_ in orbits])
    for size,rep in orbits:
        print(size, np.array(rep).reshape(3,3,3).tolist())
    return orbits
if __name__=='__main__':run()
