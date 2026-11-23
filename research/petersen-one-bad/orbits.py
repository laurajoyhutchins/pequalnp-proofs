"""Enumerate disjoint nonempty unordered support pairs up to the Petersen automorphisms."""
from collections import Counter
E=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
N=[sum(1<<j for j in range(10) if (i,j) in E or (j,i) in E) for i in range(10)]
def auto(a):
    if len(a)==10: yield tuple(a);return
    i=len(a)
    for j in range(10):
        if j not in a and all(bool(N[i]>>k&1)==bool(N[j]>>v&1) for k,v in enumerate(a)):
            yield from auto(a+[j])
A=tuple(auto([]));assert len(A)==120
maps=[[sum(1<<p[i] for i in range(10) if m>>i&1) for m in range(1024)] for p in A]
seen=set();reps=[]
for u in range(1,1024):
    v=1023^u
    while v:
        if u<v and (u,v) not in seen:
            orb={tuple(sorted((a[u],a[v]))) for a in maps}
            seen|=orb
            if any(v&~N[i] for i in range(10) if u>>i&1):reps.append((u,v,len(orb)))
        v=(v-1)&(1023^u)
assert len(seen)==(3**10-2*2**10+1)//2
print(len(reps),sum(z for _,_,z in reps))
for u,v,k in reps:print(u,v,k)
