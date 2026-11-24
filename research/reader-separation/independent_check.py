"""Full residual truth-table check independent of the neighborhood code."""
from reader_codes import E, subsets, code, upper, N
from itertools import combinations

V=(0,1,2,3,4)
D=31
A=list(subsets(D))
O=511^D
F=lambda a:any(a>>i&1 and a>>j&1 for i,j in E)
C={a:tuple(F(a|b) for b in subsets(O)) for a in A}
K=[('raw',i,i) for i in V]+[(op,i,j) for i,j in combinations(V,2) for op in ('and','or')]
def bit(k,a):
 op,i,j=k
 return bool(a>>i&1) if op=='raw' else bool(a>>i&1 and a>>j&1) if op=='and' else bool(a>>i&1 or a>>j&1)
fixed=('and',0,3)
P=[(a,b) for a,b in combinations(A,2) if C[a]!=C[b] and bit(fixed,a)==bit(fixed,b)]
assert len(P)==189
W=[(26,18),(26,10),(22,20),(22,18),(21,5),(19,18),(13,9),(12,5),(11,9)]
assert all((a,b) in P or (b,a) in P for a,b in W)
assert all(sum(bit(k,a)!=bit(k,b) for a,b in W)==(0 if k==fixed else 2) for k in K)
assert all(not all(any(bit(k,a)!=bit(k,b) for k in B) for a,b in P) for B in combinations(K,4))
assert all(any(bit(k,a)!=bit(k,b) for k in K[:5]) for a,b in P)
print('independent exhaustive 4-extra-column exclusions:',len(list(combinations(K,4))))
print('distinct residual classes:',len(set(C.values())))
print('conditioned fibers:',[len({C[a] for a in A if bit(fixed,a)==b}) for b in (False,True)])
print('reader optimum 6 (5 raw columns plus mandatory first gate)')
best=[]
for k in range(2,6):
 for V in combinations(range(N),k):
  D=sum(1<<i for i in V); b=code(D)
  for i,j in combinations(V,2):
   for op in ('and','or'):
    n,info=b((op,i,j));best.append((n+upper(D),V,op,i,j,n,upper(D)))
print('max of bound plus constructive residual upper:',max(best),'cases:',len(best))
assert len(best)==4608 and max(best)[0]==14
