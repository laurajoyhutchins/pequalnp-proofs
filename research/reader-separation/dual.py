from reader_codes import *
import numpy as np
from scipy.optimize import linprog
V=(0,1,2,3,4); fixed=('and',0,3); D=sum(1<<i for i in V); O=511^D; A=list(subsets(D))
def co(a):
 if any(a>>i&1 and a>>j&1 for i,j in E):return -1
 m=0
 for i in V:
  if a>>i&1:m|=adj[i]
 return m&O
C=[co(a) for a in A]
cols={('raw',i,i):lambda a,i=i:bool(a>>i&1) for i in V}
for i,j in combinations(V,2):
 cols['and',i,j]=lambda a,i=i,j=j:bool(a>>i&1 and a>>j&1)
 cols['or',i,j]=lambda a,i=i,j=j:bool(a>>i&1 or a>>j&1)
P=[(a,b) for a,b in combinations(A,2) if co(a)!=co(b) and cols[fixed](a)==cols[fixed](b)]
keys=list(cols); M=np.array([[f(a)!=f(b) for a,b in P] for f in cols.values()],dtype=int)
r=linprog(-np.ones(len(P)),A_ub=M,b_ub=np.ones(len(keys)),bounds=(0,None),method='highs');print('pairs',len(P),'dual',-r.fun,[(p,w) for p,w in zip(P,r.x) if w>1e-7])
# exact proof by greedy witness subcollection hitting all possible 4 additional choices
books=list(combinations(range(len(keys)),4)); bad=[sum(1<<i for i,B in enumerate(books) if not M[list(B),p].any()) for p in range(len(P))]; remaining=(1<<len(books))-1; chosen=[]
while remaining:
 p=max(range(len(P)),key=lambda i:(bad[i]&remaining).bit_count()); assert bad[p]&remaining; chosen.append(p);remaining&=~bad[p]
print('witness pairs',len(chosen),[P[p] for p in chosen]); print('masks',[(k,sum(int(M[i,p])<<j for j,p in enumerate(chosen))) for i,k in enumerate(keys)])
