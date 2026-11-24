from itertools import combinations
from functools import lru_cache
from collections import Counter
E=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5))
N=9
adj=[sum(1<<v for v in range(N) if (u,v) in E or (v,u) in E) for u in range(N)]

def subsets(mask):
 a=mask
 while True:
  yield a
  if not a:return
  a=(a-1)&mask

def code(D):
 A=list(subsets(D)); O=((1<<N)-1)^D; v=[i for i in range(N) if D>>i&1]
 def co(a):
  if any(a>>i&1 and a>>j&1 for i,j in E):return -1
  m=0
  for i in v:
   if a>>i&1:m|=adj[i]
  return m&O
 C=[co(a) for a in A]; pairs=[(a,b) for a,b in combinations(range(len(A)),2) if C[a]!=C[b]]; U=(1<<len(pairs))-1
 cols={}
 for i in v:cols[('raw',i,i)]=[bool(a>>i&1) for a in A]
 for i,j in combinations(v,2):
  cols['and',i,j]=[bool(a>>i&1 and a>>j&1) for a in A]
  cols['or',i,j]=[bool(a>>i&1 or a>>j&1) for a in A]
 masks={k:sum(1<<p for p,(a,b) in enumerate(pairs) if c[a]!=c[b]) for k,c in cols.items()}
 distinct=list(set(masks.values())); distinct=[m for m in distinct if not any(m!=z and m&~z==0 for z in distinct)]
 bypair=[[m for m in distinct if m>>p&1] for p in range(len(pairs))]
 @lru_cache(None)
 def solve(rem,b):
  if not rem:return True
  if b==0:return False
  if max((rem&m).bit_count() for m in distinct)*b<rem.bit_count():return False
  # select a pair with fewest choices, branch strongest first
  p=min((i for i in range(len(pairs)) if rem>>i&1),key=lambda i:len(bypair[i]))
  return any(solve(rem&~m,b-1) for m in sorted(bypair[p],key=lambda m:-(m&rem).bit_count()))
 def bound(fixed):
  rem=U&~masks[fixed]; vals=cols[fixed]; fibers=[len({c for c,z in zip(C,vals) if z==b}) for b in (False,True)]
  info=1+(max(fibers)-1).bit_length()
  for extra in range(max(0,info-1),len(v)+1):
   if solve(rem,extra):return 1+extra,info
  raise AssertionError
 return bound

def upper(D):
 R=((1<<N)-1)^D; ee=[(i,j) for i,j in E if R>>i&1 and R>>j&1]
 if not ee:return 0
 tau=min(a.bit_count() for a in subsets(R) if all(a>>i&1 or a>>j&1 for i,j in ee))
 return len(ee)+tau-1
if __name__=='__main__':
 hist=Counter();best=[]
 for k in range(2,6):
  for v in combinations(range(N),k):
   D=sum(1<<i for i in v); b=code(D)
   for i,j in combinations(v,2):
    for op in ('and','or'):
     exact,info=b((op,i,j)); hist[k,exact,info]+=1
     if exact>info:best.append((exact-info,exact+upper(D),v,op,i,j,exact,info,upper(D)))
 print('hist',sorted(hist.items()))
 print('improvement cases',len(best)); print('top',sorted(best,reverse=True)[:25])
