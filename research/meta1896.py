from itertools import combinations
from collections import Counter
N=13; ALL=(1<<N)-1; D=(0,1,3,9)
lines=[sum(1<<((l+d)%N) for d in D) for l in range(N)]
points=[sum(1<<l for l in range(N) if lines[l]>>p&1) for p in range(N)]
def union_masks(masks,s):
    u=0
    for i,v in enumerate(masks):
        if s>>i&1:u|=v
    return u

def generic():
    for s in range(1<<N):
        t=ALL^union_masks(points,s)
        if ALL^union_masks(lines,t)!=s:continue
        if any(s&~line==0 for line in lines):continue
        if any(t&~point==0 for point in points):continue
        yield s|(t<<N)

def subsets(x):
    s=x
    while True:
        yield s
        if s==0:break
        s=(s-1)&x

def shape(x):return ((x&ALL).bit_count(),(x>>N).bit_count())

G=list(generic()); assert len(G)==468
covered=Counter(s for g in G for s in subsets(g))
independent=set()
for p in range(1<<N):
    for l in subsets(ALL^union_masks(points,p)):
        independent.add(p|(l<<N))
minimal=[]
for x in independent-covered.keys():
    if all(x^(1<<i) in covered for i in range(26) if x>>i&1):minimal.append(x)
print('generic',Counter(map(shape,G)))
print('independent',len(independent),'covered',len(covered))
print('minimal invisible',Counter(map(shape,minimal)))
print('pair multiplicities',Counter(covered[x] for x in independent if x.bit_count()==2))
for k in range(2,8):
    print('independent size',k,'coverage counts', sorted(Counter(covered[x] for x in independent if x.bit_count()==k).items()))
assert all(covered[x] for x in independent if x.bit_count()<=2)

# Independent cross-check from the 3-subset characterization.
triangles=[sum(1<<i for i in c) for c in combinations(range(N),3)
           if all(not all(line>>i&1 for i in c) for line in lines)]
triads=[sum(1<<i for i in c) for c in combinations(range(N),3)
        if all(not all(point>>i&1 for i in c) for point in points)]
assert len(triangles)==len(triads)==234
from_triples={s|((ALL^union_masks(points,s))<<N) for s in triangles}
from_triples|={(ALL^union_masks(lines,t))|(t<<N) for t in triads}
assert from_triples==set(G)
collinear={s for line in lines for s in subsets(line) if s.bit_count()==3}
concurrent={t<<N for point in points for t in subsets(point) if t.bit_count()==3}
assert len(collinear)==len(concurrent)==52
assert set(minimal)==collinear|concurrent
assert all((x in covered)==(not any(x&m==m for m in minimal)) for x in independent)
assert {shape(x) for x in G}=={(3,4),(4,3)}

# Exact circuit-model evaluation on all 520 care inputs.
gates=[]
def add(op,a,b):
    gates.append((op,a,b));return 25+len(gates)
def ors(ids):
    it=iter(ids);w=next(it)
    for i in it:w=add('or',w,i)
    return w
star=[]
for l,line in enumerate(lines):
    star.append(add('and',13+l,ors(i for i in range(N) if line>>i&1)))
out=ors(star)
def evaluate(x):
    w=[bool(x>>i&1) for i in range(26)]
    for op,a,b in gates:w.append((w[a] or w[b]) if op=='or' else (w[a] and w[b]))
    return w[out]
P=[(1<<p)|(1<<(N+l)) for l in range(N) for p in range(N) if lines[l]>>p&1]
assert len(P)==52 and all(map(evaluate,P)) and not any(map(evaluate,G))
assert Counter(op for op,_,_ in gates)=={'and':13,'or':51}
print('All exact geometry and star-circuit assertions passed.')
