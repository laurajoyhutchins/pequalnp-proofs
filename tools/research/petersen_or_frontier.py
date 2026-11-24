"""Exact full-signature forward-prefix experiment for L-meta-1674/1675.
Run with Python 3, no dependencies. This is not a lower-bound certificate.
"""
from itertools import combinations, permutations, product
from functools import lru_cache
N = 9
E = {tuple(sorted(e)) for e in [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]}
P = list(combinations(range(N),2))
FULL = (1 << (1 << N)) - 1
X = [sum(1 << r for r in range(1 << N) if r >> i & 1) for i in range(N)]
F = 0
for i,j in E: F |= X[i] & X[j]
AND = {X[i] & X[j] for i,j in P}
degrees = [sum(i in e for e in E) for i in range(N)]
a = [i for i in range(N) if degrees[i] == 2]
b = [i for i in range(N) if degrees[i] == 3]
autos = []
for ap,bp in product(permutations(a),permutations(b)):
    p = dict(zip(a+b,ap+bp))
    p = tuple(p[i] for i in range(N))
    if {tuple(sorted((p[i],p[j]))) for i,j in E} == E: autos.append(p)
reps = [(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)]
orbits = [{tuple(sorted((p[i],p[j]))) for p in autos} for i,j in reps]
assert set.union(*orbits) == set(P) and sum(map(len,orbits)) == len(P)
print("automorphisms", len(autos), "pair orbit sizes", list(map(len,orbits)))

def op(o,ws):
    if o == "and": return all(ws)
    if o == "or": return any(ws)
    return not (ws[0] if ws else False)

def run(n,gs,out,row):
    w = [bool(row >> i & 1) for i in range(n)]
    for o,ps in gs:
        w.append(op(o,[w[j] if j < len(w) else False for j in ps]))
    return w[out] if out < len(w) else False,w

def hoist(n,gs,out,k,replacement):
    m = len(gs)
    sentinel = n+m
    order = [k]+[j for j in range(m) if j != k]
    pos = {j:n+i for i,j in enumerate(order)}
    def ref(w,at):
        if w < n: return w
        if w >= n+at: return sentinel
        return pos[w-n]
    new = [replacement if j == k else (gs[j][0],[ref(w,j) for w in gs[j][1]]) for j in order]
    return new,ref(out,m)

import random
rng = random.Random(1674)
trials = comparisons = semantic = 0
for _ in range(3000):
    n = rng.randint(2,5)
    m = rng.randint(2,12)
    k = rng.randrange(m)
    u,v = rng.sample(range(n),2)
    gs = [(rng.choice(["and","or","not"]),[rng.randrange(n+m+3) for _ in range(rng.randrange(3))]) for i in range(m)]
    if k > 0 and rng.randrange(2):
        gs[k-1] = ("and",[u,v])
        gs[k] = ("or",[n+k-1])
        semantic += 1
    else: gs[k] = ("and",[u,v])
    out = rng.randrange(n+m+3)
    ng,no = hoist(n,gs,out,k,("and",[u,v]))
    trials += 1
    for row in range(1 << n):
        old,w = run(n,gs,out,row)
        new,nw = run(n,ng,no,row)
        assert old == new and w[n+k] == nw[n]
        comparisons += 1
print("hoist trials",trials,"semantic aliases",semantic,"assignment comparisons",comparisons)

for u,v in [(0,2),(0,3)]:
    seed = X[u] | X[v]
    base = frozenset(X+[seed])
    stab = [p for p in autos if {p[u],p[v]} == {u,v}]
    witnesses = []
    for i in range(N):
        rs = [(r,r^(1<<i)) for r in range(1<<N) if not r>>i&1 and ((F>>r)^(F>>(r^(1<<i))))&1 and ((seed>>r)^(seed>>(r^(1<<i))))&1==0]
        assert rs
        witnesses.append(rs[0])
    sigs = {0,FULL}|{FULL^x for x in base}|{f(a,b) for a,b in combinations(base,2) for f in [int.__and__,int.__or__]}|set(base)
    aliases = sigs & (set(base)|{0,FULL})
    remaining = sigs-aliases-AND
    rows = [[sum(((r>>i)&1)<<p[i] for i in range(N)) for r in range(1<<N)] for p in stab]
    @lru_cache(None)
    def move(s,pi):
        return sum(((s>>r)&1)<<rr for r,rr in enumerate(rows[pi]))
    def canonical(s):
        return min(tuple(sorted(move(x,pi) for x in s)) for pi in range(len(stab)))
    def children(st,banned):
        bank = base|set(st)
        vals = {FULL^a for a in bank}
        for a,b in combinations(bank,2): vals.update((a&b,a|b))
        return vals-bank-{0,FULL}-banned
    print("OR seed",u,v,"stabilizer",len(stab),"second signatures",len(sigs),"aliases/constants",len(aliases),"raw ANDs",len(sigs&AND),"remaining",len(remaining),"remaining orbits",len({canonical((s,)) for s in remaining}),"witnesses",witnesses)
    for banned in [set(),AND]:
        front = {()}
        counts = []
        for depth in range(1,3):
            front = {canonical((*st,a)) for st in front for a in children(st,banned)}
            counts.append(len(front))
        print("prefix frontier",u,v,"ban",bool(banned),"depths",counts)
