from itertools import combinations, combinations_with_replacement
from time import perf_counter
import json,resource

EDGES=((0,1),(2,3),(3,4),(2,4))
def truth(x): return any(x>>i&1 and x>>j&1 for i,j in EDGES)
def run(rows, budget=5):
    U=(1<<len(rows))-1
    target=sum(1<<i for i,x in enumerate(rows) if truth(x))
    init=frozenset({0,*[sum(1<<i for i,x in enumerate(rows) if x>>j&1) for j in range(5)]})
    states={init}; log=[]; t=perf_counter()
    for depth in range(budget+1):
        row={'depth':depth,'states':len(states),'elapsed_s':round(perf_counter()-t,6)};log.append(row)
        if any(target in s for s in states): return {'rows':rows,'result':'reachable','log':log,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        if depth==budget:break
        # At final step decide target membership without building successors.
        if depth+1==budget:
            attempts=0
            for s in states:
                # Target false is already available; true is a legal zero-input AND.
                if target==U or (U^target) in s: return {'rows':rows,'result':'reachable','log':log}
                for a,b in combinations_with_replacement(s,2):
                    attempts+=1
                    if a&b==target or a|b==target:return {'rows':rows,'result':'reachable','log':log}
            row['final_binary_pairs']=attempts
            return {'rows':rows,'result':'excluded','log':log,'elapsed_s':round(perf_counter()-t,6),'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        nxt=set(); attempts=0; new=0
        for s in states:
            out={U,*(U^x for x in s)}
            for a,b in combinations_with_replacement(s,2):out.update((a&b,a|b))
            attempts+=len(out); new+=len(out-s)
            for x in out-s:nxt.add(s|{x})
        row.update(distinct_gate_results=attempts,new_state_transitions=new)
        states=nxt

if __name__=='__main__':
    import sys
    pos=[(1<<i)|(1<<j) for i,j in EDGES]
    neg=[x for x in range(32) if not truth(x) and all(truth(x|1<<i) for i in range(5) if not x>>i&1)]
    rows=sorted(pos+neg)
    if len(sys.argv)>1 and sys.argv[1]=='full': rows=list(range(32))
    elif len(sys.argv)>1 and sys.argv[1]=='augmented': rows=sorted(set(rows+[0,31]+[1<<i for i in range(5)]))
    print(json.dumps(run(rows),indent=2))
