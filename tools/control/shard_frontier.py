"""Publish a bounded connector-readable manifest and lossless row shards."""
import json,hashlib
from pathlib import Path
LIMIT=400_000
def encode(x):return (json.dumps(x,separators=(',',':'),ensure_ascii=False,sort_keys=True)+'\n').encode()
def write(path,x):
    data=encode(x)
    if len(data)>LIMIT:raise ValueError('frontier connector size bound exceeded: '+str(path))
    path.write_bytes(data)
    return hashlib.sha256(data).hexdigest()
def split(out):
    out=Path(out);index=json.loads((out/'index.json').read_bytes())
    rows=index.pop('gaps')
    retired=index.pop('retired')
    # Avoid duplicating potentially large detailed lists in the manifest.
    allocation=index.pop('allocation_summary')
    allocation.pop('retired',None)
    public=index.pop('public_research',{})
    selection=public.pop('selection_evidence',{})
    index['public_research']=public
    index['allocation_summary']=allocation
    index['selection_evidence_counts']={k:len(v) for k,v in selection.items()}
    d=out/'frontier';d.mkdir()
    parts=[]
    cur=[]
    def flush():
        if not cur:return
        path=f'frontier/rows-{len(parts):04d}.json'
        payload={'upstream_sha':index['upstream_sha'],'snapshot_sha256':index['snapshot_sha256'],'gaps':cur}
        digest=write(out/path,payload)
        parts.append({'path':path,'count':len(cur),'first':cur[0]['id'],'last':cur[-1]['id'],'sha256':digest})
    for row in rows:
        if len(encode({'gaps':cur+[row]}))>LIMIT-1024:
            flush();cur=[]
        cur.append(row)
    flush()
    records=[]
    for kind,values in retired.items():
        # Fixed-width pages keep the retired-ID list scalable too.
        for i in range(0,len(values),5000):
            path=f'frontier/{kind}-{i//5000:04d}.json'
            h=write(out/path,{'kind':kind,'ids':values[i:i+5000]})
            records.append({'kind':kind,'path':path,'count':len(values[i:i+5000]),'sha256':h})
    index['schema']='research-frontier/2'
    index['gap_count']=len(rows)
    index['row_shards']=parts
    index['retired_shards']=records
    index['retired_counts']={k:len(v) for k,v in retired.items()}
    # Compact rows for all posted gaps, enough for task screening before detailed shard retrieval.
    shortlist=[{'id':r['id'],'packet':r['packet'],'screening':r['screening']['state'],
                'reasons':r['screening']['reasons'],'weight':r['screening']['weight'],
                'official_plan_reference':r.get('official_plan_reference',False)}
               for r in rows]
    for i in range(0,len(shortlist),500):
        path=f'frontier/short-{i//500:04d}.json'
        h=write(out/path,{'upstream_sha':index['upstream_sha'],'snapshot_sha256':index['snapshot_sha256'],'gaps':shortlist[i:i+500]})
        index.setdefault('shortlist_shards',[]).append({'path':path,'count':len(shortlist[i:i+500]),'sha256':h})
    index['screening_counts']={s:sum(r['screening']['state']==s for r in rows) for s in ('excluded_from_local_shortlist','requires_live_desk_lease')}
    index['selection_evidence_path']='knowledge/summary.json'
    write(out/'index.json',index)
if __name__=='__main__':
    import sys
    split(sys.argv[1])
