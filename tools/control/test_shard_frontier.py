import json,tempfile,unittest,hashlib
from pathlib import Path
from shard_frontier import split,LIMIT
class Shards(unittest.TestCase):
    def test_lossless_bounded_shards(self):
        rows=[{'id':f'L-meta-{i:04d}','packet':f'packets/L-meta-{i:04d}/packet.json','title':'x'*1200,
               'screening':{'state':'requires_live_desk_lease','reasons':[],'weight':5}} for i in range(1500)]
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            index={'gaps':rows,'retired':{'checked':['L-meta-9999'],'withdrawn':[],'paused':[]},'allocation_summary':{'retired':{}},
                   'upstream_sha':'a'*40,'snapshot_sha256':'b'*64,'public_research':{'selection_evidence':{'test':['x']}}}
            (p/'index.json').write_text(json.dumps(index))
            split(p);x=json.loads((p/'index.json').read_bytes())
            self.assertEqual(x['gap_count'],len(rows));self.assertGreater(len(x['row_shards']),1)
            recovered=[]
            for s in x['row_shards']:
                raw=(p/s['path']).read_bytes()
                self.assertLessEqual(len(raw),LIMIT);self.assertEqual(hashlib.sha256(raw).hexdigest(),s['sha256'])
                recovered.extend(json.loads(raw)['gaps'])
            self.assertEqual(rows,recovered)
            self.assertEqual(x['retired_counts']['checked'],1)
            self.assertEqual(x['screening_counts']['requires_live_desk_lease'],1500)
