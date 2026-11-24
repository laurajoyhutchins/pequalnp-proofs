import test from 'node:test';
import assert from 'node:assert/strict';
import {readDesk,UPSTREAM} from './desk_screen.mjs';
const observed='2026-11-24T15:50:00Z';
const g={id:'L-meta-1',weight:5,pr_open:0,lane:'main'};
const fixture={repo:'https://github.com/'+UPSTREAM,updated_at:'2026-11-24T15:49:00Z',
  gaps:[g],checked:[],withdrawn:{},paused:[],not_offerable:{pr_open:0,weight_1:0},offerable_by_hub:1};
test('fresh posting never confers eligibility',()=>{
  const d=readDesk(fixture,observed);
  assert.equal(d.screen(g).state,'requires_live_desk_lease');
  assert.equal(d.summary.source_updated_at,fixture.updated_at);
});
test('wrong upstream and stale source cannot be refreshed by a new observation',()=>{
  assert.throws(()=>readDesk({...fixture,repo:'https://github.com/other/pequalnp-proofs'},observed));
  assert.throws(()=>readDesk({...fixture,updated_at:'2026-11-24T15:00:00Z'},observed));
  assert.throws(()=>readDesk({...fixture,updated_at:'not-a-time'},observed));
});
test('low-weight and open-PR postings are screened out',()=>{
  const d=readDesk(fixture,observed);
  assert.deepEqual(d.screen({...g,weight:1}).reasons,['low_weight']);
  assert.deepEqual(d.screen({...g,pr_open:1}).reasons,['pr_already_open']);
  assert.deepEqual(d.screen({...g,weight:undefined}).reasons,['allocation_fields_unknown']);
});
test('retired, paused, existing-file and closure conflicts fail closed',()=>{
  const d=readDesk({...fixture,checked:[{id:g.id}],withdrawn:{[g.id]:'stood down'},paused:[g.id]},observed);
  assert.deepEqual(d.screen(g,{pathExists:true,closureBlocker:'missing'}).reasons,
    ['checked','withdrawn','paused','upstream_file_exists','import_closure_blocked']);
});
