#!/usr/bin/env node
// Compile public posted gaps into read-only, source-identified task packets.
// Never call the desk claim endpoint. A packet is not ownership or eligibility.
import { readFileSync, writeFileSync, mkdirSync, lstatSync, existsSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
export const SOURCE = 'https://data.pequalnp.com/data/desk/gaps.json';
const hash = b => createHash('sha256').update(b).digest('hex');
const save = (p, v) => writeFileSync(p, JSON.stringify(v, null, 2) + '\n', {flag:'wx'});
export async function compile(base, snapshot, out, observed) {
  const sha = execFileSync('git',['-C',base,'rev-parse','HEAD'],{encoding:'utf8'}).trim();
  if (!/^[0-9a-f]{40}$/.test(sha)) throw Error('invalid upstream revision');
  const raw = readFileSync(snapshot);
  const all = JSON.parse(raw);
  if (!Array.isArray(all.gaps)) throw Error('missing gaps array');
  const guardPath = join(base,'.github/scripts/outside-guard.mjs');
  const guard = await import(pathToFileURL(guardPath).href);
  const ids = new Set();
  for (const g of all.gaps) {
    if (!g || typeof g.id !== 'string' || ids.has(g.id) || !guard.GAP_RE.test(g.id)) throw Error('invalid or duplicate gap ID');
    ids.add(g.id);
  }
  const identity = {source:SOURCE, snapshot_sha256:hash(raw), upstream_sha:sha,
    observed_at:observed, guard_sha256:hash(readFileSync(guardPath)),
    toolchain:readFileSync(join(base,'lean/lean-toolchain'),'utf8').trim(),
    manifest_sha256:hash(readFileSync(join(base,'lean/lake-manifest.json')))};
  mkdirSync(out);
  mkdirSync(join(out,'packets'));
  const rows = [];
  const readModule = m => {
    const p = join(base,'lean',...m.split('.'))+'.lean';
    try { const st=lstatSync(p); return st.isFile() && st.size<=guard.MAX_BYTES ? readFileSync(p) : null; }
    catch(e) { if(e.code==='ENOENT') return null; throw e; }
  };
  for (const g of [...all.gaps].sort((a,b)=>a.id.localeCompare(b.id))) {
    const info = guard.checkGap(all, x=>x.id===g.id, g.file);
    const dir = join(out,'packets',info.id);
    mkdirSync(dir);
    let closure = null, blocker = null;
    try { closure = guard.importClosure(info.imports,readModule,g.module); }
    catch(e) { blocker=String(e.message); }
    const pathExists = existsSync(join(base,g.file));
    const context = {};
    // Copy only documented research fields, not arbitrary desk metadata.
    for (const key of ['title','context','sketch','refutation','shard_spec','dead','unlocks','depends_on','status']) {
      if (Object.hasOwn(g,key)) context[key]=g[key];
    }
    const deps = Array.isArray(g.depends_on) && g.depends_on.every(d=>typeof d==='string')
      ? g.depends_on : null;
    const sources = closure ? [...closure.base,...closure.outside].map(module=>({
      module, path:'lean/'+module.replaceAll('.','/')+'.lean', sha256:hash(readModule(module))
    })) : [];
    const packet={...identity, id:info.id, file:g.file, module:g.module, statement:info.statement,
      permitted_project_imports:info.imports, context, closure, closure_blocker:blocker,
      closure_sources:sources, path_exists:pathExists, explicit_dependencies:deps,
      missing_dependency_ids:deps===null?null:deps.filter(d=>!ids.has(d)),
      eligibility:'unknown: consult live desk; public posting does not confer ownership',
      local_verification:'not_run', authoritative_verdict:'not_reconciled'};
    save(join(dir,'packet.json'),packet);
    writeFileSync(join(dir,'statement.txt'),info.statement,{flag:'wx'});
    writeFileSync(join(dir,'Skeleton.lean'),['import Mathlib',...info.imports.map(m=>'import '+m),'',
      'theorem '+g.module+' : '+info.statement+' := by','  sorry',''].join('\n'),{flag:'wx'});
    rows.push({id:info.id,file:g.file,packet:'packets/'+info.id+'/packet.json',
      status:typeof g.status==='string'?g.status:null, depends_on:deps, closure_blocker:blocker,path_exists:pathExists});
  }
  // Unknown dependency lists and non-open statuses are not silently treated as open.
  const reverse=new Map(rows.map(row=>[row.id,[]]));
  for(const row of rows) for(const dep of row.depends_on??[]) if(reverse.has(dep)) reverse.get(dep).push(row.id);
  for(const row of rows) {
    const seen=new Set([row.id]), pending=[...reverse.get(row.id)];
    while(pending.length){const id=pending.pop(); if(seen.has(id))continue; seen.add(id); pending.push(...reverse.get(id));}
    seen.delete(row.id);
    row.known_downstream=[...seen].sort();
  }
  save(join(out,'index.json'),{...identity,scope:'public posted gaps; explicit edges only; not a claim allocator',gaps:rows});
  return rows.length;
}
if (process.argv[1] && import.meta.url===pathToFileURL(resolve(process.argv[1])).href) {
  const [base,snapshot,out,observed]=process.argv.slice(2);
  if(!base||!snapshot||!out||!observed||!Number.isFinite(Date.parse(observed))) throw Error('usage: packets.mjs BASE SNAPSHOT NEW_OUTPUT OBSERVED_ISO');
  console.log('Public research packets: '+await compile(resolve(base),resolve(snapshot),resolve(out),observed));
}
