// Public screening, not lease ownership or authoritative eligibility.
export const UPSTREAM='open-goat/pequalnp-proofs';
const ID=/^L-[a-z0-9]+(?:-[a-z0-9]+)*$/;
const ids=(xs,name)=>{
  if(!Array.isArray(xs)) throw Error('invalid '+name);
  const out=xs.map(x=>typeof x==='string'?x:x?.id);
  if(out.some(x=>typeof x!=='string'||!ID.test(x))) throw Error('invalid '+name+' ID');
  return new Set(out);
};
export function readDesk(all,observed,maxAge=1200){
  if(all?.repo!=='https://github.com/'+UPSTREAM||!Array.isArray(all.gaps)) throw Error('unexpected desk repository or gaps');
  const delta=(Date.parse(observed)-Date.parse(all.updated_at))/1000;
  if(!Number.isFinite(delta)||delta< -120||delta>maxAge) throw Error('stale or invalid source timestamp');
  if(!all.withdrawn||typeof all.withdrawn!=='object'||Array.isArray(all.withdrawn)) throw Error('invalid withdrawn list');
  const checked=ids(all.checked,'checked'),withdrawn=ids(Object.keys(all.withdrawn),'withdrawn'),paused=ids(all.paused,'paused');
  if(!Number.isSafeInteger(all.offerable_by_hub)||all.offerable_by_hub<0||all.offerable_by_hub>all.gaps.length||
      !all.not_offerable||typeof all.not_offerable!=='object') throw Error('invalid public allocation summary');
  const summary={source_updated_at:all.updated_at,upstream_repository:UPSTREAM,offerable_by_hub:all.offerable_by_hub,
    not_offerable:all.not_offerable,lanes:all.lanes??null,retired:{checked:[...checked].sort(),withdrawn:[...withdrawn].sort(),paused:[...paused].sort()}};
  function screen(g,{pathExists=false,closureBlocker=null}={}){
    const reasons=[];
    if(checked.has(g.id)) reasons.push('checked');
    if(withdrawn.has(g.id)) reasons.push('withdrawn');
    if(paused.has(g.id)) reasons.push('paused');
    if(pathExists) reasons.push('upstream_file_exists');
    if(closureBlocker!==null) reasons.push('import_closure_blocked');
    if(!Number.isSafeInteger(g.weight)||!Number.isSafeInteger(g.pr_open)||g.pr_open<0||typeof g.lane!=='string') reasons.push('allocation_fields_unknown');
    else{
      // The current desk distinguishes weight-one tasks and open-PR tasks from its offerable pool.
      // These are conservative local exclusion signals, not an attempt to reconstruct the desk allocator.
      if(g.weight<=1) reasons.push('low_weight');
      if(g.pr_open>0) reasons.push('pr_already_open');
    }
    return {state:reasons.length?'excluded_from_local_shortlist':'requires_live_desk_lease',reasons,
      weight:g.weight??null,pr_open:g.pr_open??null,lane:g.lane??null,parallel:g.parallel??null};
  }
  return {summary,screen};
}
