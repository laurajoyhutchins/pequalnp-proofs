import PEqualNP.Outside.L_meta_2165
import PEqualNP.Research.PetersenGroupPotential

namespace PEqualNP.Research.Anchored
open PEqualNP.Outside.L_meta_2165_aux
open PEqualNP.Research.BranchBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open BranchGraph BranchGroupsLean CircuitProof CircuitProof.Readers
open PetersenNine PetersenCutTrace PetersenFirstGroup

local instance : DecidableRel petersenGraph.Adj := petersenAdjDecidable

def mask (S : Finset (Fin 9)) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 9 => decide (i ∈ S)))).toNat

theorem mask_lt (S : Finset (Fin 9)) : mask S < 512 := by
  have h := (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 9 => decide (i ∈ S)))).isLt
  simpa [mask] using h

@[simp] theorem mask_test (S : Finset (Fin 9)) (i : Fin 9) :
    (mask S).testBit i.val = true ↔ i ∈ S := by
  change (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => decide (j ∈ S)))).getLsbD i.val = true ↔ _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some, decide_eq_true_eq]

theorem decode_mask (S : Finset (Fin 9)) :
    PetersenMaskBridge.decode PetersenGroupBFS.petersenNine (mask S) = S := by
  ext i
  rw [PetersenMaskBridge.mem_decode]
  exact mask_test S i

theorem mask_union (A B : Finset (Fin 9)) : mask (A ∪ B) = mask A ||| mask B := by
  apply PetersenMaskBridge.decode_inj PetersenGroupBFS.petersenNine (mask_lt (A ∪ B))
    (Nat.or_lt_two_pow (n:=9) (mask_lt A) (mask_lt B))
  change PetersenMaskBridge.decode PetersenGroupBFS.petersenNine (mask (A ∪ B)) = PetersenMaskBridge.decode PetersenGroupBFS.petersenNine (Nat.lor (mask A) (mask B))
  rw [PetersenMaskBridge.decode_or, decode_mask, decode_mask, decode_mask]

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem pop_decode : ∀ m : Fin 512,
    pop m.val = (PetersenMaskBridge.decode PetersenGroupBFS.petersenNine m.val).card := by decide +kernel

theorem pop_mask (S : Finset (Fin 9)) : pop (mask S) = S.card := by
  have h := pop_decode ⟨mask S,mask_lt S⟩
  change pop (mask S) = (PetersenMaskBridge.decode PetersenGroupBFS.petersenNine (mask S)).card at h
  rwa [decode_mask] at h

theorem residual_eq (m i : Nat) : res m i = PetersenGroupBFS.residualNeighbors PetersenGroupBFS.petersenNine m i := rfl

theorem residual_zero (M : Finset (Fin 9)) (i : Fin 9) :
    res (mask M) i.val = 0 ↔ neighborsAfter petersenGraph M i = ∅ := by
  rw [residual_eq]
  have h := @PetersenMaskBridge.residual_zero_iff PetersenGroupBFS.petersenNine petersenGraph petersenAdjDecidable
    petersen_graph_matches_mask (mask M) (mask_lt M) i
  rwa [decode_mask] at h

theorem good_of_twin (M S : Finset (Fin 9)) (h : TwinGroup petersenGraph M S) :
    GoodGroup (mask M) (mask S) := by
  intro i j hi hj hni hnj
  have ni : (neighborsAfter petersenGraph M i).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun e => hni ((residual_zero M i).mpr e))
  have nj : (neighborsAfter petersenGraph M j).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun e => hnj ((residual_zero M j).mpr e))
  rw [residual_eq,residual_eq]
  apply PetersenMaskBridge.decode_inj PetersenGroupBFS.petersenNine
    (PetersenGroupBFS.neighbor_bounded _ _ _ (mask_lt M))
    (PetersenGroupBFS.neighbor_bounded _ _ _ (mask_lt M))
  have ei := @PetersenMaskBridge.decode_neighbors PetersenGroupBFS.petersenNine petersenGraph petersenAdjDecidable petersen_graph_matches_mask (mask M) i
  have ej := @PetersenMaskBridge.decode_neighbors PetersenGroupBFS.petersenNine petersenGraph petersenAdjDecidable petersen_graph_matches_mask (mask M) j
  rw [ei,ej,decode_mask]
  exact h i ((mask_test S i).mp hi) j ((mask_test S j).mp hj) ni nj

theorem groups_valid (M : Finset (Fin 9)) (groups : List (Finset (Fin 9)))
    (h : TwinSteps petersenGraph M groups) : GroupSequence (mask M) (groups.map mask) := by
  induction groups generalizing M with
  | nil => trivial
  | cons S ss ih =>
    refine ⟨mask_lt S, good_of_twin M S h.1, ?_⟩
    rw [←mask_union]
    exact ih _ h.2

theorem groups_remove (M : Finset (Fin 9)) (groups : List (Finset (Fin 9))) :
    removeGroups (mask M) (groups.map mask) = mask (removedThrough M groups) := by
  induction groups generalizing M with
  | nil => rfl
  | cons S ss ih =>
    change removeGroups (mask M ||| mask S) (ss.map mask) = mask (removedThrough (M ∪ S) ss)
    rw [←mask_union,ih]

theorem edgeless_mask (M : Finset (Fin 9)) (h : EdgelessAfter petersenGraph M) :
    EdgelessMask (mask M) := by
  intro i hi
  apply (residual_zero M i).mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨j,hj⟩
  have hj' : petersenGraph.Adj i j ∧ j ∉ M := by
    simpa only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] using hj
  have hi' : i ∉ M := fun e => by
    have ht := (mask_test M i).mpr e
    rw [hi] at ht
    contradiction
  exact h i j hi' hj'.2 hj'.1

theorem graph_group_lower (M : Finset (Fin 9)) (groups : List (Finset (Fin 9)))
    (twins : TwinSteps petersenGraph M groups)
    (finished : EdgelessAfter petersenGraph (removedThrough M groups)) :
    potential (mask M) ≤ groups.length := by
  have h := graph_sequence_lower (mask M) (mask_lt M) (groups.map mask)
    (groups_valid M groups twins) (by rw [groups_remove]; exact edgeless_mask _ finished)
  simpa only [List.length_map] using h

-- The raw roots are paid for as individual branch wires; the remaining
-- internal roots must pay for the residual graph potential.
theorem raw_prefix_budget {m : Nat} (label : Fin 9 → Fin m) (out : Fin m)
    (branches : Finset (Fin m)) (embed : Fin 9 → Fin m)
    (embed_val : ∀ i, (embed i).val = i.val)
    (raw_fixed : ∀ i, embed i ∈ branches → label i = embed i)
    (raw_only : ∀ i, (label i).val < 9 → (label i).val = i.val)
    (cover : ∀ v, label v = out ∨ label v ∈ branches)
    (early : ∀ r ∈ branches, r < out)
    (twins : ∀ r ∈ branches, TwinGroup petersenGraph (below label r) (bucket label r))
    (independent : Independent petersenGraph (bucket label out)) :
    let M := Finset.univ.filter (fun i : Fin 9 => embed i ∈ branches)
    pop (mask M) + potential (mask M) ≤ branches.card := by
  classical
  let M := Finset.univ.filter (fun i : Fin 9 => embed i ∈ branches)
  change pop (mask M) + potential (mask M) ≤ branches.card
  let rawRoots := branches.filter (fun r => r.val < 9)
  let innerRoots := branches.filter (fun r => ¬ r.val < 9)
  let done := rawRoots.sort
  let pending := innerRoots.sort
  have splitMem (r : Fin m) : r ∈ done ++ pending ↔ r ∈ branches := by
    simp only [List.mem_append,done,pending,Finset.mem_sort,rawRoots,innerRoots,Finset.mem_filter]
    by_cases h : r.val < 9 <;> simp [h]
  have sorted : (done ++ pending).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort rawRoots),
      List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort innerRoots), ?_⟩
    intro a ha b hb
    have haM : a ∈ rawRoots := by simpa only [done,Finset.mem_sort] using ha
    have hbM : b ∈ innerRoots := by simpa only [pending,Finset.mem_sort] using hb
    have ha' : a.val < 9 := (Finset.mem_filter.mp haM).2
    have hb' : ¬ b.val < 9 := (Finset.mem_filter.mp hbM).2
    change a.val < b.val
    omega
  have covered : coveredBy label done = M := by
    ext i
    simp only [coveredBy,M,Finset.mem_filter,Finset.mem_univ,true_and,done,Finset.mem_sort,rawRoots]
    constructor
    · rintro ⟨hi,hr⟩
      have he : label i = embed i := Fin.ext ((raw_only i hr).trans (embed_val i).symm)
      rwa [he] at hi
    · intro hi
      rw [raw_fixed i hi]
      exact ⟨hi,(embed_val i).symm ▸ i.isLt⟩
  have cov (v : Fin 9) : label v = out ∨ label v ∈ done ++ pending :=
    (cover v).imp id (splitMem _).mpr
  have valid := sorted_tail_twin_steps petersenGraph label out (done ++ pending) sorted cov
    (fun r hr => early r ((splitMem r).mp hr))
    (fun r hr => twins r ((splitMem r).mp hr)) done pending rfl
  rw [covered] at valid
  have finished : EdgelessAfter petersenGraph (removedThrough M (pending.map (bucket label))) := by
    rw [←covered,removedThrough_coveredBy]
    intro u v hu hv
    have hu' : label u = out := (cover u).resolve_right (fun h => hu (by
      simp only [coveredBy,Finset.mem_filter,Finset.mem_univ,true_and,splitMem]; exact h))
    have hv' : label v = out := (cover v).resolve_right (fun h => hv (by
      simp only [coveredBy,Finset.mem_filter,Finset.mem_univ,true_and,splitMem]; exact h))
    exact independent u (by simp [bucket,hu']) v (by simp [bucket,hv'])
  have cost := graph_group_lower M (pending.map (bucket label)) valid finished
  simp only [List.length_map,pending,Finset.length_sort] at cost
  have rawCard : M.card ≤ rawRoots.card := by
    apply Finset.card_le_card_of_injOn embed
    · intro i hi
      have he : embed i ∈ branches := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨he,(embed_val i).symm ▸ i.isLt⟩
    · intro a ha b hb e
      apply Fin.ext
      rw [←embed_val a,←embed_val b,e]
  have cards : rawRoots.card + innerRoots.card = branches.card :=
    Finset.card_filter_add_card_filter_not (s:=branches) (fun r => r.val < 9)
  rw [pop_mask]
  omega

noncomputable def rawBranches (gs : List Gate) : Finset (Fin 9) := by
  classical
  exact Finset.univ.filter (fun i : Fin 9 => inputWire gs i ∈ circuitBranchWires (n:=9) gs)

theorem least_raw_branch_budget (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out) :
    pop (mask (rawBranches gs)) + potential (mask (rawBranches gs)) + 8 ≤ nonNotCount gs := by
  classical
  have valid := least_petersen_output_valid least
  let outWire : Fin (9 + gs.length) := ⟨out,valid⟩
  have live := least_read_edge_live least petersen_nonconstant petersen_depends petersen_restrict_nonconstant valid
  let label : Fin 9 → Fin (9 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (setInput S) outWire.val = true ↔ BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact petersen_graph_marked_edges S
  have independent (r) : BranchGraph.Independent petersenGraph (bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least petersen_nonconstant)
      petersenGraph computes petersen_graph_alternate_neighbors r
  have labels (v : Fin 9) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    rcases stopped with h | h
    · exact Or.inl h
    · exact Or.inr (in_circuit_branches.mpr h)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : TwinGroup petersenGraph (below label r) (bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live petersenGraph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  have fixed (i : Fin 9) (h : inputWire gs i ∈ branches) : label i = inputWire gs i :=
    FirstBranchRoute.first_of_terminal (readEdge gs) outWire (read_order least.hcl) live
      (Or.inr (in_circuit_branches.mp h))
  have rawOnly (i : Fin 9) (hi : (label i).val < 9) : (label i).val = i.val := by
    have path := FirstBranchRoute.first_path (readEdge gs) outWire (read_order least.hcl) live (inputWire gs i)
    change Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) outWire) (inputWire gs i) (label i) at path
    rcases path.cases_head with eq | ⟨next,edge,rest⟩
    · have e := congrArg Fin.val eq
      change i.val = (label i).val at e
      exact e.symm
    · have hle := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl)
        (FirstBranchRoute.follows_is_read_path (readEdge gs) outWire rest)
      change next.val ≤ (label i).val at hle
      obtain ⟨p,g,hp,hn,ha⟩ := edge.1
      omega
  have graphBound := raw_prefix_budget label outWire branches (inputWire gs)
    (fun _ => rfl) fixed rawOnly labels before twins (independent outWire)
  change pop (mask (rawBranches gs)) + potential (mask (rawBranches gs)) ≤ branches.card at graphBound
  have wireBound := branching_budget least.hcl valid (fun w hw hne => by
    let wire : Fin (9 + gs.length) := ⟨w,hw⟩
    obtain ⟨v,p,g,hg,_,hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
    exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at wireBound
  have total := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at total
  omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem anchor02 (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    (cost : nonNotCount gs ≤ 13)
    (h0 : (0 : Fin 9) ∈ rawBranches gs) (h2 : (2 : Fin 9) ∈ rawBranches gs) :
    allowed (mask (rawBranches gs)) = true := by
  have hb := least_raw_branch_budget gs out least
  have h := allowed_masks ⟨mask (rawBranches gs), mask_lt _⟩ ((mask_test _ 0).mpr h0) ((mask_test _ 2).mpr h2)
  apply h
  change pop (mask (rawBranches gs)) + potential (mask (rawBranches gs)) ≤ 5
  omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem anchor04 (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    (h0 : (0 : Fin 9) ∈ rawBranches gs) (h4 : (4 : Fin 9) ∈ rawBranches gs) : 14 ≤ nonNotCount gs := by
  have hb := least_raw_branch_budget gs out least
  have h := no_mask04 ⟨mask (rawBranches gs), mask_lt _⟩ ((mask_test _ 0).mpr h0) ((mask_test _ 4).mpr h4)
  change 6 ≤ pop (mask (rawBranches gs)) + potential (mask (rawBranches gs)) at h
  omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem anchor46 (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    (h4 : (4 : Fin 9) ∈ rawBranches gs) (h6 : (6 : Fin 9) ∈ rawBranches gs) : 14 ≤ nonNotCount gs := by
  have hb := least_raw_branch_budget gs out least
  have h := no_mask46 ⟨mask (rawBranches gs), mask_lt _⟩ ((mask_test _ 4).mpr h4) ((mask_test _ 6).mpr h6)
  change 6 ≤ pop (mask (rawBranches gs)) + potential (mask (rawBranches gs)) at h
  omega

#print axioms least_raw_branch_budget
#print axioms anchor02
#print axioms anchor04
#print axioms anchor46

end PEqualNP.Research.Anchored
