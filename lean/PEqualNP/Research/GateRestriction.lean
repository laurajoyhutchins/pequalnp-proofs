import PEqualNP.Research.GateElimination
namespace PEqualNP.Research.GateElimination
open PEqualNP.CircuitLowerBounds
inductive Ref where
  | lit (b : Bool)
  | wire (i : Nat)
  deriving DecidableEq

def Ref.val (r : Ref) (w : List Bool) : Bool := match r with
  | .lit b => b
  | .wire i => w.getD i false

def Ref.valid (r : Ref) (n : Nat) : Prop := match r with
  | .lit _ => True
  | .wire i => i < n

def evalOpt (g : Option Gate) (w : List Bool) : List Bool := match g with
  | none => w
  | some g => step w g

def emit (op : GateOp) (n : Nat) (ins : List Nat) : Option Gate × Ref :=
  (some ⟨op, ins⟩, .wire n)

def simplifyAnd (n : Nat) (rs : List Ref) : Option Gate × Ref := match rs with
  | [] => (none, .lit true)
  | [r] => (none, r)
  | [.lit false, _] | [_, .lit false] => (none, .lit false)
  | [.lit true, r] | [r, .lit true] => (none, r)
  | [.wire i, .wire j] => emit .and n [i,j]
  | _ => (none, .lit false)

def simplifyOr (n : Nat) (rs : List Ref) : Option Gate × Ref := match rs with
  | [] => (none, .lit false)
  | [r] => (none, r)
  | [.lit true, _] | [_, .lit true] => (none, .lit true)
  | [.lit false, r] | [r, .lit false] => (none, r)
  | [.wire i, .wire j] => emit .or n [i,j]
  | _ => (none, .lit false)

def simplifyNot (n : Nat) (rs : List Ref) : Option Gate × Ref := match rs with
  | [] => (none, .lit true)
  | .lit b :: _ => (none, .lit (!b))
  | .wire i :: _ => emit .not n [i]

def simplify (op : GateOp) (n : Nat) (rs : List Ref) : Option Gate × Ref := match op with
  | .and => simplifyAnd n rs
  | .or => simplifyOr n rs
  | .not => simplifyNot n rs
  | _ => (none, .lit false)

def basis : GateOp → Prop
  | .and | .or | .not => True
  | _ => False

def LocalSound (op : GateOp) (rs : List Ref) (w : List Bool) : Prop :=
  let p := simplify op w.length rs
  p.2.valid (evalOpt p.1 w).length ∧
  p.2.val (evalOpt p.1 w) = op.eval (rs.map (fun r => r.val w))

theorem local_sound (op : GateOp) (rs : List Ref) (w : List Bool)
    (hop : basis op) (hlen : rs.length ≤ 2) (hv : ∀ r ∈ rs, r.valid w.length) :
    LocalSound op rs w := by
  cases op with
  | and =>
    rcases rs with _ | ⟨a, rs⟩
    · simp [LocalSound, simplify, simplifyAnd, Ref.valid, Ref.val, GateOp.eval]
    rcases rs with _ | ⟨b, rs⟩
    · simp [LocalSound, simplify, simplifyAnd, Ref.val, evalOpt, GateOp.eval, hv a (by simp)]
    have hz : rs = [] := by cases rs <;> simp_all
    subst rs
    cases a <;> cases b <;> rename_i a b
    all_goals try cases a
    all_goals try cases b
    all_goals simp_all [LocalSound, simplify, simplifyAnd, Ref.valid, Ref.val, evalOpt, emit, step, GateOp.eval, List.getD_eq_getElem?_getD]
  | or =>
    rcases rs with _ | ⟨a, rs⟩
    · simp [LocalSound, simplify, simplifyOr, Ref.valid, Ref.val, GateOp.eval]
    rcases rs with _ | ⟨b, rs⟩
    · simp [LocalSound, simplify, simplifyOr, Ref.val, evalOpt, GateOp.eval, hv a (by simp)]
    have hz : rs = [] := by cases rs <;> simp_all
    subst rs
    cases a <;> cases b <;> rename_i a b
    all_goals try cases a
    all_goals try cases b
    all_goals simp_all [LocalSound, simplify, simplifyOr, Ref.valid, Ref.val, evalOpt, emit, step, GateOp.eval, List.getD_eq_getElem?_getD]
  | not =>
    rcases rs with _ | ⟨a, rs⟩
    · simp [LocalSound, simplify, simplifyNot, Ref.valid, Ref.val, GateOp.eval]
    cases a <;> simp_all [LocalSound, simplify, simplifyNot, Ref.valid, Ref.val, evalOpt, emit, step, GateOp.eval, List.getD_eq_getElem?_getD]
  | mod => contradiction
  | maj => contradiction

theorem opt_length (g : Option Gate) (w : List Bool) :
    (evalOpt g w).length = w.length + g.toList.length := by
  cases g <;> simp [evalOpt, step]

theorem val_preserve (r : Ref) (g : Option Gate) (w : List Bool) (h : r.valid w.length) :
    r.val (evalOpt g w) = r.val w := by
  cases r with
  | lit => rfl
  | wire i =>
    cases g with
    | none => rfl
    | some g =>
      simp only [Ref.valid] at h
      simp [Ref.val, evalOpt, step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem valid_preserve (r : Ref) (g : Option Gate) (w : List Bool) (h : r.valid w.length) :
    r.valid (evalOpt g w).length := by
  cases r with
  | lit => trivial
  | wire i => simp only [Ref.valid] at *; rw [opt_length]; omega

def Inv (rs : List Ref) (old new : List Bool) : Prop :=
  old = rs.map (fun r => r.val new) ∧ ∀ r ∈ rs, r.valid new.length

theorem getD_map_ref (rs : List Ref) (w : List Bool) (i : Nat) :
    (rs.map (fun r => r.val w)).getD i false = (rs.getD i (.lit false)).val w := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : rs[i]? <;> rfl

theorem valid_getD (rs : List Ref) (w : List Bool) (i : Nat)
    (hv : ∀ r ∈ rs, r.valid w.length) : (rs.getD i (.lit false)).valid w.length := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : rs[i]? with
  | none => trivial
  | some a => exact hv a (List.mem_of_getElem? h)

def transformStep (n : Nat) (acc : List Ref × List Gate) (g : Gate) : List Ref × List Gate :=
  let p := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (.lit false))
  (acc.1 ++ [p.2], acc.2 ++ p.1.toList)

def Well (g : Gate) : Prop := basis g.op ∧ g.inputs.length ≤ 2

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem opt_fold (gs : List Gate) (w : List Bool) (g : Option Gate) :
    (gs ++ g.toList).foldl step w = evalOpt g (gs.foldl step w) := by
  cases g <;> simp [List.foldl_append, evalOpt]

theorem transform_step_sound (gs : List Gate) (rs : List Ref) (old x : List Bool) (g : Gate)
    (h : Inv rs old (gs.foldl step x)) (hg : Well g) :
    Inv (transformStep x.length (rs, gs) g).1 (step old g)
      ((transformStep x.length (rs, gs) g).2.foldl step x) := by
  let w := gs.foldl step x
  let ins := g.inputs.map fun i => rs.getD i (.lit false)
  let p := simplify g.op w.length ins
  have hp := local_sound g.op ins w hg.1 (by simpa [ins] using hg.2) (by
    intro r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact valid_getD rs w i h.2)
  change p.2.valid (evalOpt p.1 w).length ∧ p.2.val (evalOpt p.1 w) = _ at hp
  have hm : transformStep x.length (rs, gs) g = (rs ++ [p.2], gs ++ p.1.toList) := by
    simp [transformStep, p, w, ins, fold_length]
  rw [hm]
  simp only [opt_fold]
  change Inv (rs ++ [p.2]) (step old g) (evalOpt p.1 w)
  constructor
  · unfold step
    rw [List.map_append]
    have heq : rs.map (fun r => r.val (evalOpt p.1 w)) = old := by
      rw [h.1]
      exact List.map_congr_left (fun r hr => val_preserve r p.1 w (h.2 r hr))
    rw [heq]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [hp.2]
    congr 1
    rw [h.1]
    simp only [ins, List.map_map, Function.comp_def, getD_map_ref]
    rfl
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact valid_preserve r p.1 w (h.2 r hr)
    · simp only [List.mem_singleton] at hr
      rw [hr]; exact hp.1

theorem transform_sound (gs : List Gate) (rs : List Ref) (pre : List Gate) (old x : List Bool)
    (h : Inv rs old (pre.foldl step x)) (hg : ∀ g ∈ gs, Well g) :
    Inv (gs.foldl (transformStep x.length) (rs,pre)).1 (gs.foldl step old)
      ((gs.foldl (transformStep x.length) (rs,pre)).2.foldl step x) := by
  induction gs generalizing rs pre old with
  | nil => exact h
  | cons g gs ih =>
    let a := transformStep x.length (rs,pre) g
    have hh := transform_step_sound pre rs old x g h (hg g (by simp))
    change Inv a.1 (step old g) (a.2.foldl step x) at hh
    simp only [List.foldl_cons]
    exact ih a.1 a.2 (step old g) hh (fun g' hg' => hg g' (by simp [hg']))

-- Count exactly the omitted original indices, not wire occurrences.
def omissions (n : Nat) (acc : List Ref × List Gate) : List Gate → Nat
  | [] => 0
  | g :: gs =>
    let nxt := transformStep n acc g
    (if nxt.2.length = acc.2.length then 1 else 0) + omissions n nxt gs

theorem step_budget (n : Nat) (acc : List Ref × List Gate) (g : Gate) :
    (transformStep n acc g).2.length = acc.2.length ∨
    (transformStep n acc g).2.length = acc.2.length + 1 := by
  unfold transformStep
  simp only [List.length_append]
  cases (simplify g.op (n + acc.2.length) (List.map (fun i => acc.1.getD i (.lit false)) g.inputs)).1 <;> simp

theorem exact_budget (n : Nat) (gs : List Gate) (acc : List Ref × List Gate) :
    (gs.foldl (transformStep n) acc).2.length + omissions n acc gs = acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [omissions]
  | cons g gs ih =>
    simp only [List.foldl_cons, omissions, List.length_cons]
    have h := ih (transformStep n acc g)
    rcases step_budget n acc g with he | he
    · simp only [he, ite_true] at *; omega
    · have hne : (transformStep n acc g).2.length ≠ acc.2.length := by omega
      simp only [hne, ite_false] at *; omega

-- The output may be an existing wire or the missing false wire for zero overhead.
-- True needs a single empty AND, matching the actual evaluator.
def finish (n : Nat) (acc : List Ref × List Gate) (o : Nat) : Circuit :=
  match acc.1.getD o (.lit false) with
  | .wire i => ⟨acc.2, i⟩
  | .lit false => ⟨acc.2, n + acc.2.length⟩
  | .lit true => ⟨acc.2 ++ [⟨.and, []⟩], n + acc.2.length⟩

theorem finish_sound (acc : List Ref × List Gate) (old x : List Bool) (o : Nat)
    (h : Inv acc.1 old (acc.2.foldl step x)) :
    (finish x.length acc o).eval x = old.getD o false := by
  rw [h.1, getD_map_ref]
  unfold finish
  cases hr : acc.1.getD o (.lit false) with
  | wire i => rfl
  | lit b =>
    cases b
    · simp only [Circuit.eval, Circuit.wires, Ref.val]
      change (acc.2.foldl step x).getD (x.length + acc.2.length) false = false
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by rw [fold_length]; exact Nat.le_refl _)]
      rfl
    · simp only [Circuit.eval, Circuit.wires, Ref.val, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (step (acc.2.foldl step x) ⟨.and, []⟩).getD (x.length + acc.2.length) false = true
      simp [step, GateOp.eval, List.getD_eq_getElem?_getD, fold_length]

theorem finish_budget (n : Nat) (acc : List Ref × List Gate) (o : Nat) :
    (finish n acc o).size ≤ acc.2.length + 1 := by
  unfold finish
  cases h : acc.1.getD o (.lit false) with
  | wire i => simp [Circuit.size]
  | lit b => cases b <;> simp [Circuit.size]

def restrictCircuit (n : Nat) (rs : List Ref) (C : Circuit) : Circuit :=
  finish n (C.gates.foldl (transformStep n) (rs, [])) C.output

theorem restrict_semantics (C : Circuit) (rs : List Ref) (x : List Bool)
    (hv : ∀ r ∈ rs, r.valid x.length) (hg : ∀ g ∈ C.gates, Well g) :
    (restrictCircuit x.length rs C).eval x = C.eval (rs.map (fun r => r.val x)) := by
  let old := rs.map (fun r => r.val x)
  have h : Inv rs old (([] : List Gate).foldl step x) := ⟨rfl, hv⟩
  have hs := transform_sound C.gates rs [] old x h hg
  exact finish_sound _ _ _ C.output hs

theorem restrict_budget (C : Circuit) (rs : List Ref) (n : Nat) :
    (restrictCircuit n rs C).size + omissions n (rs, []) C.gates ≤ C.size + 1 := by
  have h := exact_budget n C.gates (rs, [])
  have hb := finish_budget n (C.gates.foldl (transformStep n) (rs, [])) C.output
  simp only [List.length_nil, Nat.zero_add] at h
  unfold restrictCircuit
  unfold Circuit.size
  change (finish n (List.foldl (transformStep n) (rs, []) C.gates) C.output).size +
    omissions n (rs, []) C.gates ≤ C.gates.length + 1
  omega

theorem finish_budget_nontrue (n : Nat) (acc : List Ref × List Gate) (o : Nat)
    (h : acc.1.getD o (.lit false) ≠ .lit true) :
    (finish n acc o).size = acc.2.length := by
  unfold finish
  cases hr : acc.1.getD o (.lit false) with
  | wire i => rfl
  | lit b => cases b <;> simp_all [Circuit.size]

theorem restrict_budget_nontrue (C : Circuit) (rs : List Ref) (x : List Bool)
    (hv : ∀ r ∈ rs, r.valid x.length) (hg : ∀ g ∈ C.gates, Well g)
    (hf : C.eval (rs.map (fun r => r.val x)) = false) :
    (restrictCircuit x.length rs C).size + omissions x.length (rs, []) C.gates = C.size := by
  let acc := C.gates.foldl (transformStep x.length) (rs, [])
  have h : Inv rs (rs.map (fun r => r.val x)) (([] : List Gate).foldl step x) := ⟨rfl,hv⟩
  have hi := transform_sound C.gates rs [] _ x h hg
  have hne : acc.1.getD C.output (.lit false) ≠ .lit true := by
    intro he
    change (C.gates.foldl step (rs.map (fun r => r.val x))).getD C.output false = false at hf
    rw [hi.1, getD_map_ref] at hf
    change (acc.1.getD C.output (.lit false)).val _ = false at hf
    rw [he] at hf
    contradiction
  have hb := finish_budget_nontrue x.length acc C.output hne
  have hh := exact_budget x.length C.gates (rs, [])
  change (finish x.length acc C.output).size + _ = C.gates.length
  rw [hb]
  simpa [acc] using hh

-- Any effective constant operand removes its original gate (including empty/unary cases).
theorem local_constant_omits (op : GateOp) (n : Nat) (rs : List Ref)
    (hop : basis op) (hlen : rs.length ≤ 2)
    (hc : ∃ b, Ref.lit b ∈ (match op with | .not => rs.take 1 | _ => rs)) :
    (simplify op n rs).1 = none := by
  cases op with
  | and =>
    rcases rs with _ | ⟨a, rs⟩
    · simp at hc
    rcases rs with _ | ⟨b, rs⟩
    · rfl
    have hz : rs = [] := by cases rs <;> simp_all
    subst rs
    cases a <;> cases b <;> rename_i a b
    all_goals try cases a
    all_goals try cases b
    all_goals simp_all [simplify, simplifyAnd]
  | or =>
    rcases rs with _ | ⟨a, rs⟩
    · simp at hc
    rcases rs with _ | ⟨b, rs⟩
    · rfl
    have hz : rs = [] := by cases rs <;> simp_all
    subst rs
    cases a <;> cases b <;> rename_i a b
    all_goals try cases a
    all_goals try cases b
    all_goals simp_all [simplify, simplifyOr]
  | not =>
    rcases rs with _ | ⟨a, rs⟩
    · simp at hc
    cases a <;> simp_all [simplify, simplifyNot]
  | mod => contradiction
  | maj => contradiction

theorem simplify_well (op : GateOp) (n : Nat) (rs : List Ref) (g : Gate)
    (he : (simplify op n rs).1 = some g) : Well g := by
  cases op with
  | and =>
    rcases rs with _ | ⟨a, rs⟩
    · simp [simplify, simplifyAnd] at he
    rcases rs with _ | ⟨b, rs⟩
    · simp [simplify, simplifyAnd] at he
    rcases rs with _ | ⟨c, rs⟩
    · cases a <;> cases b <;> rename_i a b
      all_goals try cases a
      all_goals try cases b
      all_goals simp_all [simplify, simplifyAnd, emit, Well, basis]
      all_goals subst g <;> simp [Well, basis]
    · simp [simplify, simplifyAnd] at he
  | or =>
    rcases rs with _ | ⟨a, rs⟩
    · simp [simplify, simplifyOr] at he
    rcases rs with _ | ⟨b, rs⟩
    · simp [simplify, simplifyOr] at he
    rcases rs with _ | ⟨c, rs⟩
    · cases a <;> cases b <;> rename_i a b
      all_goals try cases a
      all_goals try cases b
      all_goals simp_all [simplify, simplifyOr, emit, Well, basis]
      all_goals subst g <;> simp [Well, basis]
    · simp [simplify, simplifyOr] at he
  | not =>
    rcases rs with _ | ⟨a, rs⟩
    · simp [simplify, simplifyNot] at he
    cases a <;> simp_all [simplify, simplifyNot, emit, Well, basis]
    subst g; simp [Well, basis]
  | mod => simp [simplify] at he
  | maj => simp [simplify] at he

theorem transform_well (n : Nat) (gs : List Gate) (acc : List Ref × List Gate)
    (h : ∀ g ∈ acc.2, Well g) : ∀ g ∈ (gs.foldl (transformStep n) acc).2, Well g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro g' hg'
    unfold transformStep at hg'
    rcases List.mem_append.mp hg' with hm | hm
    · exact h g' hm
    · apply simplify_well g.op (n + acc.2.length) _ g'
      simpa using hm

theorem restrict_well (C : Circuit) (rs : List Ref) (n : Nat) :
    ∀ g ∈ (restrictCircuit n rs C).gates, Well g := by
  let a := C.gates.foldl (transformStep n) (rs, [])
  have h : ∀ g ∈ a.2, Well g := transform_well n C.gates (rs, []) (by simp)
  intro g hg
  change g ∈ (finish n a C.output).gates at hg
  unfold finish at hg
  cases hr : a.1.getD C.output (.lit false) with
  | wire i => rw [hr] at hg; exact h g hg
  | lit b =>
    cases b
    · rw [hr] at hg; exact h g hg
    · rw [hr] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hm | rfl
      · exact h g hm
      · simp [Well, basis]

theorem readers_map (g : Gate) (f : Nat → Ref) :
    (readers g).map f = (match g.op with
      | .not => (g.inputs.map f).take 1
      | _ => g.inputs.map f) := by
  rcases g with ⟨op,ins⟩
  cases op <;> try rfl
  cases ins <;> rfl

theorem step_constant_reader_omitted (n : Nat) (acc : List Ref × List Gate) (g : Gate)
    (hg : Well g) (u : Nat) (b : Bool)
    (hr : u ∈ readers g) (hc : acc.1.getD u (.lit false) = .lit b) :
    (transformStep n acc g).2.length = acc.2.length := by
  let rs := g.inputs.map fun i => acc.1.getD i (.lit false)
  have h := local_constant_omits g.op (n + acc.2.length) rs hg.1 (by simpa [rs] using hg.2) (by
    refine ⟨b, ?_⟩
    rw [← readers_map g (fun i => acc.1.getD i (.lit false))]
    exact List.mem_map.mpr ⟨u,hr,hc⟩)
  change (acc.2 ++ (simplify g.op (n + acc.2.length) rs).1.toList).length = acc.2.length
  rw [h]; simp

-- One Boolean omission flag per original gate.
def marks (n : Nat) (acc : List Ref × List Gate) : List Gate → List Bool
  | [] => []
  | g :: gs =>
    let nxt := transformStep n acc g
    (decide (nxt.2.length = acc.2.length)) :: marks n nxt gs

theorem marks_length (n : Nat) (acc : List Ref × List Gate) (gs : List Gate) :
    (marks n acc gs).length = gs.length := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih => simp [marks, ih]

theorem marks_count (n : Nat) (acc : List Ref × List Gate) (gs : List Gate) :
    (marks n acc gs).count true = omissions n acc gs := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [marks, omissions, List.count_cons, ih]
    by_cases h : (transformStep n acc g).2.length = acc.2.length <;> simp [h] <;> omega
end PEqualNP.Research.GateElimination
