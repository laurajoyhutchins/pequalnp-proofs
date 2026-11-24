import RestrictedTriangle
import EvaluatorMirror
namespace CircuitCompression
open PEqualNP.CircuitLowerBounds (GateOp Circuit)
abbrev CGate := PEqualNP.CircuitLowerBounds.Gate
def Good (g : CGate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def read (ws : List (Wire α)) (i : Nat) : Wire α := ws.getD i zero
def evalGate (ws : List (Wire α)) (g : CGate) : Wire α := fun x => g.op.eval (g.inputs.map fun i => read ws i x)
def step (ws : List (Wire α)) (g : CGate) := ws ++ [evalGate ws g]
def scalarStep (ws : List Bool) (g : CGate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

theorem readMem {ws S : List (Wire α)} (h : ∀ f ∈ ws, f ∈ S) (hc : Constants S) (i : Nat) : read ws i ∈ S := by
  unfold read
  rw [List.getD_eq_getElem?_getD]
  cases he : ws[i]? with
  | none => exact hc.1
  | some f => exact h f (List.mem_of_getElem? he)

theorem evalGateGen {ws S : List (Wire α)} {g : CGate} (hg : Good g)
    (h : ∀ f ∈ ws, f ∈ S) (hc : Constants S) : Gate S (evalGate ws g) := by
  rcases g with ⟨op,ins⟩
  rcases hg with ⟨hop,hlen⟩
  simp only at hop hlen
  cases ins with
  | nil =>
    rcases hop with h' | h' | h' <;> subst op
    · exact .copy hc.2
    · exact .copy hc.1
    · exact .copy hc.2
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with h' | h' | h' <;> subst op
      · have e : evalGate ws ⟨.and,[i]⟩ = read ws i := by funext x; simp [evalGate,GateOp.eval]
        rw [e]; exact .copy (readMem h hc i)
      · have e : evalGate ws ⟨.or,[i]⟩ = read ws i := by funext x; simp [evalGate,GateOp.eval]
        rw [e]; exact .copy (readMem h hc i)
      · exact .not (readMem h hc i)
    | cons j tail =>
      cases tail with
      | nil =>
        rcases hop with h' | h' | h' <;> subst op
        · have e : evalGate ws ⟨.and,[i,j]⟩ = meet (read ws i) (read ws j) := by funext x; simp [evalGate,GateOp.eval,meet]
          rw [e]; exact .and (readMem h hc i) (readMem h hc j)
        · have e : evalGate ws ⟨.or,[i,j]⟩ = join (read ws i) (read ws j) := by funext x; simp [evalGate,GateOp.eval,join]
          rw [e]; exact .or (readMem h hc i) (readMem h hc j)
        · exact .not (readMem h hc i)
      | cons k tail => simp at hlen

theorem runOf (gs : List CGate) (hg : ∀ g ∈ gs, Good g) {ws S : List (Wire α)}
    (h : ∀ f ∈ ws, f ∈ S) (hc : Constants S) :
    ∃ T, Run S gs.length T ∧ (∀ f ∈ gs.foldl step ws, f ∈ T) ∧ Constants T := by
  induction gs generalizing ws S with
  | nil => exact ⟨S,.nil S,h,hc⟩
  | cons g gs ih =>
    have hgate := evalGateGen (hg g (by simp)) h hc
    have h' : ∀ f ∈ step ws g, f ∈ evalGate ws g :: S := by
      intro f hf
      simp only [step,List.mem_append,List.mem_singleton] at hf
      rcases hf with hf | hf
      · exact List.mem_cons_of_mem _ (h f hf)
      · subst f; simp
    obtain ⟨T,hr,ht,hc'⟩ := ih (fun g hm => hg g (by simp [hm])) h' (constantsGrow hc)
    exact ⟨T,.cons hgate hr,ht,hc'⟩

theorem readMap (ws : List (Wire α)) (i : Nat) (x : α) : (ws.map (fun f => f x)).getD i false = read ws i x := by
  simp only [read,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem stepMap (ws : List (Wire α)) (g : CGate) (x : α) : (step ws g).map (fun f => f x) = scalarStep (ws.map (fun f => f x)) g := by
  simp only [step,evalGate,scalarStep,List.map_append,List.map_cons,List.map_nil]
  congr 2
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i _
  exact (readMap ws i x).symm

theorem runMap (gs : List CGate) (ws : List (Wire α)) (x : α) :
    (gs.foldl step ws).map (fun f => f x) = gs.foldl scalarStep (ws.map (fun f => f x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons,ih,stepMap]

theorem upstreamEval (C : Circuit) (x : Fin n → Bool) : C.eval (List.ofFn x) = read (C.gates.foldl step (List.ofFn input)) C.output x := by
  unfold Circuit.eval Circuit.wires
  rw [← readMap,runMap,List.map_ofFn]
  rfl

theorem circuitLower (C : Circuit) (hg : ∀ g ∈ C.gates, Good g) (ht : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeTriangle x) : 6 ≤ C.size := by
  have h : ∀ f ∈ List.ofFn (input (n:=5)), f ∈ initial 5 := by intro f hf; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)
  obtain ⟨T,hr,ht',hc⟩ := runOf C.gates hg h (initialConstants 5)
  have he : read (C.gates.foldl step (List.ofFn (input (n:=5)))) C.output = edgeTriangle := by
    funext x; rw [← upstreamEval]; exact ht x
  have hm := readMem ht' hc C.output
  rw [he] at hm
  exact edgeTriangleLower hr hm

def edgeWitness : Circuit := ⟨[⟨.or,[3,4]⟩,⟨.and,[2,5]⟩,⟨.and,[3,4]⟩,⟨.or,[6,7]⟩,⟨.and,[0,1]⟩,⟨.or,[8,9]⟩],10⟩

theorem witnessGood : ∀ g ∈ edgeWitness.gates, Good g := by
  intro g hg
  simp [edgeWitness] at hg
  rcases hg with h|h|h|h|h|h <;> subst g <;> simp [Good]

theorem witnessEval (x : Fin 5 → Bool) : edgeWitness.eval (List.ofFn x) = edgeTriangle x := by
  simp [edgeWitness,Circuit.eval,Circuit.wires,GateOp.eval,List.ofFn_succ,edgeTriangle]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;> cases h4 : x 4 <;> simp_all

end CircuitCompression
open CircuitCompression

theorem exactSize764 : ∀ s : Nat, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  constructor
  · rintro ⟨C,hg,hs,ht⟩
    have hgood : ∀ g ∈ C.gates, Good g := by
      intro g hm
      obtain ⟨hop,hlen⟩ := hg g hm
      exact ⟨by simpa using hop,hlen⟩
    exact Nat.le_trans (circuitLower C hgood ht) hs
  · intro hs
    refine ⟨edgeWitness,?_,hs,witnessEval⟩
    intro g hm
    obtain ⟨hop,hlen⟩ := witnessGood g hm
    exact ⟨by simpa using hop,hlen⟩
