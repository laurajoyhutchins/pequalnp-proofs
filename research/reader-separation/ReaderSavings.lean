import ReaderWitness

namespace ReaderWitness

abbrev Wire (A : Type) := A → Bool

def zero : Wire A := fun _ => false
def one : Wire A := fun _ => true
def meet (f g : Wire A) : Wire A := fun x => f x && g x
def join (f g : Wire A) : Wire A := fun x => f x || g x
def neg (f : Wire A) : Wire A := fun x => ! f x

def read (ws : List (Wire A)) (i : Nat) : Wire A := ws.getD i zero

def wOperand (ws : List (Wire A)) : Operand → Wire A
  | .inl _ => zero
  | .inr i => read ws i

def wEval (ws : List (Wire A)) : Gate → Wire A
  | .const b => fun _ => b
  | .copy u => wOperand ws u
  | .bnot u => neg (wOperand ws u)
  | .band u v => meet (wOperand ws u) (wOperand ws v)
  | .bor u v => join (wOperand ws u) (wOperand ws v)

def wStep (ws : List (Wire A)) (g : Gate) := ws ++ [wEval ws g]

def Contains (ws S : List (Wire A)) : Prop := ∀ f ∈ ws, f ∈ S

def Constants (S : List (Wire A)) : Prop := zero ∈ S ∧ one ∈ S

inductive Add (S : List (Wire A)) : Wire A → Prop where
  | copy : f ∈ S → Add S f
  | band : f ∈ S → g ∈ S → Add S (meet f g)
  | bor : f ∈ S → g ∈ S → Add S (join f g)
  | bnot : f ∈ S → Add S (neg f)

inductive Trace : List (Wire A) → Nat → List (Wire A) → Prop where
  | nil (S) : Trace S 0 S
  | cons : Add S f → Trace (f::S) k T → Trace S (k+1) T

theorem readMem {ws S : List (Wire A)} (hc : Contains ws S) (hconst : Constants S) (i : Nat) : read ws i ∈ S := by
  unfold read
  rw [List.getD_eq_getElem?_getD]
  cases he : ws[i]? with
  | none => exact hconst.1
  | some f => exact hc f (List.mem_of_getElem? he)

theorem operandMem {ws S : List (Wire A)} (hc : Contains ws S) (hconst : Constants S) (u : Operand) : wOperand ws u ∈ S := by
  cases u with
  | inl => exact hconst.1
  | inr i => exact readMem hc hconst i

theorem evalAdd {ws S : List (Wire A)} (hc : Contains ws S) (hconst : Constants S) (g : Gate) : Add S (wEval ws g) := by
  cases g with
  | const b => cases b; exact .copy hconst.1; exact .copy hconst.2
  | copy u => exact .copy (operandMem hc hconst u)
  | bnot u => exact .bnot (operandMem hc hconst u)
  | band u v => exact .band (operandMem hc hconst u) (operandMem hc hconst v)
  | bor u v => exact .bor (operandMem hc hconst u) (operandMem hc hconst v)

theorem meetZero (f : Wire A) : meet zero f = zero := rfl
theorem meetZeroR (f : Wire A) : meet f zero = zero := by funext x; simp [meet,zero]
theorem joinZero (f : Wire A) : join zero f = f := rfl
theorem joinZeroR (f : Wire A) : join f zero = f := by funext x; simp [join,zero]

theorem readerFree {ws S : List (Wire A)} (hc : Contains ws S) (hconst : Constants S) (g : Gate)
    (hg : gateCode g ≠ none) : wEval ws g ∈ S := by
  cases g with
  | const => exact False.elim (hg rfl)
  | copy u => exact operandMem hc hconst u
  | bnot u =>
    cases u with
    | inl => exact hconst.2
    | inr => exact False.elim (hg rfl)
  | band u v =>
    cases u <;> cases v
    · exact hconst.1
    · exact hconst.1
    · change meet (read ws _) zero ∈ S
      rw [meetZeroR]; exact hconst.1
    · exact False.elim (hg rfl)
  | bor u v =>
    cases u <;> cases v
    · exact hconst.1
    · exact readMem hc hconst _
    · change join (read ws _) zero ∈ S
      rw [joinZeroR]; exact readMem hc hconst _
    · exact False.elim (hg rfl)

theorem stepContains {ws S : List (Wire A)} {g : Gate} (hc : Contains ws S) (hg : wEval ws g ∈ S) : Contains (wStep ws g) S := by
  intro f hf
  simp only [wStep,List.mem_append,List.mem_singleton] at hf
  rcases hf with h | h
  · exact hc f h
  · rw [h]; exact hg

theorem stepContainsNew {ws S : List (Wire A)} {g : Gate} (hc : Contains ws S) : Contains (wStep ws g) (wEval ws g :: S) :=
  stepContains (fun f hf => List.mem_cons_of_mem _ (hc f hf)) (by simp)

theorem countLe (gs : List Gate) : (columns gs).length ≤ gs.length := by
  exact List.length_filterMap_le _ _

theorem saveAllReaders (gs : List Gate) {ws S : List (Wire A)} (hc : Contains ws S) (hconst : Constants S) :
    ∃ T, Trace S (gs.length - (columns gs).length) T ∧ Contains (gs.foldl wStep ws) T := by
  induction gs generalizing ws S with
  | nil => exact ⟨S,.nil S,hc⟩
  | cons g gs ih =>
    have hle := countLe gs
    cases he : gateCode g with
    | none =>
      have hnew : Constants (wEval ws g :: S) := ⟨List.mem_cons_of_mem _ hconst.1,List.mem_cons_of_mem _ hconst.2⟩
      obtain ⟨T,ht,hcover⟩ := ih (stepContainsNew hc (g:=g)) hnew
      have hcount : (g::gs).length - (columns (g::gs)).length = (gs.length - (columns gs).length)+1 := by
        simp [columns,he] at *
        omega
      exact ⟨T,hcount ▸ Trace.cons (evalAdd hc hconst g) ht,hcover⟩
    | some c =>
      have hmem := readerFree hc hconst g (by simp [he])
      obtain ⟨T,ht,hcover⟩ := ih (stepContains hc hmem) hconst
      have hcount : (g::gs).length - (columns (g::gs)).length = gs.length - (columns gs).length := by
        simp [columns,he]
      exact ⟨T,hcount ▸ ht,hcover⟩

theorem readMap (ws : List (Wire A)) (i : Nat) (x : A) :
    (ws.map (fun f => f x)).getD i false = read ws i x := by
  simp only [read,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem operandMap (ws : List (Wire A)) (u : Operand) (x : A) :
    wOperand ws u x = operand 0 (ws.map (fun f => f x)) u := by
  cases u with
  | inl => simp [wOperand,zero,operand]
  | inr i => exact (readMap ws i x).symm

theorem evalMap (ws : List (Wire A)) (g : Gate) (x : A) :
    wEval ws g x = gateEval g 0 (ws.map (fun f => f x)) := by
  cases g <;> simp [wEval,gateEval,meet,join,neg,operandMap]

theorem runMap (gs : List Gate) (ws : List (Wire A)) (x : A) :
    (gs.foldl wStep ws).map (fun f => f x) = run gs 0 (ws.map (fun f => f x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,run] at *
    rw [ih]
    simp [wStep,evalMap]

theorem readRestricted (gs : List Gate) (ws : List (Wire A)) (out : Nat) (x : A) :
    read (gs.foldl wStep ws) out x = (run gs 0 (ws.map (fun f => f x))).getD out false := by
  rw [← runMap,readMap]

theorem sixGateSavings (gs : List Gate) (cs : List Column) (out : Nat)
    (hfixed : columns gs = fixed :: cs)
    (hw : ∀ r ∈ witnesses, ∃ pool : List Bool,
      (run gs r.1 pool).getD out false ≠ (run gs r.2.1 pool).getD out false)
    {ws S : List (Wire A)} (hc : Contains ws S) (hconst : Constants S) :
    ∃ k T, k + 6 ≤ gs.length ∧ Trace S k T ∧
      (fun x => (run gs 0 (ws.map (fun f => f x))).getD out false) ∈ T := by
  have h6 := readerCertificate gs cs out hfixed hw
  have hle := countLe gs
  obtain ⟨T,ht,hcover⟩ := saveAllReaders gs hc hconst
  have hcT : Constants T := by
    -- Constants are available in the initial pool; Trace never removes a wire.
    have persist {U V : List (Wire A)} {k : Nat} (h : Trace U k V) :
        ∀ f ∈ U, f ∈ V := by
      induction h with
      | nil => exact fun f hf => hf
      | cons _ _ ih => exact fun f hf => ih f (List.mem_cons_of_mem _ hf)
    exact ⟨persist ht _ hconst.1,persist ht _ hconst.2⟩
  have hm := readMem hcover hcT out
  have he : read (gs.foldl wStep ws) out = (fun x => (run gs 0 (ws.map (fun f => f x))).getD out false) := by
    funext x; exact readRestricted gs ws out x
  rw [he] at hm
  exact ⟨_,T,by omega,ht,hm⟩

#print axioms saveAllReaders
#print axioms sixGateSavings
end ReaderWitness
