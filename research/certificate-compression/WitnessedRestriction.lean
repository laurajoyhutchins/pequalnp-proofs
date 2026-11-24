import Lean

namespace CircuitCompression

abbrev Wire (α : Type) := α → Bool

def zero : Wire α := fun _ => false
def one : Wire α := fun _ => true
def meet (f g : Wire α) : Wire α := fun x => f x && g x
def join (f g : Wire α) : Wire α := fun x => f x || g x
def neg (f : Wire α) : Wire α := fun x => !f x
def project (r : β → α) (f : Wire α) : Wire β := fun x => f (r x)

inductive Gate (S : List (Wire α)) : Wire α → Prop where
  | copy : f ∈ S → Gate S f
  | and : f ∈ S → g ∈ S → Gate S (meet f g)
  | or : f ∈ S → g ∈ S → Gate S (join f g)
  | not : f ∈ S → Gate S (neg f)

inductive Run : List (Wire α) → Nat → List (Wire α) → Prop where
  | nil (S) : Run S 0 S
  | cons : Gate S f → Run (f :: S) k T → Run S (k+1) T

def Covers (r : β → α) (S : List (Wire α)) (U : List (Wire β)) : Prop :=
  ∀ f ∈ S, project r f ∈ U

def Constants (S : List (Wire α)) : Prop := zero ∈ S ∧ one ∈ S

theorem coverCons {r : β → α} {S : List (Wire α)} {U : List (Wire β)} {f : Wire α}
    (h : Covers r S U) (hf : project r f ∈ U) : Covers r (f :: S) U := by
  intro g hg
  rcases List.mem_cons.mp hg with e | e
  · subst g; exact hf
  · exact h g e

theorem coverGrow {r : β → α} {S : List (Wire α)} {U : List (Wire β)} {v : Wire β}
    (h : Covers r S U) : Covers r S (v :: U) :=
  fun f hf => List.mem_cons_of_mem v (h f hf)

theorem constantsGrow {S : List (Wire α)} {v : Wire α} (h : Constants S) : Constants (v :: S) :=
  ⟨List.mem_cons_of_mem v h.1, List.mem_cons_of_mem v h.2⟩

theorem gateProject {r : β → α} {S : List (Wire α)} {U : List (Wire β)}
    {f : Wire α} (h : Gate S f) (hc : Covers r S U) : Gate U (project r f) := by
  cases h with
  | copy hf => exact .copy (hc _ hf)
  | and hf hg => exact .and (hc _ hf) (hc _ hg)
  | or hf hg => exact .or (hc _ hf) (hc _ hg)
  | not hf => exact .not (hc _ hf)

theorem runProject {r : β → α} {S T : List (Wire α)} {k : Nat}
    (h : Run S k T) {U : List (Wire β)} (hc : Covers r S U) :
    ∃ V, Run U k V ∧ Covers r T V := by
  induction h generalizing U with
  | nil S => exact ⟨U, .nil U, hc⟩
  | @cons S f k T hg hr ih =>
    have hc' : Covers r (f :: S) (project r f :: U) :=
      coverCons (coverGrow hc) (by simp)
    obtain ⟨V, hv, hcv⟩ := ih hc'
    exact ⟨V, .cons (gateProject hg hc) hv, hcv⟩

-- An unstable input must project to a free constant. Stable inputs may be arbitrary.
def Collapses (r : β → α) (a b : α) (S : List (Wire α)) : Prop :=
  ∀ f ∈ S, f a ≠ f b → project r f = zero ∨ project r f = one

theorem redundantGate {r : β → α} {a b : α} {S : List (Wire α)} {U : List (Wire β)}
    {v : Wire α} (hg : Gate S v) (hd : v a ≠ v b) (hc : Covers r S U)
    (hconst : Constants U) (hcol : Collapses r a b S) : project r v ∈ U := by
  cases hg with
  | copy hf => exact hc _ hf
  | @not f hf =>
    have hn : f a ≠ f b := by
      intro he; apply hd; simp [neg, he]
    have h : project r (neg f) = neg (project r f) := rfl
    rw [h]
    rcases hcol f hf hn with h0 | h1
    · rw [h0, show neg (zero : Wire β) = one by rfl]; exact hconst.2
    · rw [h1, show neg (one : Wire β) = zero by rfl]; exact hconst.1
  | @and f g hf hg =>
    have h : project r (meet f g) = meet (project r f) (project r g) := rfl
    rw [h]
    by_cases he : f a = f b
    · have hn : g a ≠ g b := by intro he'; apply hd; simp [meet, he, he']
      rcases hcol g hg hn with h0 | h1
      · rw [h0]; first | exact (show meet (project r f) zero ∈ U from by rw [show meet (project r f) zero = zero by funext x; simp [meet, zero]]; exact hconst.1) | exact (show meet zero (project r g) ∈ U from by rw [show meet zero (project r g) = zero by funext x; simp [meet, zero]]; exact hconst.1)
      · rw [h1, show meet (project r f) one = project r f by funext x; simp [meet, one]]; exact hc f hf
    · rcases hcol f hf he with h0 | h1
      · rw [h0]; first | exact (show meet (project r f) zero ∈ U from by rw [show meet (project r f) zero = zero by funext x; simp [meet, zero]]; exact hconst.1) | exact (show meet zero (project r g) ∈ U from by rw [show meet zero (project r g) = zero by funext x; simp [meet, zero]]; exact hconst.1)
      · rw [h1, show meet one (project r g) = project r g by funext x; simp [meet, one]]; exact hc g hg
  | @or f g hf hg =>
    have h : project r (join f g) = join (project r f) (project r g) := rfl
    rw [h]
    by_cases he : f a = f b
    · have hn : g a ≠ g b := by intro he'; apply hd; simp [join, he, he']
      rcases hcol g hg hn with h0 | h1
      · rw [h0, show join (project r f) zero = project r f by funext x; simp [join, zero]]; exact hc f hf
      · rw [h1]; first | exact (show join (project r f) one ∈ U from by rw [show join (project r f) one = one by funext x; simp [join, one]]; exact hconst.2) | exact (show join one (project r g) ∈ U from by rw [show join one (project r g) = one by funext x; simp [join, one]]; exact hconst.2)
    · rcases hcol f hf he with h0 | h1
      · rw [h0, show join zero (project r g) = project r g by funext x; simp [join, zero]]; exact hc g hg
      · rw [h1]; first | exact (show join (project r f) one ∈ U from by rw [show join (project r f) one = one by funext x; simp [join, one]]; exact hconst.2) | exact (show join one (project r g) ∈ U from by rw [show join one (project r g) = one by funext x; simp [join, one]]; exact hconst.2)

-- Restrict and save at least one gate, while preserving the entire terminal pool.
theorem saveGate {r : β → α} {a b : α} {S T : List (Wire α)} {k : Nat}
    {target : Wire α} (run : Run S k T) (ht : target ∈ T) (hn : target ∉ S)
    (hd : target a ≠ target b) {U : List (Wire β)} (hc : Covers r S U)
    (hconst : Constants U) (hcol : Collapses r a b S) :
    ∃ m V, m < k ∧ Run U m V ∧ Covers r T V := by
  induction run generalizing U with
  | nil S => exact False.elim (hn ht)
  | @cons S f k T hg hr ih =>
    by_cases hf : f a ≠ f b
    · have hm := redundantGate hg hf hc hconst hcol
      obtain ⟨V, hv, hcv⟩ := runProject hr (coverCons hc hm)
      exact ⟨k, V, by omega, hv, hcv⟩
    · have hn' : target ∉ f :: S := by
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · subst f; exact hf hd
        · exact hn h
      have hcol' : Collapses r a b (f :: S) := by
        intro g hm hdiff
        rcases List.mem_cons.mp hm with h | h
        · subst g; exact False.elim (hf hdiff)
        · exact hcol g h hdiff
      have hc' : Covers r (f :: S) (project r f :: U) := coverCons (coverGrow hc) (by simp)
      obtain ⟨m, V, hm, hv, hcv⟩ := ih ht hn' hc' (constantsGrow hconst) hcol'
      exact ⟨m+1, V, by omega, .cons (gateProject hg hc) hv, hcv⟩


end CircuitCompression
