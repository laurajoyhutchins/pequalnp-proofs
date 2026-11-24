import WitnessedRestriction

namespace CircuitCompression

-- Executable finite certificate. No classical decision of function equality is needed.
def decode (m : BitVec w) : Wire (Fin w) := fun i => m.getLsbD i.val

theorem decodeInjective {m n : BitVec w} (h : decode m = decode n) : m = n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun h ⟨i, hi⟩

theorem decodeAnd (m n : BitVec w) : decode (m &&& n) = meet (decode m) (decode n) := by
  funext i; simp [decode, meet]

theorem decodeOr (m n : BitVec w) : decode (m ||| n) = join (decode m) (decode n) := by
  funext i; simp [decode, join]

theorem decodeNot (m : BitVec w) : decode (~~~m) = neg (decode m) := by
  funext i; simp [decode, neg, i.isLt]

def nextMasks (s : List (BitVec w)) : List (BitVec w) :=
  (s ++ s.map (fun a => ~~~a) ++ s.flatMap (fun a => s.flatMap (fun b => [a &&& b, a ||| b]))).eraseDups

def search (s : List (BitVec w)) (t : BitVec w) : Nat → Bool
  | 0 => s.contains t
  | 1 => (nextMasks s).contains t
  | k+2 => s.contains t || (nextMasks s).any (fun a => search (a::s) t (k+1))

def MaskCovers (r : Fin w → α) (S : List (Wire α)) (s : List (BitVec w)) : Prop :=
  ∀ f ∈ S, ∃ m ∈ s, decode m = project r f

theorem nextCopy {s : List (BitVec w)} {a : BitVec w} (h : a ∈ s) : a ∈ nextMasks s := by
  simp only [nextMasks, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inl h)

theorem nextNot {s : List (BitVec w)} {a : BitVec w} (h : a ∈ s) : ~~~a ∈ nextMasks s := by
  simp only [nextMasks, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨a,h,rfl⟩))

theorem nextAnd {s : List (BitVec w)} {a b : BitVec w} (ha : a ∈ s) (hb : b ∈ s) : a &&& b ∈ nextMasks s := by
  simp only [nextMasks, List.mem_eraseDups, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,by simp⟩⟩)

theorem nextOr {s : List (BitVec w)} {a b : BitVec w} (ha : a ∈ s) (hb : b ∈ s) : a ||| b ∈ nextMasks s := by
  simp only [nextMasks, List.mem_eraseDups, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,by simp⟩⟩)

theorem maskGate {r : Fin w → α} {S : List (Wire α)} {s : List (BitVec w)} {f : Wire α}
    (hg : Gate S f) (hc : MaskCovers r S s) : ∃ m ∈ nextMasks s, decode m = project r f := by
  cases hg with
  | copy hf =>
    obtain ⟨a,ha,he⟩ := hc _ hf
    exact ⟨a,nextCopy ha,he⟩
  | not hf =>
    obtain ⟨a,ha,he⟩ := hc _ hf
    exact ⟨~~~a,nextNot ha,by rw [decodeNot,he]; rfl⟩
  | and hf hg =>
    obtain ⟨a,ha,he⟩ := hc _ hf
    obtain ⟨b,hb,he'⟩ := hc _ hg
    exact ⟨a &&& b,nextAnd ha hb,by rw [decodeAnd,he,he']; rfl⟩
  | or hf hg =>
    obtain ⟨a,ha,he⟩ := hc _ hf
    obtain ⟨b,hb,he'⟩ := hc _ hg
    exact ⟨a ||| b,nextOr ha hb,by rw [decodeOr,he,he']; rfl⟩

theorem searchSound {r : Fin w → α} {S T : List (Wire α)} {k : Nat} {f : Wire α}
    (hr : Run S k T) (hf : f ∈ T) {t : BitVec w} (he : decode t = project r f)
    {s : List (BitVec w)} (hc : MaskCovers r S s) (fuel : Nat) (hk : k ≤ fuel) :
    search s t fuel = true := by
  induction hr generalizing s fuel with
  | nil S =>
    obtain ⟨a,ha,ha'⟩ := hc f hf
    have eq : a = t := decodeInjective (ha'.trans he.symm)
    subst a
    have hm := List.contains_iff_mem.mpr ha
    cases fuel with
    | zero => exact hm
    | succ fuel =>
      cases fuel with
      | zero => exact List.contains_iff_mem.mpr (nextCopy ha)
      | succ fuel => simp [search,ha]
  | @cons S g k T hg hr ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨a,ha,ha'⟩ := maskGate hg hc
      have hc' : MaskCovers r (g::S) (a::s) := by
        intro v hv
        rcases List.mem_cons.mp hv with h | h
        · subst v; exact ⟨a,by simp,ha'⟩
        · obtain ⟨b,hb,heq⟩ := hc v h
          exact ⟨b,List.mem_cons_of_mem a hb,heq⟩
      cases fuel with
      | zero =>
        have hrec := ih hf hc' 0 (by omega)
        have hm : t ∈ a::s := List.contains_iff_mem.mp hrec
        rcases List.mem_cons.mp hm with h | h
        · subst t; exact List.contains_iff_mem.mpr ha
        · exact List.contains_iff_mem.mpr (nextCopy h)
      | succ fuel =>
        have hrec := ih hf hc' (fuel+1) (by omega)
        have hex : (nextMasks s).any (fun a => search (a::s) t (fuel+1)) = true :=
          List.any_eq_true.mpr ⟨a,ha,hrec⟩
        simp [search,hex]

-- Concrete triangle certificate: rows 1,2,4,3,5,6 (singletons then pairs).
def input (i : Fin n) : Wire (Fin n → Bool) := fun x => x i
def initial (n : Nat) : List (Wire (Fin n → Bool)) := zero :: one :: List.ofFn input

theorem initialConstants (n : Nat) : Constants (initial n) := by simp [Constants,initial]

def triangle : Wire (Fin 3 → Bool) := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)
def sample (i : Fin 6) : Fin 3 → Bool := fun j => ([1,2,4,3,5,6] : List Nat).getD i.val 0 |>.testBit j.val

def triangleMasks : List (BitVec 6) := [0,63,25,42,52]

theorem triangleMaskCover : MaskCovers sample (initial 3) triangleMasks := by
  intro f hf
  simp only [initial,List.mem_cons,List.mem_ofFn] at hf
  rcases hf with h | h | ⟨i,h⟩
  · subst f; exact ⟨0,by decide,by funext j; simp [decode,project,zero]⟩
  · subst f; refine ⟨63,by decide,?_⟩; funext j
    exact (show ∀ j : Fin 6, decode (63 : BitVec 6) j = project sample one j by decide) j
  · subst f
    have hfinite : ∀ i : Fin 3, ∃ m : BitVec 6, m ∈ triangleMasks ∧ ∀ j : Fin 6, decode m j = project sample (input i) j := by decide
    obtain ⟨m,hm,he⟩ := hfinite i
    exact ⟨m,hm,funext he⟩

theorem triangleTargetMask : decode (56 : BitVec 6) = project sample triangle := by
  funext j
  exact (show ∀ j : Fin 6, decode (56 : BitVec 6) j = project sample triangle j by decide) j

theorem triangleFirstMasks : nextMasks triangleMasks = [0,63,25,42,52,38,21,11,8,59,16,61,32,62] := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch0 : search ((0 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch63 : search ((63 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch25 : search ((25 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch42 : search ((42 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch52 : search ((52 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch38 : search ((38 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch21 : search ((21 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch11 : search ((11 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch8 : search ((8 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch59 : search ((59 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch16 : search ((16 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch61 : search ((61 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch32 : search ((32 : BitVec 6) :: triangleMasks) 56 2 = false := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem triangleBranch62 : search ((62 : BitVec 6) :: triangleMasks) 56 2 = false := by decide


theorem triangleCertificate : search triangleMasks 56 3 = false := by
  have h : triangleMasks.contains 56 = false := by decide
  rw [search]
  simp only [Nat.reduceAdd, h, Bool.false_or, triangleFirstMasks, List.any_cons, List.any_nil, triangleBranch0, triangleBranch63, triangleBranch25, triangleBranch42, triangleBranch52, triangleBranch38, triangleBranch21, triangleBranch11, triangleBranch8, triangleBranch59, triangleBranch16, triangleBranch61, triangleBranch32, triangleBranch62]

theorem triangleLower {T : List (Wire (Fin 3 → Bool))} {k : Nat}
    (hr : Run (initial 3) k T) (ht : triangle ∈ T) : 4 ≤ k := by
  by_cases h : 4 ≤ k
  · exact h
  · have hs := searchSound hr ht triangleTargetMask triangleMaskCover 3 (by omega)
    rw [triangleCertificate] at hs
    contradiction


end CircuitCompression
