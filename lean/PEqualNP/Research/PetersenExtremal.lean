import Mathlib

namespace PEqualNP.Research.PetersenExtremal

abbrev sub (a b : Fin 1024) : Prop := ∀ i : Fin 10, a.val.testBit i.val = true → b.val.testBit i.val = true
def f (a : Fin 1024) : Bool := (a.val.testBit 0 && a.val.testBit 1) || (a.val.testBit 1 && a.val.testBit 2) ||
    (a.val.testBit 2 && a.val.testBit 3) || (a.val.testBit 3 && a.val.testBit 4) ||
    (a.val.testBit 4 && a.val.testBit 0) || (a.val.testBit 0 && a.val.testBit 5) ||
    (a.val.testBit 1 && a.val.testBit 6) || (a.val.testBit 2 && a.val.testBit 7) ||
    (a.val.testBit 3 && a.val.testBit 8) || (a.val.testBit 4 && a.val.testBit 9) ||
    (a.val.testBit 5 && a.val.testBit 7) || (a.val.testBit 7 && a.val.testBit 9) ||
    (a.val.testBit 9 && a.val.testBit 6) || (a.val.testBit 6 && a.val.testBit 8) ||
    (a.val.testBit 8 && a.val.testBit 5)
def p (i : Fin 15) : Fin 1024 := ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] : List (Fin 1024)).getD i.val 0
def q (i : Fin 15) : Fin 1024 := ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List (Fin 1024)).getD i.val 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma coverage : ∀ a : Fin 1024,
    (f a = true → ∃ i : Fin 15, sub (p i) a) ∧
    (f a = false → ∃ i : Fin 15, sub a (q i)) := by
  decide

end PEqualNP.Research.PetersenExtremal

theorem PEqualNP.Research.PetersenExtremal : let sub := fun (a b : Fin 1024) => ∀ i : Fin 10, a.val.testBit i.val = true → b.val.testBit i.val = true
  let f := fun (a : Fin 1024) => (a.val.testBit 0 && a.val.testBit 1) || (a.val.testBit 1 && a.val.testBit 2) ||
    (a.val.testBit 2 && a.val.testBit 3) || (a.val.testBit 3 && a.val.testBit 4) ||
    (a.val.testBit 4 && a.val.testBit 0) || (a.val.testBit 0 && a.val.testBit 5) ||
    (a.val.testBit 1 && a.val.testBit 6) || (a.val.testBit 2 && a.val.testBit 7) ||
    (a.val.testBit 3 && a.val.testBit 8) || (a.val.testBit 4 && a.val.testBit 9) ||
    (a.val.testBit 5 && a.val.testBit 7) || (a.val.testBit 7 && a.val.testBit 9) ||
    (a.val.testBit 9 && a.val.testBit 6) || (a.val.testBit 6 && a.val.testBit 8) ||
    (a.val.testBit 8 && a.val.testBit 5)
  let p := fun i : Fin 15 => ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] : List (Fin 1024)).getD i.val 0
  let q := fun i : Fin 15 => ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List (Fin 1024)).getD i.val 0
  ∀ g : Fin 1024 → Bool,
    (∀ a b, sub a b → g a = true → g b = true) →
    (∀ i, g (p i) = true) →
    (∀ i, g (q i) = false) →
    ∀ a, g a = f a := by
  dsimp only
  intro g hm hp hq a
  change (∀ a b, PEqualNP.Research.PetersenExtremal.sub a b →
    g a = true → g b = true) at hm
  change (∀ i, g (PEqualNP.Research.PetersenExtremal.p i) = true) at hp
  change (∀ i, g (PEqualNP.Research.PetersenExtremal.q i) = false) at hq
  change g a = PEqualNP.Research.PetersenExtremal.f a
  cases h : PEqualNP.Research.PetersenExtremal.f a with
  | false =>
      obtain ⟨i, hi⟩ := (PEqualNP.Research.PetersenExtremal.coverage a).2 h
      cases hg : g a with
      | false => rfl
      | true =>
          have ht := hm a (PEqualNP.Research.PetersenExtremal.q i) hi hg
          rw [hq i] at ht
          contradiction
  | true =>
      obtain ⟨i, hi⟩ := (PEqualNP.Research.PetersenExtremal.coverage a).1 h
      exact hm (PEqualNP.Research.PetersenExtremal.p i) a hi (hp i)
