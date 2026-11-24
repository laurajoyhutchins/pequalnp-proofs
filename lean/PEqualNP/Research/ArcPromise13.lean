import Mathlib

namespace PEqualNP.Research.ArcPromise13

abbrev I (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def line (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => I p l)

def miss (X : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => ∀ p ∈ X, ¬ I p l)

def zero (Y : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => ∀ l ∈ Y, ¬ I p l)

abbrev Arc (X : Finset (Fin 13)) : Prop :=
  ∀ l : Fin 13, (X.filter (fun p => I p l)).card ≤ 2

abbrev DualArc (Y : Finset (Fin 13)) : Prop :=
  ∀ p : Fin 13, (Y.filter (fun l => I p l)).card ≤ 2

abbrev Generic (Z : Finset (Fin 13)) : Prop :=
  (∀ p ∉ Z, ∃ l : Fin 13, (∀ q ∈ Z, ¬ I q l) ∧ I p l) ∧
  (¬ ∃ l : Fin 13, ∀ p ∈ Z, I p l) ∧
  (¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ Z, ¬ I q l) → I p l)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pointArc : ∀ X : Finset (Fin 13), Arc X → 3 ≤ X.card → Generic X := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lineArc : ∀ Y : Finset (Fin 13), DualArc Y → 3 ≤ Y.card → Generic (zero Y) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallPool : ∀ Y : Finset (Fin 13), Y.card ≤ 2 → 6 ≤ (zero Y).card := by
  decide

theorem lineCard : ∀ l : Fin 13, (line l).card = 4 := by decide

theorem pairLine : ∀ p q : Fin 13, p ≠ q → ∃ l : Fin 13, I p l ∧ I q l := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem triangleArc : ∀ p q r l : Fin 13,
    p ≠ q → I p l → I q l → ¬ I r l → Arc ({r, p, q} : Finset (Fin 13)) := by
  decide

theorem extend (X Y : Finset (Fin 13))
    (hind : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) (hX : Arc X) (hY : DualArc Y) :
    ∃ Z : Finset (Fin 13),
      X ⊆ Z ∧ (∀ l ∈ Y, ∀ p ∈ Z, ¬ I p l) ∧ Generic Z := by
  by_cases hlarge : 3 ≤ X.card
  · exact ⟨X, fun _ h => h, fun l hl p hp => hind p hp l hl, pointArc X hX hlarge⟩
  have hsub : X ⊆ zero Y := by
    intro p hp
    simp only [zero, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hind p hp
  have hmiss : ∀ l ∈ Y, ∀ p ∈ zero Y, ¬ I p l := by
    intro l hl p hp
    simp only [zero, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp l hl
  by_cases hylarge : 3 ≤ Y.card
  · exact ⟨zero Y, hsub, hmiss, lineArc Y hY hylarge⟩
  have hpool := smallPool Y (by omega)
  obtain ⟨T, hXT, hTP, hTc⟩ :=
    Finset.exists_subsuperset_card_eq hsub (show X.card ≤ 2 by omega)
      (show 2 ≤ (zero Y).card by omega)
  obtain ⟨p, q, hpq, hT⟩ := Finset.card_eq_two.mp hTc
  obtain ⟨l, hpl, hql⟩ := pairLine p q hpq
  obtain ⟨r, hrP, hrL⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (line l).card < (zero Y).card by rw [lineCard]; omega)
  have hr : ¬ I r l := by simpa [line] using hrL
  have hrT : r ∉ T := by
    rw [hT]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => hr (e.symm ▸ hpl), fun e => hr (e.symm ▸ hql)⟩
  have hc : (insert r T).card = 3 := by
    rw [Finset.card_insert_of_notMem hrT, hTc]
  have ha : Arc (insert r T) := by
    rw [hT]
    exact triangleArc p q r l hpq hpl hql hr
  have hzP : insert r T ⊆ zero Y := Finset.insert_subset_iff.mpr ⟨hrP, hTP⟩
  exact ⟨insert r T, hXT.trans (Finset.subset_insert _ _),
    fun l hl p hp => hmiss l hl p (hzP hp), pointArc _ ha (by omega)⟩

end PEqualNP.Research.ArcPromise13
