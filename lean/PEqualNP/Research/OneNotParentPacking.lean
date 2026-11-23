import Mathlib

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Research.OneNotParentPacking : ∀ (n m s : ℕ) (S : Fin m → Finset (Fin n))
  (W : ℕ → Finset (Fin n) → Prop) (o a b : Fin m → ℕ) (k : Fin m → Bool),
  (∀ i, 2 ≤ (S i).card) →
  (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) →
  (∀ v : Fin n, ∀ x, W v.val x ↔ v ∈ x) →
  (∀ i, n ≤ o i ∧ o i < n + s) →
  (∀ i, a i < o i ∧ b i < o i) →
  (∀ i x, W (o i) x ↔ ∃ v ∈ S i, v ∈ x) →
  (∀ i w, w < o i → ¬ (∀ x, W w x ↔ ∃ v ∈ S i, v ∈ x)) →
  (∀ i, k i = true → ∀ x, W (o i) x ↔ W (a i) x ∧ W (b i) x) →
  (∀ i, k i = false → ∀ x, W (o i) x ↔ W (a i) x ∨ W (b i) x) →
  m + (Finset.univ.filter (fun i : Fin m => 3 ≤ (S i).card)).card ≤ s := by
  classical
  intro n m s S W o a b k hsize hlin hinput hob hparents hout hearly hand hor
  let F : Fin m → Finset (Fin n) → Prop := fun i x => ∃ v ∈ S i, v ∈ x
  let P : ℕ → Finset (Fin n) := fun w => Finset.univ.filter (fun v => W w {v})
  have hF (i : Fin m) (v : Fin n) : F i {v} ↔ v ∈ S i := by
    simp [F]
  have hW (i : Fin m) (x : Finset (Fin n)) : W (o i) x ↔ F i x :=
    hout i x
  have hcontain (i j : Fin m) (h : ∀ x, F i x → F j x) : i = j := by
    by_contra hij
    have hsub : S i ⊆ S i ∩ S j := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨hv, (hF j v).mp (h {v} ((hF i v).mpr hv))⟩
    have hc := Finset.card_le_card hsub
    have h1 := hsize i
    have h2 := hlin i j hij
    omega
  have hoinj : Function.Injective o := by
    intro i j h
    apply hcontain i j
    intro x hx
    apply (hW j x).mp
    rw [← h]
    exact (hW i x).mpr hx
  have hsub (i : Fin m) (w : ℕ) (hk : k i = false)
      (hp : w = a i ∨ w = b i) : ∀ x, W w x → F i x := by
    intro x hx
    apply (hW i x).mp
    apply (hor i hk x).mpr
    rcases hp with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  have hsup (i : Fin m) (w : ℕ) (hk : k i = true)
      (hp : w = a i ∨ w = b i) : ∀ x, F i x → W w x := by
    intro x hx
    have hh := (hand i hk x).mp ((hW i x).mpr hx)
    rcases hp with rfl | rfl
    · exact hh.1
    · exact hh.2
  have hpbound (w : ℕ) (hw : 2 ≤ (P w).card) : n ≤ w := by
    by_contra! hn
    let v : Fin n := ⟨w, hn⟩
    have hs : P w ⊆ {v} := by
      intro u hu
      have hwu : W w {u} := (Finset.mem_filter.mp hu).2
      have hv : v ∈ ({u} : Finset (Fin n)) := (hinput v {u}).mp hwu
      simpa [eq_comm] using hv
    have hc := Finset.card_le_card hs
    simp at hc
    omega
  have hparentlt (i : Fin m) (w : ℕ) (hw : w = a i ∨ w = b i) : w < o i := by
    rcases hw with rfl | rfl
    · exact (hparents i).1
    · exact (hparents i).2
  have hclean (i : Fin m) (w : ℕ) (hk : k i = false)
      (hw : w = a i ∨ w = b i) : P w ⊆ S i := by
    intro v hv
    exact (hF i v).mp (hsub i w hk hw {v} (Finset.mem_filter.mp hv).2)
  have hlarge (i : Fin m) (w : ℕ) (hk : k i = true)
      (hw : w = a i ∨ w = b i) : 2 ≤ (P w).card := by
    have hs : S i ⊆ P w := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hsup i w hk hw {v} ((hF i v).mpr hv)⟩
    exact (hsize i).trans (Finset.card_le_card hs)
  have houtside (i j : Fin m) (hij : j ≠ i) : ∃ v ∈ S j, v ∉ S i := by
    by_contra! h
    have he : S j ⊆ S j ∩ S i := fun v hv => Finset.mem_inter.mpr ⟨hv, h v hv⟩
    have hc := Finset.card_le_card he
    have h1 := hsize j
    have h2 := hlin j i hij
    omega
  let T : Finset (Fin m) := Finset.univ.filter (fun i => 3 ≤ (S i).card)
  let shared (i : Fin m) (w : ℕ) : Prop :=
    ∃ j : Fin m, j ≠ i ∧ k j = true ∧ (w = a j ∨ w = b j)
  have haux (i : Fin m) (hi : i ∈ T) :
      ∃ w : ℕ, (w = a i ∨ w = b i) ∧ 2 ≤ (P w).card ∧
        (k i = false ∨ (k i = true ∧ ¬ shared i w)) := by
    cases hk : k i with
    | false =>
      have hc : S i ⊆ P (a i) ∪ P (b i) := by
        intro v hv
        have h := (hor i hk {v}).mp ((hW i {v}).mpr ((hF i v).mpr hv))
        rcases h with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have hcard := Finset.card_le_card hc
      have hu := Finset.card_union_le (P (a i)) (P (b i))
      have ht : 3 ≤ (S i).card := (Finset.mem_filter.mp hi).2
      by_cases ha : 2 ≤ (P (a i)).card
      · exact ⟨a i, Or.inl rfl, ha, Or.inl (by simp [hk])⟩
      · exact ⟨b i, Or.inr rfl, by omega, Or.inl (by simp [hk])⟩
    | true =>
      by_cases ha : shared i (a i)
      · by_cases hb : shared i (b i)
        · obtain ⟨j, hji, hj, hp⟩ := ha
          obtain ⟨l, hli, hl, hq⟩ := hb
          obtain ⟨u, hu, hui⟩ := houtside i j hji
          obtain ⟨v, hv, hvi⟩ := houtside i l hli
          let x : Finset (Fin n) := {u, v}
          have hja : F j x := ⟨u, hu, by simp [x]⟩
          have hlb : F l x := ⟨v, hv, by simp [x]⟩
          have htrue := (hW i x).mp ((hand i hk x).mpr
            ⟨hsup j (a i) hj hp x hja, hsup l (b i) hl hq x hlb⟩)
          obtain ⟨p, hpi, hpx⟩ := htrue
          simp [x] at hpx
          rcases hpx with rfl | rfl
          · exact False.elim (hui hpi)
          · exact False.elim (hvi hpi)
        · exact ⟨b i, Or.inr rfl, hlarge i (b i) hk (Or.inr rfl), Or.inr ⟨by simp [hk], hb⟩⟩
      · exact ⟨a i, Or.inl rfl, hlarge i (a i) hk (Or.inl rfl), Or.inr ⟨by simp [hk], ha⟩⟩
  choose p hp using (fun i : {i : Fin m // i ∈ T} => haux i.val i.property)
  have hpinj : Function.Injective p := by
    intro i j h
    apply Subtype.ext
    by_contra hij
    obtain ⟨hi, hci, hki⟩ := hp i
    obtain ⟨hj, hcj, hkj⟩ := hp j
    rcases hki with hki | ⟨hki, hsi⟩
    · rcases hkj with hkj | ⟨hkj, hsj⟩
      · have hss : P (p i) ⊆ S i.val ∩ S j.val := by
          intro v hv
          exact Finset.mem_inter.mpr ⟨hclean i.val (p i) hki hi hv,
            hclean j.val (p j) hkj hj (h ▸ hv)⟩
        have hc := Finset.card_le_card hss
        have hl := hlin i.val j.val hij
        omega
      · have he : j.val = i.val := hcontain j.val i.val (fun x hx =>
          hsub i.val (p i) hki hi x (h.symm ▸ hsup j.val (p j) hkj hj x hx))
        exact hij he.symm
    · rcases hkj with hkj | ⟨hkj, hsj⟩
      · have he : i.val = j.val := hcontain i.val j.val (fun x hx =>
          hsub j.val (p j) hkj hj x (h ▸ hsup i.val (p i) hki hi x hx))
        exact hij he
      · exact hsi ⟨j.val, Ne.symm hij, hkj, h.symm ▸ hj⟩
  have hdis (i : Fin m) (j : {i : Fin m // i ∈ T}) : o i ≠ p j := by
    intro he
    obtain ⟨hj, hcj, hkj⟩ := hp j
    have heq : i = j.val := by
      rcases hkj with hk | ⟨hk, _⟩
      · exact hcontain i j.val (fun x hx => hsub j.val (p j) hk hj x (he ▸ (hW i x).mpr hx))
      · exact (hcontain j.val i (fun x hx => (hW i x).mp (he.symm ▸ hsup j.val (p j) hk hj x hx))).symm
    have hl := hparentlt j.val (p j) hj
    subst i
    omega
  let O : Finset ℕ := Finset.univ.image o
  let A : Finset ℕ := Finset.univ.image p
  have hO : O.card = m := by
    simp [O, Finset.card_image_of_injective _ hoinj]
  have hA : A.card = T.card := by
    rw [show A = Finset.univ.image p from rfl, Finset.card_image_of_injective _ hpinj]
    simp
  have hOA : Disjoint O A := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwO hwA
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwO
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hwA
    exact hdis i j (hi.trans hj.symm)
  have hb : O ∪ A ⊆ Finset.Ico n (n+s) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_Ico.mpr (hob i)
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_Ico.mpr ⟨hpbound (p j) (hp j).2.1,
        (hparentlt j.val (p j) (hp j).1).trans (hob j.val).2⟩
  have hc := Finset.card_le_card hb
  rw [Finset.card_union_of_disjoint hOA, hO, hA] at hc
  simpa [T] using hc
