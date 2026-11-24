import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser

namespace PEqualNP.Outside.L_gct_122

open Module Finset PEqualNP.Gct.Helpers PEqualNP.Gct.Helpers.Kneser.Asm

private theorem polar2 {m : ℕ} (X : Submodule ℂ (Fin m → ℂ))
    (h2 : ∀ x ∈ X, ∑ i, x i ^ 2 = 0) :
    ∀ a ∈ X, ∀ b ∈ X, ∑ i, a i * b i = 0 := by
  intro a ha b hb
  have key : ∑ i, (2 : ℂ) * (a i * b i) =
      (∑ i, (a+b) i ^ 2) - (∑ i, a i ^ 2) - (∑ i, b i ^ 2) := by
    simp only [← Finset.sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]; ring
  rw [h2 _ (X.add_mem ha hb), h2 _ ha, h2 _ hb, ← mul_sum] at key
  simpa using key

private theorem polar4 {m : ℕ} (X : Submodule ℂ (Fin m → ℂ))
    (h4 : ∀ x ∈ X, ∑ i, x i ^ 4 = 0) :
    ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, ∀ d ∈ X,
      ∑ i, a i * b i * c i * d i = 0 := by
  have h22 : ∀ a ∈ X, ∀ b ∈ X, ∑ i, a i ^ 2 * b i ^ 2 = 0 := by
    intro a ha b hb
    have key : ∑ i, (12 : ℂ) * (a i ^ 2 * b i ^ 2) =
        (∑ i, (a+b) i ^ 4) + (∑ i, (a-b) i ^ 4) -
        2 * (∑ i, a i ^ 4) - 2 * (∑ i, b i ^ 4) := by
      simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [h4 _ (X.add_mem ha hb), h4 _ (X.sub_mem ha hb), h4 _ ha, h4 _ hb,
      ← mul_sum] at key
    simpa [show (12 : ℂ) ≠ 0 by norm_num] using key
  have h112 : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      ∑ i, a i * b i * c i ^ 2 = 0 := by
    intro a ha b hb c hc
    have key : ∑ i, (2 : ℂ) * (a i * b i * c i ^ 2) =
        (∑ i, (a+b) i ^ 2 * c i ^ 2) -
        (∑ i, a i ^ 2 * c i ^ 2) - (∑ i, b i ^ 2 * c i ^ 2) := by
      simp only [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h22 _ (X.add_mem ha hb) _ hc, h22 _ ha _ hc, h22 _ hb _ hc,
      ← mul_sum] at key
    simpa using key
  intro a ha b hb c hc d hd
  have key : ∑ i, (2 : ℂ) * (a i * b i * c i * d i) =
      (∑ i, a i * b i * (c+d) i ^ 2) -
      (∑ i, a i * b i * c i ^ 2) - (∑ i, a i * b i * d i ^ 2) := by
    simp only [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]; ring
  rw [h112 _ ha _ hb _ (X.add_mem hc hd), h112 _ ha _ hb _ hc,
    h112 _ ha _ hb _ hd, ← mul_sum] at key
  simpa using key

private theorem product_sum {m : ℕ} (X : Submodule ℂ (Fin m → ℂ))
    (h2 : ∀ x ∈ X, ∑ i, x i ^ 2 = 0) :
    ∀ v ∈ X * X, ∑ i, v i = 0 := by
  intro v hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro a ha b hb
    exact polar2 X h2 a ha b hb
  · intro a b ha hb
    simp only [Pi.add_apply, sum_add_distrib, ha, hb, add_zero]

private theorem product_perp {m : ℕ} (X : Submodule ℂ (Fin m → ℂ))
    (h4 : ∀ x ∈ X, ∑ i, x i ^ 4 = 0) :
    ∀ v ∈ X * X, ∀ w ∈ X * X, ∑ i, v i * w i = 0 := by
  intro v hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro a ha b hb w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro c hc d hd
      simpa only [Pi.mul_apply, mul_assoc] using polar4 X h4 a ha b hb c hc d hd
    · intro c d hc hd
      simp only [Pi.add_apply, mul_add, sum_add_distrib, hc, hd, add_zero]
  · intro a b ha hb w hw
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha w hw, hb w hw, add_zero]

-- A coordinatewise square has dimension at least its original subspace.
private theorem square_rank {m : ℕ} (X : Submodule ℂ (Fin m → ℂ)) :
    finrank ℂ X ≤ finrank ℂ (X * X : Submodule ℂ (Fin m → ℂ)) := by
  classical
  obtain ⟨u, hu, hunit⟩ := exists_isUnit_of_support (X ⊔ offSupp X X)
    (support_sup_offSupp X X)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
  let L : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.mulLeft ℂ (a+b)
  have hL : Function.Injective L := by
    rw [Pi.isUnit_iff] at hunit
    intro x y h
    funext i
    have hi := congr_fun h i
    change (a+b) i * x i = (a+b) i * y i at hi
    exact mul_left_cancel₀ (isUnit_iff_ne_zero.1 (hunit i)) hi
  have hmap : X.map L ≤ X * X := by
    rintro _ ⟨x, hx, rfl⟩
    have hzero : b*x = 0 := by
      funext i
      change b i * x i = 0
      by_cases hxi : x i = 0
      · rw [hxi, mul_zero]
      · have hbi := hb i ⟨x, hx, hxi⟩ ⟨x, hx, hxi⟩
        rw [hbi, zero_mul]
    change (a+b)*x ∈ X*X
    rw [add_mul, hzero, add_zero]
    exact Submodule.mul_mem_mul ha hx
  have hdim := Submodule.finrank_mono hmap
  have heq : finrank ℂ (X.map L) = finrank ℂ X :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hL X)).symm
  rwa [heq] at hdim

-- Zero coordinate sum makes the product space disjoint from its stabilizer.
private theorem stab_disjoint {m : ℕ} (V : Submodule ℂ (Fin m → ℂ))
    (hsum : ∀ v ∈ V, ∑ i, v i = 0) : V ⊓ stab V = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro z ⟨hzV, hzS⟩
  rw [Submodule.mem_bot]
  funext j
  obtain ⟨e, he, hev⟩ := exists_indicator hzS j
  have he01 : ∀ k, e k = 0 ∨ e k = 1 := fun k => by
    rw [hev k]; split_ifs <;> simp
  have hz : ∑ i, e i * z i = 0 := hsum _ (mem_stab.1 he _ hzV)
  have hrest := sum_restr e he01 z
  rw [hz] at hrest
  have hc : ∀ k : {k // e k = 1}, z k = z j := by
    intro k
    have hk := k.2
    rw [hev] at hk
    split_ifs at hk with h
    · exact h
    · exact (zero_ne_one hk).elim
  have hval : (∑ k : {k // e k = 1}, z k) =
      (Fintype.card {k // e k = 1} : ℂ) * z j := by
    simp only [hc, sum_const, card_univ, nsmul_eq_mul]
  haveI : Nonempty {k // e k = 1} := ⟨⟨j, by rw [hev]; simp⟩⟩
  have hn : (Fintype.card {k // e k = 1} : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [hval] at hrest
  exact (mul_eq_zero.1 hrest).resolve_left hn

private theorem global_bound (m : ℕ) (X : Submodule ℂ (Fin m → ℂ))
    (h2 : ∀ x ∈ X, ∑ i, x i ^ 2 = 0)
    (h4 : ∀ x ∈ X, ∑ i, x i ^ 4 = 0) :
    3 * finrank ℂ X ≤ m := by
  classical
  by_cases hX : X = ⊥
  · simp [hX]
  let V := X * X
  have hsum : ∀ v ∈ V, ∑ i, v i = 0 := product_sum X h2
  have hp : ∀ v ∈ V, ∀ w ∈ V, ∑ i, v i * w i = 0 := product_perp X h4
  have hd : finrank ℂ X ≤ finrank ℂ V := square_rank X
  have hK := PEqualNP.Gct.L065 m X X (stab V) hX hX (fun _ => Iff.rfl)
  change _ + _ ≤ finrank ℂ V + _ at hK
  have hs : ∀ v ∈ V ⊔ stab V, ∀ w ∈ V, ∑ i, v i * w i = 0 := by
    intro v hv w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have hb' : ∑ i, b i * w i = 0 := hsum _ (mem_stab.1 hb _ hw)
    simp only [Pi.add_apply, add_mul, sum_add_distrib, hp a ha w hw, hb', add_zero]
  have hdim := perp_bound (V ⊔ stab V) V hs
  have heq := Submodule.finrank_sup_add_finrank_inf_eq V (stab V)
  rw [stab_disjoint V hsum, finrank_bot, add_zero] at heq
  rw [heq, Fintype.card_fin] at hdim
  omega

end PEqualNP.Outside.L_gct_122

theorem PEqualNP.Outside.L_gct_122 : ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m :=
  PEqualNP.Outside.L_gct_122.global_bound
