import Mathlib

theorem PEqualNP.Research.MonotoneReplace : ∀ (P N : ℕ → Prop) (c : ℕ → Bool → Bool) (u v : ℕ → Bool),
    (∀ x, c x false = true → c x true = true) →
    (∀ x, P x → u x = true → v x = true) →
    (∀ x, N x → v x = true → u x = true) →
    (∀ x, P x → c x (u x) = true) →
    (∀ x, N x → c x (u x) = false) →
    (∀ x, P x → c x (v x) = true) ∧
    (∀ x, N x → c x (v x) = false) := by
  intro P N c u v hm hpos hneg hp hn
  constructor
  · intro x hx
    cases hu : u x with
    | false =>
      have h0 : c x false = true := by simpa [hu] using hp x hx
      cases hv : v x with
      | false => simpa [hv] using h0
      | true => simpa [hv] using hm x h0
    | true =>
      have hv := hpos x hx hu
      simpa [hu, hv] using hp x hx
  · intro x hx
    cases hv : v x with
    | true =>
      have hu := hneg x hx hv
      simpa [hu, hv] using hn x hx
    | false =>
      cases hu : u x with
      | false => simpa [hu, hv] using hn x hx
      | true =>
        have h1 : c x true = false := by simpa [hu] using hn x hx
        cases h0 : c x false with
        | false => simpa [hv] using h0
        | true => have h := hm x h0; simp_all
