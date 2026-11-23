import Mathlib

theorem PEqualNP.Research.CutCapacity : ∀ (r k m : ℕ)
  (rows : Fin r → Fin m → Bool)
  (encode : Fin r → Fin k → Bool)
  (decode : (Fin k → Bool) → Fin m → Bool),
  Function.Injective rows →
  (∀ i, decode (encode i) = rows i) →
  r ≤ 2 ^ k := by
  intro r k m rows encode decode hrows hdecode
  have hinj : Function.Injective encode := by
    intro a b hab
    apply hrows
    exact (hdecode a).symm.trans ((congrArg decode hab).trans (hdecode b))
  simpa using Fintype.card_le_of_injective encode hinj
