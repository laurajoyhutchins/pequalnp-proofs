import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  let g : (Fin 4 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)
  have hnc : ∃ y y' : Fin 4 → Bool, g y ≠ g y' := ⟨fun _ => false, fun _ => true, by decide⟩
  have hstep (t : Nat) : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) (t + 2) ↔ 3 ≤ t := by
    have he : (fun x : Fin (2 + 4) → Bool => (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) := by
      funext x
      have h0 : Fin.castAdd 4 (0 : Fin 2) = (0 : Fin 6) := by decide
      have h1 : Fin.castAdd 4 (1 : Fin 2) = (1 : Fin 6) := by decide
      have h2 : Fin.natAdd 2 (0 : Fin 4) = (2 : Fin 6) := by decide
      have h3 : Fin.natAdd 2 (1 : Fin 4) = (3 : Fin 6) := by decide
      have h4 : Fin.natAdd 2 (2 : Fin 4) = (4 : Fin 6) := by decide
      have h5 : Fin.natAdd 2 (3 : Fin 4) = (5 : Fin 6) := by decide
      simp only [Bool.or_assoc, g, h0, h1, h2, h3, h4, h5]
    simpa only [he] using (PEqualNP.MetaComplexity.L153 4 t g hnc).trans (PEqualNP.MetaComplexity.L112 t)
  intro s
  constructor
  · rintro ⟨C,hC,hsize,hfun⟩
    have h := (hstep (s-2)).mp ⟨C,hC,by omega,hfun⟩
    omega
  · intro hs
    have h := (hstep (s-2)).mpr (by omega)
    have he : s-2+2 = s := by omega
    simpa only [he] using h
