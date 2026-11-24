import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  let g : (Fin 3 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)
  have hnc : ∃ y y' : Fin 3 → Bool, g y ≠ g y' := ⟨fun _ => false, fun _ => true, by decide⟩
  have hstep (t : Nat) : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) (t + 2) ↔ 4 ≤ t := by
    have he : (fun x : Fin (2 + 3) → Bool => (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) := by
      funext x
      have h0 : Fin.castAdd 3 (0 : Fin 2) = (0 : Fin 5) := by decide
      have h1 : Fin.castAdd 3 (1 : Fin 2) = (1 : Fin 5) := by decide
      have h2 : Fin.natAdd 2 (0 : Fin 3) = (2 : Fin 5) := by decide
      have h3 : Fin.natAdd 2 (1 : Fin 3) = (3 : Fin 5) := by decide
      have h4 : Fin.natAdd 2 (2 : Fin 3) = (4 : Fin 5) := by decide
      simp only [Bool.or_assoc, g, h0, h1, h2, h3, h4]
    simpa only [he] using (PEqualNP.MetaComplexity.L153 3 t g hnc).trans (PEqualNP.MetaComplexity.L100 t)
  intro s
  constructor
  · rintro ⟨C,hC,hsize,hfun⟩
    have h := (hstep (s-2)).mp ⟨C,hC,by omega,hfun⟩
    omega
  · intro hs
    have h := (hstep (s-2)).mpr (by omega)
    have he : s-2+2 = s := by omega
    simpa only [he] using h
