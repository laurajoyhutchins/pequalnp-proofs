import PEqualNP.Research.PetersenOrCut
namespace PEqualNP.Research.Hoist
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem legal_iff (C : Circuit) : Legal C ↔ FanInTwo C := by
  simp [Legal, LegalGate, FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff]

-- These six statements are precisely the checked L-meta-1667 through L-meta-1672.
-- Keep them explicit as hypotheses so the residual problem does not depend on
-- stale copies of accepted artifacts in a research branch.
def UpstreamSix : Prop := ∀ r : Fin 6, ∀ C : Circuit, FanInTwo C →
  (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x (rep r).1 && x (rep r).2)) →
  circuitFun 9 C = edge → 16 ≤ C.size

theorem upstream_six (h : UpstreamSix) : SixBounds := by
  intro r C hc hf first
  exact h r C ((legal_iff C).mp hc) first hf

theorem upstream_noRawAnd (h : UpstreamSix) (C : Circuit) (hc : FanInTwo C)
    (hf : circuitFun 9 C = edge) (hs : C.size < 16) : NoRawAnd C :=
  noRawAnd_of_six (upstream_six h) C ((legal_iff C).mpr hc) hf hs

theorem upstream_or_cut (u v : Fin 9) (h : UpstreamSix)
    (residual : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x u || x v)) →
      circuitFun 9 C = edge → NoRawAnd C → 16 ≤ C.size) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x u || x v)) →
      circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C hc first hf
  apply or_first_cut u v (upstream_six h) _ C ((legal_iff C).mpr hc) hf first
  intro D hd fd anchor noAnd
  exact residual D ((legal_iff D).mp hd) anchor fd noAnd

#print axioms upstream_or_cut
end PEqualNP.Research.Hoist
