import Lean
namespace PEqualNP.CircuitLowerBounds
inductive GateOp where
  | and | or | not | mod (m : Nat) | maj
def GateOp.eval : GateOp → List Bool → Bool
  | .and,l => l.all id
  | .or,l => l.any id
  | .not,l => !(l.headD false)
  | .mod m,l => decide (l.count true % m = 0)
  | .maj,l => decide (l.length ≤ 2 * l.count true)
structure Gate where
  op : GateOp
  inputs : List Nat
structure Circuit where
  gates : List Gate
  output : Nat
def Circuit.wires (C : Circuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
def Circuit.eval (C : Circuit) (x : List Bool) : Bool := (C.wires x).getD C.output false
def Circuit.size (C : Circuit) : Nat := C.gates.length
end PEqualNP.CircuitLowerBounds
namespace PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds
def FanInTwo (C : Circuit) : Prop := ∀ g ∈ C.gates,
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def HasCircuitSize (n : Nat) (f : (Fin n → Bool) → Bool) (s : Nat) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x
end PEqualNP.MetaComplexity
