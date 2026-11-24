import Lean

namespace ReaderWitness

-- Each signature is the deleted part of a direct reader: a raw bit, or a
-- pure binary gate on two deleted inputs. Unary complements separate the
-- same pairs as the raw bit; constants and nonreaders separate no pairs.
inductive Column where
  | raw (i : Fin 5)
  | band (i j : Fin 5)
  | bor (i j : Fin 5)

def eval : Column → Nat → Bool
  | .raw i, a => a.testBit i.val
  | .band i j, a => a.testBit i.val && a.testBit j.val
  | .bor i j, a => a.testBit i.val || a.testBit j.val

abbrev Row := Nat × Nat × Nat

def witnesses : List Row :=
  [(26,18,384),(26,10,128),(22,20,256),(22,18,384),(21,5,256),
    (19,18,384),(13,9,192),(12,5,256),(11,9,192)]

def fixed : Column := .band 0 3

def hits (c : Column) (r : Row) : Bool := eval c r.1 != eval c r.2.1

def count (p : Row → Bool) : List Row → Nat
  | [] => 0
  | r::rs => (if p r then 1 else 0) + count p rs

def cover (cs : List Column) (r : Row) : Bool := cs.any (fun c => hits c r)

theorem countUnion (p q : Row → Bool) (rs : List Row) :
    count (fun r => p r || q r) rs ≤ count p rs + count q rs := by
  induction rs with
  | nil => simp [count]
  | cons r rs ih =>
    simp only [count]
    by_cases hp : p r = true <;> by_cases hq : q r = true <;> simp [hp,hq] <;> omega

theorem colCapacity (c : Column) : count (hits c) witnesses ≤ 2 := by
  cases c with
  | raw i => exact (show ∀ i : Fin 5, count (hits (.raw i)) witnesses ≤ 2 by decide) i
  | band i j => exact (show ∀ i j : Fin 5, count (hits (.band i j)) witnesses ≤ 2 by decide) i j
  | bor i j => exact (show ∀ i j : Fin 5, count (hits (.bor i j)) witnesses ≤ 2 by decide) i j

theorem fixedCapacity : count (hits fixed) witnesses = 0 := by decide

theorem coverCapacity (cs : List Column) : count (cover cs) witnesses ≤ 2 * cs.length := by
  induction cs with
  | nil => decide
  | cons c cs ih =>
    have h := countUnion (hits c) (cover cs) witnesses
    have hc := colCapacity c
    change count (fun r => hits c r || cover cs r) witnesses ≤ 2 * (cs.length+1)
    omega

theorem countFull (p : Row → Bool) (rs : List Row) (h : ∀ r ∈ rs, p r = true) : count p rs = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := h r (by simp)
    have hs := ih (fun x hx => h x (by simp [hx]))
    simp [count,hr,hs]
    omega

theorem sixReaders (cs : List Column) (h : ∀ r ∈ witnesses, cover (fixed::cs) r = true) :
    6 ≤ (fixed::cs).length := by
  have hf := countFull (cover (fixed::cs)) witnesses h
  have hlen : witnesses.length = 9 := rfl
  have hcap := countUnion (hits fixed) (cover cs) witnesses
  have hzero := fixedCapacity
  have hc := coverCapacity cs
  change count (fun r => hits fixed r || cover cs r) witnesses = witnesses.length at hf
  simp only [List.length_cons]
  omega

-- The nine pairs really distinguish the L-meta-1669 target at their
-- listed common outside assignment, and the fixed AND does not separate them.
def edge (a : Nat) (i j : Nat) : Bool := a.testBit i && a.testBit j

def target (a : Nat) : Bool :=
  edge a 0 1 || edge a 1 2 || edge a 2 3 || edge a 3 4 || edge a 4 0 ||
  edge a 0 5 || edge a 1 6 || edge a 2 7 || edge a 3 8 || edge a 5 7 ||
  edge a 6 8 || edge a 8 5

theorem actualWitnesses : witnesses.all (fun r =>
    (decide (r.1 < 32) && decide (r.2.1 < 32) && r.2.2 % 32 == 0) &&
    (target (r.1 ||| r.2.2) != target (r.2.1 ||| r.2.2)) && !hits fixed r) = true := by decide

-- A general trace factoring lemma: the outside pool initially agrees,
-- and each step factors through its own deleted-input signature and that pool.
theorem foldCongr {G A B : Type} (steps : List G) (code : G → A → B)
    (step : G → B → List Bool → List Bool) (a b : A)
    (h : ∀ g ∈ steps, code g a = code g b) (pool : List Bool) :
    steps.foldl (fun s g => step g (code g a) s) pool =
    steps.foldl (fun s g => step g (code g b) s) pool := by
  induction steps generalizing pool with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, h g (by simp)]
    exact ih (fun g hg => h g (by simp [hg])) _

-- Split evaluator: direct deleted inputs are distinct from outside/earlier wires.
abbrev Operand := Sum (Fin 5) Nat
inductive Gate where
  | const (b : Bool)
  | copy (u : Operand)
  | bnot (u : Operand)
  | band (u v : Operand)
  | bor (u v : Operand)

def operand (a : Nat) (pool : List Bool) : Operand → Bool
  | .inl i => a.testBit i.val
  | .inr i => pool.getD i false

def gateEval (g : Gate) (a : Nat) (pool : List Bool) : Bool :=
  match g with
  | .const b => b
  | .copy u => operand a pool u
  | .bnot u => !operand a pool u
  | .band u v => operand a pool u && operand a pool v
  | .bor u v => operand a pool u || operand a pool v

def unaryCode : Operand → Option Column
  | .inl i => some (.raw i)
  | .inr _ => none

def binaryCode (mk : Fin 5 → Fin 5 → Column) : Operand → Operand → Option Column
  | .inl i, .inl j => some (mk i j)
  | .inl i, .inr _ => some (.raw i)
  | .inr _, .inl j => some (.raw j)
  | .inr _, .inr _ => none

def gateCode : Gate → Option Column
  | .const _ => none
  | .copy u | .bnot u => unaryCode u
  | .band u v => binaryCode Column.band u v
  | .bor u v => binaryCode Column.bor u v

def codeValue (g : Gate) (a : Nat) : Bool := (gateCode g).elim false (fun c => eval c a)

theorem evalCongr (g : Gate) (a b : Nat) (p : List Bool)
    (h : codeValue g a = codeValue g b) : gateEval g a p = gateEval g b p := by
  cases g with
  | const => rfl
  | copy u => cases u <;> simp_all [codeValue,gateCode,unaryCode,gateEval,operand,eval]
  | bnot u => cases u <;> simp_all [codeValue,gateCode,unaryCode,gateEval,operand,eval]
  | band u v => cases u <;> cases v <;> simp_all [codeValue,gateCode,binaryCode,gateEval,operand,eval]
  | bor u v => cases u <;> cases v <;> simp_all [codeValue,gateCode,binaryCode,gateEval,operand,eval]

def run (gs : List Gate) (a : Nat) (pool : List Bool) :=
  gs.foldl (fun p g => p ++ [gateEval g a p]) pool

theorem runEqual (gs : List Gate) (a b : Nat) (pool : List Bool)
    (h : ∀ g ∈ gs, codeValue g a = codeValue g b) : run gs a pool = run gs b pool := by
  induction gs generalizing pool with
  | nil => rfl
  | cons g gs ih =>
    have he := evalCongr g a b pool (h g (by simp))
    simp only [run,List.foldl_cons,he]
    exact ih (pool ++ [gateEval g b pool]) (fun g hg => h g (by simp [hg]))

def columns (gs : List Gate) : List Column := gs.filterMap gateCode

theorem codeMem {gs : List Gate} {g : Gate} {c : Column} (hg : g ∈ gs)
    (hc : gateCode g = some c) : c ∈ columns gs := by
  exact List.mem_filterMap.mpr ⟨g,hg,hc⟩

theorem separated (gs : List Gate) (a b : Nat) (pool : List Bool) (out : Nat)
    (h : (run gs a pool).getD out false ≠ (run gs b pool).getD out false) :
    ∃ c ∈ columns gs, eval c a ≠ eval c b := by
  classical
  by_cases hn : ∃ c ∈ columns gs, eval c a ≠ eval c b
  · exact hn
  · exfalso
    apply h
    have hs : ∀ g ∈ gs, codeValue g a = codeValue g b := by
      intro g hg
      cases he : gateCode g with
      | none => simp [codeValue,he]
      | some c =>
        have hm := codeMem hg he
        have eq : eval c a = eval c b := by
          by_cases heq : eval c a = eval c b
          · exact heq
          · exact False.elim (hn ⟨c,hm,heq⟩)
        simpa [codeValue,he] using eq
    rw [runEqual gs a b pool hs]

theorem readerCertificate (gs : List Gate) (cs : List Column) (out : Nat)
    (hfixed : columns gs = fixed :: cs)
    (hw : ∀ r ∈ witnesses, ∃ pool : List Bool,
      (run gs r.1 pool).getD out false ≠ (run gs r.2.1 pool).getD out false) :
    6 ≤ (columns gs).length := by
  rw [hfixed]
  apply sixReaders
  intro r hr
  obtain ⟨pool,hp⟩ := hw r hr
  obtain ⟨c,hc,hd⟩ := separated gs r.1 r.2.1 pool out hp
  rw [hfixed] at hc
  apply List.any_eq_true.mpr
  exact ⟨c,hc,by simpa [hits] using hd⟩

#print axioms sixReaders
#print axioms actualWitnesses
#print axioms foldCongr
#print axioms readerCertificate
end ReaderWitness
