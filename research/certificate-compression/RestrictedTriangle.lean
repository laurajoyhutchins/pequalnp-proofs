import ProjectedCertificate

namespace CircuitCompression

-- Prepending a fixed bit gives a uniform gate-saving restriction.
def prepend (b : Bool) (x : Fin n → Bool) : Fin (n+1) → Bool := Fin.cases b x

theorem prependCover (b : Bool) (n : Nat) : Covers (prepend (n:=n) b) (initial (n+1)) (initial n) := by
  intro f hf
  simp only [initial,List.mem_cons,List.mem_ofFn] at hf
  rcases hf with h | h | ⟨i,h⟩
  · subst f; exact (initialConstants n).1
  · subst f; exact (initialConstants n).2
  · subst f
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b
      · exact (initialConstants n).1
      · exact (initialConstants n).2
    · have e : project (prepend b) (input j.succ) = input j := by
        funext x; simp [project,prepend,input]
      rw [e]
      simp [initial,List.mem_ofFn]

theorem prependCollapse (b : Bool) (x : Fin n → Bool) :
    Collapses (prepend b) (prepend false x) (prepend true x) (initial (n+1)) := by
  intro f hf hd
  simp only [initial,List.mem_cons,List.mem_ofFn] at hf
  rcases hf with h | h | ⟨i,h⟩
  · subst f; exact False.elim (hd rfl)
  · subst f; exact False.elim (hd rfl)
  · subst f
    revert hd
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _
      cases b
      · exact Or.inl (by funext y; simp [project,prepend,input,zero])
      · exact Or.inr (by funext y; simp [project,prepend,input,one])
    · intro hd
      exact False.elim (hd (by simp [input,prepend]))


def edgeTriangle : Wire (Fin 5 → Bool) := fun x =>
  (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)
def tailTriangle : Wire (Fin 4 → Bool) := fun x =>
  x 0 || (x 1 && x 2) || (x 2 && x 3) || (x 1 && x 3)

theorem notInitial {n : Nat} {f : Wire (Fin n → Bool)}
    (h0 : f (fun _ => false) = false) (h1 : f (fun _ => true) = true)
    (hi : ∀ i : Fin n, ∃ x, f x ≠ x i) : f ∉ initial n := by
  intro hm
  simp only [initial,List.mem_cons,List.mem_ofFn] at hm
  rcases hm with h | h | ⟨i,h⟩
  · have he := congrFun h (fun _ => true)
    simp [h1,zero] at he
  · have he := congrFun h (fun _ => false)
    simp [h0,one] at he
  · obtain ⟨x,hx⟩ := hi i
    exact hx (congrFun h.symm x)

def rowOf {n m : Nat} (r : Fin m) : Fin n → Bool := fun i => r.val.testBit i.val

theorem edgeNotInitial : edgeTriangle ∉ initial 5 := by
  apply notInitial (by decide) (by decide)
  intro i
  have h : ∀ i : Fin 5, ∃ j : Fin 32, edgeTriangle (rowOf j) ≠ rowOf (n:=5) j i := by decide
  obtain ⟨j,hj⟩ := h i
  exact ⟨rowOf j,hj⟩

theorem tailNotInitial : tailTriangle ∉ initial 4 := by
  apply notInitial (by decide) (by decide)
  intro i
  have h : ∀ i : Fin 4, ∃ j : Fin 16, tailTriangle (rowOf j) ≠ rowOf (n:=4) j i := by decide
  obtain ⟨j,hj⟩ := h i
  exact ⟨rowOf j,hj⟩

theorem restrictEdge : project (prepend true) edgeTriangle = tailTriangle := by
  funext x; simp [project,prepend,edgeTriangle,tailTriangle] <;> rfl

theorem restrictTail : project (prepend false) tailTriangle = triangle := by
  funext x; simp [project,prepend,tailTriangle,triangle] <;> rfl

-- The exact lower bound is obtained by two witnessed restrictions and a 3-gate residual.
theorem edgeTriangleLower {T : List (Wire (Fin 5 → Bool))} {k : Nat}
    (hr : Run (initial 5) k T) (ht : edgeTriangle ∈ T) : 6 ≤ k := by
  let y : Fin 4 → Bool := fun i => i == 0
  have hdiff : edgeTriangle (prepend false y) ≠ edgeTriangle (prepend true y) := by decide
  obtain ⟨m,U,hm,hu,hc⟩ := saveGate hr ht edgeNotInitial hdiff
    (prependCover true 4) (initialConstants 4) (prependCollapse true y)
  have ht' : tailTriangle ∈ U := by rw [← restrictEdge]; exact hc _ ht
  let z : Fin 3 → Bool := fun _ => false
  have hdiff' : tailTriangle (prepend false z) ≠ tailTriangle (prepend true z) := by decide
  obtain ⟨l,V,hl,hv,hc'⟩ := saveGate hu ht' tailNotInitial hdiff'
    (prependCover false 3) (initialConstants 3) (prependCollapse false z)
  have ht'' : triangle ∈ V := by rw [← restrictTail]; exact hc' _ ht'
  have h := triangleLower hv ht''
  omega

end CircuitCompression
