def andAssoc : Prop := ∀ P Q R : Prop, P ∧ (Q ∧ R) → (P ∧ Q) ∧ R

-- This proof term is correct
def pfAndAssoc : andAssoc :=
  fun (P Q R : Prop)  =>

    fun (h : P ∧ (Q ∧ R)) =>
      let p : P := h.left
      let q : Q := h.right.left
      let r : R := h.right.right
      let pqr : (P ∧ Q) ∧ R := And.intro (And.intro p q) r
      pqr
