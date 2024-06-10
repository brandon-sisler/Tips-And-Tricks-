import Mathlib.Tactic

-- Else is by far the coolest one for this sort of thing. Let us look at the definition.

inductive Exists' {α : Sort u} (p : α → Prop) : Prop where
  -- To prove that P(x) holds for some x, you need to proide a pair ⟨w, h⟩ in which w is a term and h is a proof of P (w).
  | intro (w : α) (h : p w) : Exists' p

theorem root_of_polym : ∃n, n^2 - 1 = 0 := by
  use 1
  rfl

-- or rather

theorem root_of_polym' : ∃n, n^2 - 1 = 0 := ⟨1, rfl⟩
