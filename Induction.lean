import Mathlib.Tactic
-- Induction is by far the most interesting notion in dependent type theory. Instead of it being about
-- indexing, it is an argument that inductive types only need proofs on their canonical elements.

-- That is, the naturals only need proofs on 0 and the successors.
-- The booleans only need proofs on true and false, etc.

-- Let us look at induction rules for famous types

#check Nat.rec

#check Bool.rec

#check Empty.rec

-- This has interesting consequences, consider:
theorem ex_falso {P : Prop} : Empty → P := Empty.rec
-- That is, to show that P holds, we need to show it holds for all of none of it's elements!

-- Similairly
theorem bool_either_t_o_f: ∀ x: Bool, x = true ∨ x = false := by
apply Bool.rec
right
rfl

left
rfl

theorem bool_either_t_o_f': ∀ x: Bool, x = true ∨ x = false :=
Bool.rec (Or.inr (rfl)) (Or.inl (rfl))
