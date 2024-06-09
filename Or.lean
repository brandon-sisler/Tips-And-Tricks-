import Mathlib.Tactic

-- In this section we will talk about Or.
-- Let us look at the definition of Or

inductive Or' (a b : Prop) : Prop where
  -- A proof of A gives a proof of A ∨ B
  | inl (h : a) : Or' a b
  -- A proof of B gives a proof of A ∨ B
  | inr (h : b) : Or' a b

-- Do not be fooled into thinking that this structure is the same as And!
-- In order to construct a term of A ∧ B it was required that we construct a term a : A and a term b : B. Now we only need one.

theorem symm_or {A B: Prop} : A ∨ B → (B ∨ A) := by
  intro h -- Let h be our initial assumption that A ∨ B
  cases' h with a b -- Then by construction either there is a term a : A or a term b : B
  right -- If a : A then we can construct a proof of the right term
  exact a
  left -- If b : B then we can construct a proof of the left term
  exact b

-- This proof is actually pretty nice, but we can do even better. Consiter the reason that things like `left, exact a' work. Essentially er are saying that inl a is a term of Or A B. Let us see that in action.

theorem symm_or' {A B: Prop} : A ∨ B → (B ∨ A) := by
  intro h -- Let h be our initial assumption that A ∨ B
  cases' h with a b -- Then by construction either there is a term a : A or a term b : B
  exact Or.inr a
  exact Or.inl b

-- But even cases is suseptible now, since we can just use the standard elimination rules for Or.
-- Consider the term
#check Or.rec -- which is the induction rule for Or
theorem symm_or'' {A B: Prop} : A ∨ B → (B ∨ A) := by
  apply Or.rec
  intro a
  exact Or.inr a
  intro b
  exact Or.inl b

-- And now our final term is easy
theorem symm_or''' {A B: Prop} : A ∨ B → (B ∨ A) := Or.rec (fun a : A => Or.inr a) (fun b : B => Or.inl b)
