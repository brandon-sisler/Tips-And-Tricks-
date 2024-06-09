import Mathlib.Tactic

-- Dealing with constructor and apply

-- In this file I will show you some of the tricks to shortening
-- proofs and making them closer to the λ-calculus which also
-- provides a clearer picture of what the witness of a proposition
-- really is. Consider

theorem trivial_but_true {A B : Prop} (a : A) (b : B) : A ∧ B := by
  constructor
  assumption
  assumption

-- In this proof you told Lean to break up the goal if it could
-- into it's respective parts, in this case And has the structure of a thing with a left and a right part.
-- Specifically then we can make a term of And A B by providing a proof of A and a proof of B. Which we said were assumptions.

-- However, our proof does not actually reveal what Lean considered a sufficient proof. We will need that now.
theorem trivial_but_true' {A B : Prop} (a : A) (b : B) : A ∧ B := by
  apply And.intro
  exact a
  exact b

-- Okay this is better, we can see that to obtain a witness of A ∧ B, we can instead provide a witness of A and a witness of B, which we did by providing a and b resp.

-- But we can do even better.

theorem trivial_but_true'' {A B : Prop} (a : A) (b : B) : A ∧ B := And.intro a b

-- Since And.into : A → B → A ∧ B, then we can get our proof simply by plugging in our proofs, and keep in mind that And.intro is NOT a tactic! It is a proof term, and it lives within the lambda calculus by definition. So it is clear that this proof is the best one.

-- Dealing with or statements and elses

-- Now consider

theorem Even_more_trivial_but_true {A B : Prop} (a : A) (b : B) : ∃x : A, A ∨ B := by
  use a
  left
  assumption

-- Well this is ambiguous, it is not clear at all what term we constructed. That is especially bad since the proof is supposedly so simple.

-- Consider though, what an Or statment really is at heart. Given a proposition A ∨ B, it should be that you either hand over a proof of A or hand over a proof of B and be done with it. All you need to do is SPECIFY which.

-- Similairly if you think about what makes an existance statement, ∃x , P true. It is a pair ⟨x, p⟩ where p : P that is perhaps dependent on x.

-- Time to put it in action

theorem Even_more_trivial_but_true' {A B : Prop} (a : A) (b : B) : ∃x : A, A ∨ B := ⟨a,
  by
  left
  assumption ⟩

theorem Even_more_trivial_but_true'' {A B : Prop} (a : A) (b : B) : ∃x : A, A ∨ B := ⟨a,
  by
  apply Or.inl
  assumption ⟩

theorem Even_more_trivial_but_true''' {A B : Prop} (a : A) (b : B) : ∃x : A, A ∨ B := ⟨a,
  by
  apply Or.inl
  exact a ⟩

theorem Even_more_trivial_but_true'''' {A B : Prop} (a : A) (b : B) : ∃x : A, A ∨ B := ⟨a, Or.inl a⟩
