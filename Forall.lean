import Mathlib.Tactic

-- This section you already know, since it is just the intros trick but I'll put a reference example.

-- Lets throw some junk in here just to show how the things work.
theorem thing {P Q: Prop} : ∀ x : P, P → Q → P := by
intros x hp hq
exact x

-- or
theorem thing' {P Q: Prop} : ∀ x : P, P → Q → P := fun x hp hq => by
exact x

-- and best

theorem thing'' {P Q: Prop} : ∀ x : P, P → Q → P := fun x hp hq => x

-- but another funny option
theorem thing''' {P Q: Prop} : ∀ x : P, P → Q → P := fun x hp hq => hp

-- almost makes you think that proof could not be functionally identical.
