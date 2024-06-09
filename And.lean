import Mathlib.Tactic


-- In this section we will talk about And, and all of it's wonderful features that allow us to exploit it.

-- Here is the definition (with a prime so Lean doesn't freak out)

-- And is a structure which takes two arguments that must be propositions (which means it only takes arguments that have really boring identity types, if you believe that all proofs are equal then this won't bother you).
structure And' (a b : Prop) : Prop where
  -- We may have a term of And if we can produce the following
  intro ::
  -- a proof, left, of a and
  left : a
  -- a proof, right, of b.
  right : b

-- Thus it is worth noting that And : Prop → Prop → Prop.
-- Now we can try and prove something I guess
theorem thing {A B C : Prop} : (A ∧ B) ∧ C → A ∧ (B ∧ C) := by
  intro h --introduce the hypothesis
  apply And.intro --it would suffice to show A and B ∧ C
  exact h.left.left -- this is a proof of A
  apply And.intro -- it would suffice to show B and C
  exact h.left.right -- proof of B
  exact h.right -- proof of C

-- or, and here is a great excersise, see how you can obtain the proof below from the one above.

theorem thing' {A B C : Prop} : (A ∧ B) ∧ C → A ∧ (B ∧ C) := fun h => And.intro (h.left.left) (And.intro (h.left.right) (h.right))

-- The point of this is to show that if you are proving a statement with an And, then the items included in the structure are the only tools you have available in order to produce withness to And. Because of that every tactic you can use will in some way manipulate these items. If you become familiar with each of them, you will know when to just state the term you are after, or when to use the tactics, which obfuscate the actual proof term.
