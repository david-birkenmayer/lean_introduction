set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

inductive Even : N -> Prop where
  | zero_even : Even zero                                  -- zero is an even number
  | next_even {n : N} (p : Even n) : Even (succ (succ n))  -- if n is even, so is n+2
open Even


----------------------------------------------------------------------------------
-- Part 4: **Logic**
-- introducing: **Curry-Howard Correspondence**
----------------------------------------------------------------------------------


-- Using ⟶ and False, we can define all logical connectives:
-- ¬ P     := P → False
-- P ∨ Q   := (P → Q) → Q
-- P ∧ Q   := ¬ (¬ P ∧ ¬ Q)
-- P ↔ Q   := (P → Q) ∧ (Q → P)


-- In practice only the first relation for negation is used.
-- Hover over negation symbol ¬ to see the explanation

-- An example of how to prove negation
theorem one_is_not_even : ¬ Even (succ zero) :=
  fun s => nomatch s -- The compiler sees that there is not possible pattern for p to exist

-- A more sophisticated example:
theorem succ_even_is_not_even {n : N} (h : Even n) : ¬ Even (succ n) :=
  fun s =>
  match h, s with
  | zero_even, s => one_is_not_even s
  | next_even h', next_even s' => succ_even_is_not_even h' s'
  -- The compiler understands that the other cases are impossible

-- the other connectives are defined as datatypes to make things less cumbersome.
-- Hover over the ∧ and ∨ to see the explanation
theorem and_assumption {P Q R: Prop} (h: (P → R) ∨ (Q → R)) : (P ∧ Q) → R :=
  fun pq =>
  match h with
  | Or.inl p => p (And.left pq)
  | Or.inr q => q (And.right pq)


-- We can also emulate Quantifiers! Lean has *Syntacitc Sugar* for them:

-- the theorem
theorem basic_property : ∀ n : N , n = n :=
  _

-- is equivalent to
theorem basic_property' (n : N) : n = n :=
  _
