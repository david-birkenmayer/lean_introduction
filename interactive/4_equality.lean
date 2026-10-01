set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N → N
open N

----------------------------------------------------------------------------------
-- **Part 4a: Equality**
----------------------------------------------------------------------------------

-- Equality is not built into Lean either: it is an inductive type, exactly like
-- ∧, ∨ and ∃ were in part 3. The only constructor is 'refl', and to use it the
-- two sides must be *the same term*.
inductive Equal {A : Type} : A → A → Prop where
  | refl (a : A) : Equal a a
infix:50 (priority := high) " = " => Equal  -- this overrides Lean's own '='
open Equal

-- Matching on a proof of 'n = m' is what makes equality useful: 'refl' is the
-- only way such a proof can have been built, so the compiler learns n and m are
-- the same term, and the goal becomes something refl can close.

-- Equality is reflexive
theorem reflexive {n : N} : n = n :=
  refl n

-- Equality is symmetric
theorem symmetric {n m : N} : n = m → m = n :=
  fun h => match h with | refl _ => refl _

-- Equality is transitive
theorem transitive {n m k : N} : n = m → m = k → n = k :=
  fun h1 h2 => match h1, h2 with | refl _, refl _ => refl _

-- The succ function preserves equality
theorem succ_equal {n m : N} : n = m → succ n = succ m :=
  fun h => match h with | refl _ => refl _

----------------------------------------------------------------------------------
-- **Part 4b: Addition**
----------------------------------------------------------------------------------

-- *Define Addition*
def add (n m : N) : N :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)
infix:65 (priority := high) " + " => add


-- **show that (N, +) forms a Monoid**

-- hint: substitute the definition of '+'.
theorem left_unit (n : N) : zero + n = n :=
  _

-- hint: you need to match here
theorem right_unit (n : N) : n + zero = n :=
  _

theorem associative (n m k : N) : (n + m) + k = n + (m + k) :=
  _

-- If you are done already, you can try this difficult problem:

theorem commutative (n m : N) : n + m = m + n :=
  _

-- Hint 1: You need to define a helper-theorem to solve this one
-- Hint 2: Write down the proof strategy on a piece of paper first
