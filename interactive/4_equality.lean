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

-- Matching on a proof of 'n = m' is what makes equality useful:
-- 'refl' is the only way such a proof can have been built, so the compiler learns n and m are the same

-- Equality is reflexive
theorem reflexive {A : Type} {a : A} : a = a :=
  refl a

-- Equality is symmetric
theorem symmetric {A : Type} {a b : A} : a = b → b = a :=
  fun h => match h with
  | refl _ => refl _

-- Equality is transitive
theorem transitive {A : Type} {a b c : A} : a = b → b = c → a = c :=
  fun h1 h2 =>
  match h1, h2 with
  | refl _, refl _ => refl _

-- The succ function preserves equality
theorem succ_equal {n m : N} : n = m → succ n = succ m :=
  fun h =>
  match h with
  | refl _ => refl _

----------------------------------------------------------------------------------
-- **Part 4b: Addition**
----------------------------------------------------------------------------------

-- *Define Addition*
def add (n m : N) : N :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)
infix:65 (priority := high) " + " => add  -- this overrides Lean's own '+'


-- **(N, +, zero) is a commutative monoid. Your job is to say that in Lean.**

-- Here is the first of the four statements.
theorem left_unit (n : N) : zero + n = n :=
  _

-- Now write the other three yourself, below.
-- *Write only the statement*, and leave the proof as '_'.

-- 'zero' is also a right unit of '+'
-- theorem right_unit ...

-- '+' is associative
-- theorem associative ...

-- '+' is commutative
-- theorem commutative ...


-- **Done early? Go back and replace each '_' with a proof.**
-- hint 1: 'left_unit' needs no recursion. The others do, so you have to 'match'.
-- hint 2: which argument does '+' recurse on? That is the one to match on.
-- hint 3: substitute the definition of '+' in your head or on a piece of paper, this makes the targer clearer.
-- hint 4: commutativity needs a helper theorem of its own. Write the proof strategy down on paper first.
