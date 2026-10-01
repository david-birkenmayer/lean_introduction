set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

----------------------------------------------------------------------------------
-- **Part 4a: Equality**
----------------------------------------------------------------------------------

-- The precise definition of equality is out of scope for an introduction.
-- However, assume the following properties as given:

-- Equality is reflexive
theorem reflexive {n : N} : n = n :=
  rfl

-- Equality is symmetric
theorem symmetric {n m : N} : n = m → m = n :=
  Eq.symm

-- Equality is transitive
theorem transitive {n m k : N} : n = m → m = k → n = k :=
  Eq.trans

-- The succ function preserves equality
theorem succ_equal {n m} : n = m → succ n = succ m :=
  congrArg succ

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
