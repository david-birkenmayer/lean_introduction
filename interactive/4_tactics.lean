set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

----------------------------------------------------------------------------------
-- **Part 3a: Equality**
----------------------------------------------------------------------------------

-- The definition of equality would be out of scope for an introduction.
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
-- **Part 3b: Addition**
----------------------------------------------------------------------------------

-- *Define Addition*
def add (n m : N) : N :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)
infix:65 (priority := high) " + " => add


-- **show that (N, +) forms a Monoid**

-- hint: Substitute the definition of "+"
theorem left_unit (n : N) : zero + n = n :=
  reflexive

theorem right_unit (n : N) : n + zero = n :=
  match n with
  | zero => reflexive
  | succ n' => succ_equal (right_unit n')

theorem associativity (n m k : N) : (n + m) + k = n + (m + k) :=
  match n with
  | zero => reflexive
  | succ n' => succ_equal (associativity n' m k)


-- If you are done already, you can try this difficult problem:

theorem commutative (n m : N) : n + m = m + n :=  -- Hint: You need to define a helper-theorem to solve this one
  match n with
