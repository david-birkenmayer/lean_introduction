-- Natural numbers --

set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

-- Every term has a type. Put your cursor on a #check line and look at the Infoview.
-- (Parentheses make #check show the type of a term instead of a definition's signature.)
#check (zero)
#check (succ)
#check succ (succ zero)
#check N


-- Functions are defined by pattern matching and recursion
-- Exercise: define double

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))

-- #reduce evaluates a term
#reduce double (succ (succ zero))


-- Functions are values: they can be passed to other functions
-- Exercise: define twice, which applies f two times to n

def twice (f : N -> N) (n : N) : N :=
  f (f n)

-- Currying: guess the types first, then check!
#check (twice)
#check twice double
#reduce twice double (succ zero)
#reduce twice succ zero
#reduce twice (fun n => double (succ n)) zero   -- fun defines an anonymous function
#reduce twice (twice double) (succ zero)
-- #check twice twice                       -- Uncomment this line: why does it fail?


-- Even numbers --

inductive Even : N -> Prop where
  |  zero_even : Even zero
  |  next_even {n} : Even n -> Even (succ (succ n))
open Even

theorem two_is_even : Even (succ (succ zero)) :=
  _

theorem double_is_even (n : N) : Even (double n) :=
  match n with
  | zero => _
  | succ n => _
