set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

----------------------------------------------------------------------------------
-- Part 5: Groups
-- introducing: Classes
----------------------------------------------------------------------------------

inductive N where
  | zero : N
  | succ : N -> N
open N

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))


-------  Part 2:                -------
-------  Logic and Even Numbers -------

-- A proposition is either True or False
#check Prop

-- True is a type with one element
#check True
#check True.intro

-- False is a type with zero elements
#check False
-- False has no element, the existence of such an element represents a contradiction!

theorem ex_falso {A : Prop} (a : False) : A :=
  nomatch a


-- Negation therefore is defined as
-- ¬ A := A → False
-- That is: We assume that A is true, and derive a contradiction

inductive Even : N -> Prop where
  |  zero_even : Even zero
  |  next_even {n} : Even n -> Even (succ (succ n))
open Even

-- n is an implicit argument, it can be filled in by the compiler

theorem two_is_even : Even (succ (succ zero)) :=
  _

theorem double_is_even (n : N) : Even (double n) :=
  match n with
  | zero => _
  | succ n => _
