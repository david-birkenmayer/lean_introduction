set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))


-------  Part 2:      -------
-------  Even Numbers -------


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
