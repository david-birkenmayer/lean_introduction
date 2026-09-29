set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))


----------------------------------------------------------------------------------
-- Part 3: **Even Numbers.**
-- introducing: **Propositions and Logic**
----------------------------------------------------------------------------------


-- The Proposition type "Prop"
-- A proposition is either True or False:
#check True -- True is a type with one element
#check False -- False is a type with zero elements

-- "Is n even?" is a proposition.
inductive Even : N -> Prop where
  | zero_even : Even zero                                  -- zero is an even number
  | next_even {n : N} (p : Even n) : Even (succ (succ n))  -- if n is even, so is n+2
open Even

-- By definition of Prop: *Even n is True if and only if it contains an element*
-- An element p of Even n can be interpreted as "evidence" that n is even.

-- Show that two is even.
theorem two_is_even : Even (succ (succ zero)) := -- "theorem" is mechanically the same as "def"
  _

-- Show that any doubled number is even
theorem double_is_even (n : N) : Even (double n) :=
  match n with
  | zero => _
  | succ n' => _
