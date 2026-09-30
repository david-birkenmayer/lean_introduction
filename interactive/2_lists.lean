set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N : Type where
  | zero : N
  | succ : N → N
open N

----------------------------------------------------------------------------------
-- Part 2: Lists.
-- introducing: Dependent Types and Implicit Arguments
----------------------------------------------------------------------------------

-- List is a _function of types_
inductive Lst : Type → Type
  | nil {α} : Lst α
  | cons {α} (x : α) (xs : Lst α) : Lst α
open Lst
infixr:20 (priority := high) " ∷ " => cons  -- An infix operator to abbreviate "cons". Made with "\::"

-- Notice: The Lean Compiler can infer the implicit type α!
#check zero ∷ succ zero ∷ nil -- A list of natural numbers
#check (zero ∷ succ zero ∷ nil) ∷ (nil) ∷ nil -- A list of lists


-- Define a function which concatenates two lists together
def concatenate {α : Type} (xs : Lst α) (ys : Lst α) : Lst α := -- α is an implicit argument
  match xs with
  | nil => ys
  | x ∷ xs' => x ∷ concatenate xs' ys


-- We can also make types which depend on values!
inductive Vec : Type → N → Type
  | nilV {α} : Vec α zero
  | consV {α} {n : N} (x : α) (xV : Vec α n) : Vec α (succ n)
open Vec
infixr:20 (priority := high) " • " => consV
-- An infix operator to abbreviate "consV". Made with "\bu"

#check zero • nilV
#check zero • succ zero • zero • nilV
