set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N : Type where
  | zero : N
  | succ : N → N
open N

----------------------------------------------------------------------------------
-- Part 2: Lists.
-- introducing: Dependent Types and Implicit Arguments
----------------------------------------------------------------------------------

-- The Type hierarchy: Turtles all the way down!
#check N
#check Type
#check Type 1
#check N → Type 2

-- Dependent Typing: A type which depends on another type
inductive Lst (α : Type) : Type
  | nil : Lst α
  | cons (x : α) (xs : Lst α) : Lst α
open Lst
infixr:20 (priority := high) " ∷ " => cons
-- An infix operator to abbreviate "cons". Made with "\::"

#check zero ∷ succ zero ∷ nil -- A list of natural numbers
#check (zero ∷ succ zero ∷ nil) ∷ (nil) ∷ nil -- A list of lists
-- Notice: The Lean Compiler can infer the type α!

-- Define a function which concatenates two lists together
def concatenate {α : Type} (xs : Lst α) (ys : Lst α) : Lst α := -- α is an implicit argument
  match xs with
  | nil => ys
  | x ∷ xs' => x ∷ concatenate xs' ys


-- We can also make types which depend on values!
-- A vector is a list of a fixed size n of type N
inductive Vec (α : Type): N → Type
  | nul : Vec α zero
  | consV {n : N} (x : α) (xV : Vec α n) : Vec α (succ n)
open Vec
infixr:20 (priority := high) " • " => consV
-- An infix operator to abbreviate "consV". Made with "\bu"

#check zero • nul
#check zero • succ zero • zero • nul
