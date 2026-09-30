set_option pp.fieldNotation false -- makes terms easier to read

inductive N where
  | zero : N
  | succ : N → N
open N

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n' => succ (succ (double n'))

----------------------------------------------------------------------------------
-- **Part 2a: Lists**
----------------------------------------------------------------------------------

-- Given a Type T, Lst T returns a Type of Lists over T
inductive Lst : Type → Type                -- Lst is a *function of types*
  | nil {T} : Lst T                        -- 'T' is an *implicit argument*, it is inferred by the compiler
  | cons {T} : T → Lst T → Lst T
open Lst
infixr:20 (priority := high) " ∷ " => cons  -- An infix operator to abbreviate "cons". Made with "\::"

-- Notice: The Lean Compiler can infer the implicit type T!
#check zero ∷ succ zero ∷ nil -- A list of natural numbers
#check (zero ∷ succ zero ∷ nil) ∷ (nil) ∷ nil -- A list of lists

-- *Define a function which concatenates two lists together*
def concatenate {T : Type} (xs : Lst T) (ys : Lst T) : Lst T := -- T is an implicit argument
  match xs with
  | nil => _
  | x ∷ xs' => _

----------------------------------------------------------------------------------
-- **Part 2b: Even Numbers**
----------------------------------------------------------------------------------

-- Even is simular to Lst, but instead of a type, it now *depends on a value instead of a Type*
inductive Even : N -> Type where
  | base : Even zero                              -- zero is an even number
  | next {n : N} : Even n → Even (succ (succ n))  -- if n is even, so is n+2
open Even

-- *Can you supply an element of this Type?*
def zero_even : Even zero :=
  _

-- *Can you supply an element of this Type?*
def two_even : Even (succ (succ zero)) :=
  _

-- *Can you supply a function of this type?*
def double_even (n : N) : Even (double n) :=
  match n with
  | zero => _
  | succ n' => _
-- hint: Substitute the definition of double
