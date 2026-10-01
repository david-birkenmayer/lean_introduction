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
inductive Lst (T : Type) : Type
  | nil : Lst T                            -- in the constructors T is *implicit*: the compiler infers it
  | cons : T → Lst T → Lst T
open Lst
infixr:20 (priority := high) " ∷ " => cons  -- An infix operator to abbreviate "cons". Made with "\::"

#check (Lst)  -- Lst is a function of types
-- T is a parameter: it is fixed for the whole type. Hence we call Lst a *parametric Type*

-- Notice: The Lean Compiler can infer the implicit type T!
#check zero ∷ succ zero ∷ nil -- A list of natural numbers
#check (zero ∷ succ zero ∷ nil) ∷ (nil) ∷ nil -- A list of lists

-- *Define a function which concatenates two lists together*
def concatenate {T : Type} (xs : Lst T) (ys : Lst T) : Lst T := -- T is given as an implicit argument
  match xs with
  | nil => _
  | x ∷ xs' => _

#reduce concatenate (succ (succ zero) ∷ succ zero ∷ nil) (zero ∷ succ zero ∷ nil)

----------------------------------------------------------------------------------
-- **Part 2b: Even Numbers**
----------------------------------------------------------------------------------

-- Given a natural number n, Even n returns a type which contains an element if and only if n is even
inductive Even : N → Type where
  | base : Even zero                              -- zero is an even number
  | next {n : N} : Even n → Even (succ (succ n))  -- if n is even, so is n+2
open Even

#check (Even)  -- Even also is a function of types
-- However, in contrast to Lst, n changes between the constructors!
-- Even is a proper *dependent Type*

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

#reduce double_even (succ (succ zero))
