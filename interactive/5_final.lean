import Mathlib.Order.MinMax  -- from here on we use Lean's library, not our own definitions

----------------------------------------------------------------------------------
-- **5a: Tactics**
----------------------------------------------------------------------------------

-- In the previous parts you proved in *term mode*.
-- *tactic mode* is another way of proving in Lean, using powerful *tactics*. You enter tactic mode with 'by'.
-- Here is the proof of commutativity using Lean's own '+' and '=' in tactic mode

theorem add_comm' (n m : Nat) : n + m = m + n := by
  induction n with
  | zero      => simp
  | succ k ih => rw [Nat.succ_add, ih, Nat.add_succ]

-- Tactics are not a different kind of proof, they are keywords which allow the computer to do work for you.
-- Here you see the actual term-based equivalent of what these tactics do
#print add_comm'
-- ... which you would not want to write by hand. That is what tactics are for.

-- In practice you would not need to prove commutativity. It is already in the library:
#check Nat.add_comm

----------------------------------------------------------------------------------
-- **5b: Universes**  -- Types all the way up!
----------------------------------------------------------------------------------

#check Nat
#check Type
#check Type 1
#check Type 20

-- We can make functions that work for any Type by using universes
universe u

def identity {A : Type u} : A → A :=
  fun a => a

#check identity

#check Eq  -- The lean-defined equality is defined for all universes

----------------------------------------------------------------------------------
-- **5c: Structures** -- an inductive type with exactly one constructor
----------------------------------------------------------------------------------

-- 'And' in part 3 had a single constructor carrying several things.
-- That pattern is so common that Lean gives you a keyword to build such a type.
structure Interval where  -- A structure with 3 fields
  lo    : Nat
  hi    : Nat
  sound : lo ≤ hi     -- a structure may bundle data and proofs about that data

#print Interval

def unitInterval' : Interval := Interval.mk 0 1 (by simp) -- old way
def unitInterval : Interval := { lo := 0, hi := 1, sound := by simp } -- structure notation

-- A structure builds projection maps, convenient to use
#check Interval.lo
#check unitInterval.sound

----------------------------------------------------------------------------------
-- **5d: Classes** -- a structure that Lean fills in for you
----------------------------------------------------------------------------------

-- To speak about "the smallest" we will need an order. We do not want to pass it
-- by hand every time, so we declare such things as a *class* and Lean supplies
-- them silently.
class HasDefault (α : Type) where
  default : α

instance : HasDefault Nat where default := 0
instance : HasDefault Bool where default := false

#eval (HasDefault.default : Nat)    -- Lean picks the Nat instance ...
#eval (HasDefault.default : Bool)   -- ... and here the Bool one, from the type alone

-- Square brackets ask for an instance. Compare with part 2's {implicit} arguments:
-- {x} is inferred from the other arguments, [x] is looked up in a table.
def twiceDefault (α : Type) [HasDefault α] : α × α :=
  (HasDefault.default, HasDefault.default)

#eval twiceDefault Nat

----------------------------------------------------------------------------------
-- **5e: A verified optimiser**
----------------------------------------------------------------------------------

-- The SPECIFICATION, as a structure. Read it as mathematics: "m is a minimum of l".
structure IsMinOf [LE α] (m : α) (l : List α) : Prop where
  mem    : m ∈ l
  le_all : ∀ x ∈ l, m ≤ x

-- The ALGORITHM. It walks along the list carrying the best value seen so far,
-- so 'smallest best l' returns the smallest entry of the nonempty list best :: l.
def smallest [LinearOrder α] : α → List α → α
  | best, []      => best
  | best, x :: xs => smallest (min best x) xs

#eval smallest 7 [3, 9, 2, 8]   -- smallest of 7, 3, 9, 2, 8
#eval smallest 1 [3, 9, 2, 8]   -- the starting value can win
#eval smallest 7 []             -- a one-element list

-- The PROOF that the algorithm meets the specification.
theorem smallest_le [LinearOrder α] (a : α) (l : List α) : smallest a l ≤ a := by
  induction l generalizing a with
  | nil => simp [smallest]
  | cons x xs ih => exact le_trans (ih (min a x)) (min_le_left a x)

theorem smallest_le_of_mem [LinearOrder α] (a : α) (l : List α) :
    ∀ x ∈ l, smallest a l ≤ x := by
  induction l generalizing a with
  | nil => simp
  | cons y ys ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_trans (smallest_le (min a x) ys) (min_le_right a x)
    · exact ih (min a y) x h

theorem smallest_mem [LinearOrder α] (a : α) (l : List α) : smallest a l ∈ a :: l := by
  induction l generalizing a with
  | nil => simp [smallest]
  | cons x xs ih =>

    simp only [smallest]
    rcases List.mem_cons.mp (ih (min a x)) with h | h
    · rw [h]
      rcases le_total a x with hax | hax
      · simp [min_eq_left hax]
      · simp [min_eq_right hax]
    · simp [h]

-- Put together: for any type with an order, on any list, the answer is correct.
theorem smallest_spec [LinearOrder α] (a : α) (l : List α) :
    IsMinOf (smallest a l) (a :: l) where
  mem    := smallest_mem a l
  le_all := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact smallest_le x l
    · exact smallest_le_of_mem a l x h

-- This is the thing to take away: the program and the proof that it is correct
-- live in one language, and the compiler checks both at once.

----------------------------------------------------------------------------------
-- **5f: Material**
----------------------------------------------------------------------------------

-- * Lean Game Server: Learn Tactics Playfully -- https://adam.math.hhu.de/
-- * Mathematics in Lean: free standard textbook --  https://leanprover-community.github.io/mathematics_in_lean/
-- * Theorem proving in Lean: free standard textbook --  https://leanprover.github.io/theorem_proving_in_lean4/
-- * Mathlib source code: Read how mathlib works  -- https://leanprover-community.github.io/mathlib-overview.html
