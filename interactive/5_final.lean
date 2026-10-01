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

-- A *class* is a structure that Lean looks up for you, inferred from the type alone.
-- In part 1 you wrote 'double' for N. Many types have something deserving of that name.

class Doubling (α : Type) where
  double : α → α

instance : Doubling Nat    where double n := n + n
instance : Doubling String where double s := s ++ s

#eval Doubling.double 7       -- Lean picks the Nat instance ...
#eval Doubling.double "ab"    -- ... and here the String one, from the type alone

-- Square brackets ask for an instance.
def quadruple (α : Type) [Doubling α] (a : α) : α :=
  Doubling.double (Doubling.double a)

#eval quadruple Nat 3
#eval quadruple String "ab"


----------------------------------------------------------------------------------
-- **Part 5e: Groups**
----------------------------------------------------------------------------------

variable {G : Type}  -- We declare G as a Type here, so we don't have to do it everywhere

class Mult (G) where
  mult : G → G → G
infixl:70 (priority := high) " * " => Mult.mult

class AssocMult (G) extends Mult (G) where
  assoc {g h c : G} : (g * h) * c = g * (h * c)

attribute [simp] AssocMult.assoc -- the 'simp' tactic can now prove associativity for us

class Neutral (G) where
  one : G
notation:max "e" => Neutral.one

section LeftGroupOnly  -- keeps the ⁻¹ below from clashing with Group's further down
class LeftGroup (G) extends AssocMult G, Neutral G where
  left_unit {g : G} : e * g = g
  inv     : G → G
  left_inv {g : G} : inv g * g = e
local postfix:max "⁻¹" => LeftGroup.inv

class Group (G) extends AssocMult G, Neutral G where
  left_unit {g : G} : e * g = g
  right_unit {g : G} : g * e = g
  inv     : G → G
  left_inv {g : G} : inv g * g = e
  right_inv {g : G} : g * inv g = e
postfix:max "⁻¹" => Group.inv

-- We show that every left Group is actually already a Group

theorem LG_right_inv [LeftGroup G] {g : G} : g * g⁻¹ = e := by
  calc
  g * g⁻¹ = e * (g * g⁻¹)             := by rw [LeftGroup.left_unit]
  _       = (g⁻¹⁻¹ * g⁻¹) * (g * g⁻¹) := by rw [LeftGroup.left_inv]
  _       = g⁻¹⁻¹ * (g⁻¹ * g) * g⁻¹   := by simp
  _       = g⁻¹⁻¹ * e * g⁻¹           := by rw [LeftGroup.left_inv]
  _       = g⁻¹⁻¹ * (e * g⁻¹)         := by simp
  _       = g⁻¹⁻¹ * g⁻¹               := by rw [LeftGroup.left_unit]
  _       = e                         := by rw [LeftGroup.left_inv]

theorem LG_right_unit [LeftGroup G] {g : G} : g * e = g := by
  calc
  g * e = g * (g⁻¹ * g) := by rw [LeftGroup.left_inv]
  _     = (g * g⁻¹) * g := by simp
  _     = e * g         := by rw [LG_right_inv]
  _     = g             := by rw [LeftGroup.left_unit]

end LeftGroupOnly

-- Every Left-Group is a group!
instance leftGroupIsGroup [LeftGroup G] : Group G where
  left_unit   := LeftGroup.left_unit
  right_unit  := LG_right_unit
  inv         := LeftGroup.inv
  left_inv    := LeftGroup.left_inv
  right_inv   := LG_right_inv

theorem one_unique [Group G] (e' : G) (f : ∀ h : G , e' * h = h) : e' = e := by
  calc
  e' = e' * e := Group.right_unit.symm
  _  = e      := f e

theorem left_cancel [Group G] {g h c : G} (f : c * g = c * h) : g = h := by
  calc
  g = (c⁻¹ * c) * g   := by rw [Group.left_inv, Group.left_unit]
  _ = c⁻¹ * (c * g)   := by simp
  _ = c⁻¹ * (c * h)   := by rw [f]
  _ = (c⁻¹ * c) * h   := by simp
  _ = h               := by rw [Group.left_inv, Group.left_unit]

theorem right_inverse_unique [Group G] (g : G) {g' : G} (h : g * g' = e) : g' = g⁻¹ := by
  rw [← Group.right_inv] at h
  exact (left_cancel h)

theorem double_inverse [Group G] {g : G} : g⁻¹⁻¹ = g := by
  have h : g⁻¹ * g = e := Group.left_inv
  exact (right_inverse_unique (g⁻¹) h).symm

theorem inversion_group_abelian [Group G] (h : (g : G) → g * g = e) : ∀ g h' : G , g * h' = h' * g := by
  intro g h'
  calc
  g * h' = (g * h') * e                     := (Group.right_unit).symm
  _      = (g * h') * ((h' * g) * (h' * g)) := by rw[h]
  _      = g * (h' * h') * g * h' * g       := by simp
  _      = (g * g) * h' * g                 := by rw[h, Group.right_unit]
  _      = h' * g                           := by rw[h, Group.left_unit]


----------------------------------------------------------------------------------
-- **5f: Material, and also my sources**
----------------------------------------------------------------------------------

-- * Lean Game Server: Learn Tactics Playfully -- https://adam.math.hhu.de/
-- * Mathematics in Lean: free standard textbook --  https://leanprover-community.github.io/mathematics_in_lean/
-- * Theorem proving in Lean: free standard textbook --  https://leanprover.github.io/theorem_proving_in_lean4/
-- * Mathlib source code: Read how mathlib works  -- https://leanprover-community.github.io/mathlib-overview.html
