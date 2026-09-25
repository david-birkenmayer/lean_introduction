set_option pp.fieldNotation false


------  Classes:  ------------
------  Monoids and Groups ---


-- A class is a structure for which Lean searches the argument itself.
-- Careful: Lean's core library already defines "Mul", "One" and "Inv",
-- so we pick our own names here and rebuild everything from scratch.


-- A multiplication --

class Multiplication (α : Type) where
  mul : α -> α -> α

-- The notation is declared once, for the class.
-- Everything that has a Multiplication instance may use it -- also every class
-- which extends Multiplication later on.
-- "priority := high" makes our notation win against the "*" of the core library,
-- which would otherwise make every "1 * a" ambiguous. The price is that
-- Lean's own multiplication on Nat is no longer reachable in this file.
infixl:70 (priority := high) " * " => Multiplication.mul


-- A neutral element --

class Neutral (α : Type) where
  one : α

-- "1" is not a notation, but a numeral: Lean reads "1" as "OfNat.ofNat 1".
-- So we do not declare a notation, we give Lean an instance which tells it
-- how to read the numeral 1 in a type with a neutral element.
instance [Neutral α] : OfNat α 1 where
  ofNat := Neutral.one


-- Monoids --

-- "extends" means: a Monoid *contains* a Multiplication and a Neutral.
-- Lean generates the instances Monoid.toMultiplication and Monoid.toNeutral,
-- which is why we may already write "*" and "1" in the axioms below.
class Monoid (α : Type) extends Multiplication α, Neutral α where
  mul_assoc : (a b c : α) -> (a * b) * c = a * (b * c)
  one_mul   : (a : α) -> 1 * a = a
  mul_one   : (a : α) -> a * 1 = a


-- Groups --

class Group (α : Type) extends Monoid α where
  inv     : α -> α
  inv_mul : (a : α) -> inv a * a = 1

postfix:max "⁻¹" => Group.inv


-- Everything above is available in every context which assumes [Monoid α],
-- without mentioning Multiplication or Neutral:

theorem one_is_neutral [Monoid α] (a : α) : 1 * a = a * 1 :=
  Eq.trans (Monoid.one_mul a) (Eq.symm (Monoid.mul_one a))


-- An example: the functions α -> α form a monoid under composition --

instance : Multiplication (α -> α) where
  mul f g := fun x => f (g x)

instance : Neutral (α -> α) where
  one := fun x => x

-- Composition is associative and the identity is neutral -- by rfl!
instance : Monoid (α -> α) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

-- Guess the result without looking!
#reduce (1 : Nat -> Nat) 7
#reduce ((fun n => n + n) * (fun n => n + 1) : Nat -> Nat) 3
#check (Monoid.mul_assoc : (f g h : Nat -> Nat) -> _)
