set_option pp.fieldNotation false


------  Classes:  ------------
------  Monoids and Groups ---

variable (α : Type)

class Multiplication (α) where
  mul : α -> α -> α
infixl:70 (priority := high) " * " => Multiplication.mul


class Neutral (α) where
  one : α
instance [Neutral α] : OfNat α 1 where
  ofNat := Neutral.one

class LeftMonoid (α) extends Multiplication α, Neutral α where
  mul_assoc : (a b c : α) -> (a * b) * c = a * (b * c)
  one_mul   : (a : α) -> 1 * a = a

class LeftGroup (α) extends LeftMonoid α where
  inv     : α -> α
  inv_mul : (a : α) -> inv a * a = 1
postfix:max "⁻¹" => LeftGroup.inv

class Monoid (α) extends Multiplication α, Neutral α where
  mul_assoc : (a b c : α) -> (a * b) * c = a * (b * c)
  one_mul   : (a : α) -> 1 * a = a
  mul_one   : (a : α) -> a * 1 = a

class Group (α) extends Monoid α where
  inv     : α -> α
  inv_mul : (a : α) -> inv a * a = 1
postfix:max "⁻¹" => Group.inv


-- theorem prod_one [LeftMonoid α] {a b : α} : a * b = a * 1 * b := by

theorem one_unique [Monoid α] (a : α) (f : ∀ (g : α) , a * g = g) : a = 1 := by
  specialize f 1
  rw [Monoid.mul_one] at f
  assumption

theorem cancel [Group α] (a b g : α) (h : g * a = g * b) : a = b :=
  _

theorem mul_inv [LeftGroup α] (a : α) : a * a⁻¹ = 1 := by
  have di : (a⁻¹)⁻¹ * a⁻¹ = 1 :=
    LeftGroup.inv_mul a⁻¹
  rw [← LeftMonoid.one_mul (a * a⁻¹)]
  rw [← di]
