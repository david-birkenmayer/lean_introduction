set_option pp.fieldNotation false


------  Classes:  ------------
------  Monoids and Groups ---

variable {α : Type}

class Mult (α) where
  mult : α -> α -> α
infixl:70 (priority := high) " * " => Mult.mult

class AssocMult (α) extends Mult (α) where
  assoc {a b c : α} : (a * b) * c = a * (b * c)

attribute [simp] AssocMult.assoc

class Neutral (α) where
  one : α
instance [Neutral α] : OfNat α 1 where
  ofNat := Neutral.one

class LeftMonoid (α) extends AssocMult α, Neutral α where
  left_unit {a : α} : 1 * a = a

class LeftGroup (α) extends LeftMonoid α where
  inv     : α -> α
  left_inv {a : α} : inv a * a = 1
postfix:max "⁻¹" => LeftGroup.inv

theorem LG_right_inv [LeftGroup α] {a : α} : a * a⁻¹ = 1 := by
  calc
  a * a⁻¹ = 1 * (a * a⁻¹)             := by rw [LeftMonoid.left_unit]
  _       = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [LeftGroup.left_inv]
  _       = a⁻¹⁻¹ * (a⁻¹ * a) * a⁻¹   := by simp
  _       = a⁻¹⁻¹ * 1 * a⁻¹           := by rw [LeftGroup.left_inv]
  _       = a⁻¹⁻¹ * (1 * a⁻¹)         := by simp
  _       = a⁻¹⁻¹ * a⁻¹               := by rw [LeftMonoid.left_unit]
  _       = 1                         := by rw [LeftGroup.left_inv]

theorem LG_right_unit [LeftGroup α] {a : α} : a * 1 = a := by
  calc
  a * 1 = a * (a⁻¹ * a) := by rw [LeftGroup.left_inv]
  _     = (a * a⁻¹) * a := by simp
  _     = 1 * a         := by rw [LG_right_inv]
  _     = a             := by rw [LeftMonoid.left_unit]


class Monoid (α) extends AssocMult α, Neutral α where
  left_unit {a : α} :  1 * a = a
  right_unit {a : α} :  a * 1 = a

theorem one_unique [Monoid α] (a : α) (f : ∀ (g : α) , a * g = g) : a = 1 := by
  specialize f 1
  rw [Monoid.right_unit] at f
  assumption

class Group (α) extends Monoid α where
  inv     : α -> α
  left_inv {a : α} : inv a * a = 1
  right_inv {a : α} : a * inv a = 1
postfix:max "⁻¹" => Group.inv

-- Every Left-Group is a group!
instance leftGroupIsGroup [LeftGroup α] : Group α where
  mult        := Mult.mult
  assoc       := AssocMult.assoc
  one         := Neutral.one
  left_unit   := LeftMonoid.left_unit
  right_unit  := LG_right_unit
  inv         := LeftGroup.inv
  left_inv    := LeftGroup.left_inv
  right_inv   := LG_right_inv

theorem left_cancel [Group α] {a b g : α} (h : g * a = g * b) : a = b := by
  have h2 : g⁻¹ * (g * a) = g⁻¹ * (g * b) := congrArg (g⁻¹ * ·) h
  have h3 : (g⁻¹ * g) * a = (g⁻¹ * g) * b := by simp[h2]
  have h4 :         1 * a = 1 * b         := by rw [Group.left_inv] at h3; exact h3
  have h5 :             a = b             := by rw [Monoid.left_unit, Monoid.left_unit] at h4; exact h4
  exact h5

theorem left_cancel' [Group α] {a b g : α} (h : g * a = g * b) : a = b := by
  have h := congrArg (g⁻¹ * ·) h
  have h : (g⁻¹ * g) * a = (g⁻¹ * g) * b := by simp[h]
  rw [Group.left_inv] at h
  rw [Monoid.left_unit, Monoid.left_unit] at h
  exact h

theorem left_cancel'' [Group α] {a b g : α} (h : g * a = g * b) : a = b := by
  simpa [← AssocMult.assoc, Group.left_inv, Monoid.left_unit] using congrArg (g⁻¹ * ·) h

theorem left_cancel''' [Group α] {a b g : α} (h : g * a = g * b) : a = b := by
  calc
  a = (g⁻¹ * g) * a   := by rw [Group.left_inv, Monoid.left_unit]
  _ = g⁻¹ * (g * a)   := by simp
  _ = g⁻¹ * (g * b)   := by rw [h]
  _ = (g⁻¹ * g) * b   := by simp
  _ = b               := by rw [Group.left_inv, Monoid.left_unit]

theorem right_cancel [Group α] {a b g : α} (h : a * g = b * g) : a = b := by
  simpa [AssocMult.assoc, Group.right_inv, Monoid.right_unit] using congrArg (· * g⁻¹) h

theorem left_inverse_unique [Group α] (a : α) {a' : α} (h: a' * a = 1) : a' = a⁻¹ := by
  rw [← Group.left_inv (a := a)] at h
  exact (right_cancel h)

theorem right_inverse_unique [Group α] (a : α) {a' : α} (h: a * a' = 1) : a' = a⁻¹ := by
  rw [← Group.right_inv (a := a)] at h
  exact (left_cancel h)

theorem double_inverse [Group α] {a : α} : a⁻¹⁻¹ = a := by
  have h : a * a⁻¹ = 1 := Group.right_inv
  exact (left_inverse_unique (a⁻¹) h).symm

theorem inversion_group_abelian [Group α] (h : (g : α) -> g * g = 1) : ∀ a b : α , a * b = b * a := by
  intro a b
  calc
  a * b = (a * b) * 1                   := (Monoid.right_unit).symm
  _     = (a * b) * ((b * a) * (b * a)) := by rw[h]
  _     = a * (b * b) * a * b * a       := by simp
  _     = (a * a) * b * a               := by rw[h, Monoid.right_unit]
  _     = b * a                         := by rw[h, Monoid.left_unit]
