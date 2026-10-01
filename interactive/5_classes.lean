set_option pp.fieldNotation false

----------------------------------------------------------------------------------
-- **Part 5: Groups**
----------------------------------------------------------------------------------

variable {G : Type}  -- We declare G as a Type here, so we don't have to do it everywhere

class Mult (G) where
  mult : G -> G -> G
infixl:70 (priority := high) " * " => Mult.mult

class AssocMult (G) extends Mult (G) where
  assoc {g h c : G} : (g * h) * c = g * (h * c)

attribute [simp] AssocMult.assoc -- the 'simp' tactic can now prove associativity for us

class Neutral (G) where
  one : G
notation:max "e" => Neutral.one

class LeftGroup (G) extends AssocMult G, Neutral G where
  left_unit {g : G} : e * g = g
  inv     : G -> G
  left_inv {g : G} : inv g * g = e
postfix:max "⁻¹" => LeftGroup.inv

class Group (G) extends AssocMult G, Neutral G where
  left_unit {g : G} : e * g = g
  right_unit {g : G} : g * e = g
  inv     : G -> G
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

theorem inversion_group_abelian [Group G] (h : (g : G) -> g * g = e) : ∀ g h' : G , g * h' = h' * g := by
  intro g h'
  calc
  g * h' = (g * h') * e                     := (Group.right_unit).symm
  _      = (g * h') * ((h' * g) * (h' * g)) := by rw[h]
  _      = g * (h' * h') * g * h' * g       := by simp
  _      = (g * g) * h' * g                 := by rw[h, Group.right_unit]
  _      = h' * g                           := by rw[h, Group.left_unit]
