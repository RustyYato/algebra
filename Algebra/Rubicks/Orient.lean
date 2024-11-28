import Algebra.Fintype.Prod
import Algebra.Order.Lex
import Algebra.Nat.Cmp

inductive Axis where | x | y | z
deriving DecidableEq, Repr

structure Orient where
  sign: Bool
  axis: Axis
deriving DecidableEq, Repr

instance : Fintype Axis where
  all := [.x, .y, .z]
  all_nodups := by decide
  all_spec := by intro a; cases a <;> decide

instance Orient.IsoBoolProdAxis : Ty.EmbedIso Orient (Bool × Axis) where
  fwd a := ⟨a.sign,a.axis⟩
  rev a := ⟨a.1,a.2⟩
  fwd_rev _ := rfl
  rev_fwd _ := rfl

instance : Fintype Orient := Fintype.of_equiv Orient.IsoBoolProdAxis.symm

def Axis.isAdjacent : Axis -> Axis -> Prop := (· ≠ ·)

instance : Decidable (Axis.isAdjacent a b) := inferInstanceAs (Decidable (a ≠ b))

def Axis.isAdjacent.symm : isAdjacent a b -> isAdjacent b a := Ne.symm

def Orient.isAdjacent : Orient -> Orient -> Prop := (·.axis ≠ ·.axis)
def Orient.isAdjacent.symm : isAdjacent a b -> isAdjacent b a := Ne.symm
instance : Decidable (Orient.isAdjacent a b) := inferInstanceAs (Decidable (_ ≠ _))

def Axis.card [f: Fintype Axis] : f.card = 3 := by
  rw [Fintype.card_eq _ instFintypeAxis]
  rfl
def Orient.card [f: Fintype Orient] : f.card = 6 := by
  rw [Fintype.card_eq _ instFintypeOrient]
  rfl

def Axis.rotate : Axis -> Axis
| .x => .y
| .y => .z
| .z => .x

def Axis.rotate_ne : ∀a: Axis, a.rotate ≠ a := by decide
def Axis.rotate.inj : Function.Injective rotate := by
  unfold Function.Injective
  decide

def Axis.other : Axis -> Axis -> Axis
| .x, .x => .x
| .y, .y => .y
| .z, .z => .z
| .x, .y => .z
| .y, .x => .z
| .x, .z => .y
| .z, .x => .y
| .y, .z => .x
| .z, .y => .x

def Axis.other.comm : Axis.other a b = Axis.other b a := by decide +revert
def Axis.other.eq_left : Axis.other (Axis.other a b) b = a := by decide +revert
def Axis.other.eq_right : Axis.other (Axis.other a b) a = b := by decide +revert
def Axis.other.eq_left_iff : Axis.other a b = a ↔ a = b := by decide +revert
def Axis.other.eq_right_iff : Axis.other a b = b ↔ a = b := by decide +revert
def Axis.other.eq_iff : a ≠ b -> (Axis.other a b = c ↔ a ≠ c ∧ b ≠ c) := by decide +revert
def Axis.other.eq : a ≠ b -> a ≠ c -> b ≠ c -> Axis.other a b = c := by decide +revert
def Axis.other.ne_iff : a ≠ b -> (Axis.other a b ≠ c ↔ a = c ∨ b = c) := by decide +revert
def Axis.other.ne_left : a ≠ b -> Axis.other a b ≠ a := by decide +revert
def Axis.other.ne_right : a ≠ b -> Axis.other a b ≠ b := by decide +revert
def Axis.other.inj_left : Function.Injective (Axis.other a ·) := by
  unfold Function.Injective
  decide +revert
def Axis.other.inj_right : Function.Injective (Axis.other · a) := by
  unfold Function.Injective
  decide +revert

def Axis.to_nat : Axis -> nat
| .x => 0
| .y => 1
| .z => 2

def Axis.to_nat.inj : Function.Injective Axis.to_nat := by
  unfold Function.Injective
  decide +revert

instance : LT Axis where
  lt a b := a.to_nat < b.to_nat
instance : LE Axis where
  le a b := a.to_nat ≤ b.to_nat

instance : @DecidableRel Axis (· ≤ ·) := fun a b => decidable_of_iff (a.to_nat ≤ b.to_nat) (Iff.refl _)

instance : Min Axis := minOfLe
instance : Max Axis := maxOfLe

instance : IsLinearOrder Axis := by
  apply IsLinearOrder.transfer nat Axis
  exact Axis.to_nat.inj
  intros; apply Iff.refl
  intros; apply Iff.refl
  decide
  decide
instance : IsDecidableLinearOrder Axis where

instance : LT Orient where
  lt a b := Prod.Lex (· < ·) (· < ·) ⟨a.sign, a.axis⟩  ⟨b.sign, b.axis⟩
instance : LE Orient where
  le a b := a < b ∨ a = b

instance : @DecidableRel Orient (· < ·) := by
  intro a b
  dsimp
  apply Prod.Lex.instDecidableRelOfDecidableEq
instance : @DecidableRel Orient (· ≤ ·) := by
  intro a b
  show Decidable (_ ∨ _)
  exact inferInstance

instance : Min Orient := minOfLe
instance : Max Orient := maxOfLe

instance : IsLinearOrder Orient := by
  apply IsLinearOrder.transfer (Bool × Axis) Orient (f := fun a =>⟨ a.sign, a.axis ⟩)
  unfold Function.Injective
  all_goals decide

instance : IsDecidableLinearOrder Orient where

namespace Orient
abbrev R := Orient.mk true .x
abbrev U := Orient.mk true .y
abbrev F := Orient.mk true .z
abbrev L := Orient.mk false .x
abbrev D := Orient.mk false .y
abbrev B := Orient.mk false .z

abbrev Red := Orient.mk true .x
abbrev White := Orient.mk true .y
abbrev Green := Orient.mk true .z
abbrev Orange := Orient.mk false .x
abbrev Yellow := Orient.mk false .y
abbrev Blue := Orient.mk false .z
end Orient

@[simp]
instance : Neg Orient where
  neg a := ⟨!a.sign, a.axis⟩

def Orient.neg.sign (a: Orient) : (-a).sign = !a.sign := rfl
def Orient.neg.axis (a: Orient) : (-a).axis = a.axis := rfl

def Orient.cross (a b: Orient) : Orient where
  sign := (a.axis.rotate = b.axis) ↔ (a.sign = b.sign)
  axis := a.axis.other b.axis

instance : Mul Orient where
  mul := Orient.cross

def Orient.mul.sign (a b: Orient) : (a * b).sign = true ↔ ((a.axis.rotate = b.axis) ↔ (a.sign = b.sign)) := by decide +revert
def Orient.mul.axis (a b: Orient) : (a * b).axis = a.axis.other b.axis :=by rfl
def Orient.mul.neg_left (a b: Orient) : (-a) * b = -(a * b) := by decide +revert
def Orient.mul.neg_right (a b: Orient) : a * (-b) = -(a * b) := by decide +revert
def Orient.mul.acomm (a b: Orient) : a.isAdjacent b -> a * b = -(b * a) := by decide +revert
def Orient.isAdjacent.mul_left (a b: Orient) : a.isAdjacent b -> (a * b).isAdjacent a := by decide +revert
def Orient.isAdjacent.mul_right (a b: Orient) : a.isAdjacent b -> (a * b).isAdjacent b := by decide +revert

def Orient.mul.left_inj (a: Orient) : Function.Injective (a * ·) := by
  unfold Function.Injective
  decide +revert
def Orient.mul.right_inj (a: Orient) : Function.Injective (· * a) := by
  unfold Function.Injective
  decide +revert

def Orient.mul.mul_left (a b: Orient) : (a * b) * a = b := by decide +revert
def Orient.mul.mul_right (a b: Orient) : b * (a * b) = a := by decide +revert
def Orient.mul.mul_left' (a b: Orient) (h: a.isAdjacent b) : a * (a * b) = -b := by decide +revert
def Orient.mul.mul_right' (a b: Orient) (h: a.isAdjacent b) : (a * b) * b = -a := by decide +revert

def Orient.rotate (a b: Orient) : Orient := if a.axis = b.axis then a else b * a
def Orient.rotate_of_eq (h: a.axis = b.axis) : Orient.rotate a b = a := by decide +revert
def Orient.rotate_of_ne (h: a.axis ≠ b.axis) : Orient.rotate a b = b * a := by decide +revert
def Orient.rotate.neg_left : Orient.rotate (-a) b = -Orient.rotate a b := by decide +revert
def Orient.rotate.inj : Function.Injective (Orient.rotate · r) := by
  unfold Function.Injective
  decide +revert
def Orient.rotate.isAdjacent_iff : ∀{a b r: Orient}, a.isAdjacent b ↔ (a.rotate r).isAdjacent (b.rotate r) := by decide +revert
def Orient.isAdjacent.rotate : ∀{a b r: Orient}, a.isAdjacent b -> (a.rotate r).isAdjacent (b.rotate r) := Orient.rotate.isAdjacent_iff.mp
def Orient.isAdjacent₃ (a b c: Orient) := a.isAdjacent b ∧ c = a * b
