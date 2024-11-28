import Algebra.Fintype.Prod

inductive Axis where | x | y | z
deriving DecidableEq

structure Orient where
  sign: Bool
  axis: Axis
deriving DecidableEq

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
