import Algebra.Int.Mul
import Algebra.Algebra.Ring.Defs

instance : Zero int where
  zero := 0

instance : One int where
  one := 1

instance : SMul ℕ int where
  smul n x := ↑n * x

instance : Pow int ℕ where
  pow x n := npowRec n x

def int.ofStdInt : ℤ -> int
| .ofNat 0 => .zero
| .ofNat (n + 1) => .pos_succ (nat.ofNat n)
| .negSucc n => .neg_succ (nat.ofNat n)

instance : Coe ℤ int where
  coe := int.ofStdInt

instance : SMul ℤ int where
  smul n x := ↑n * x

instance : IsAddSemigroup int where
  add_assoc := int.add.assoc

instance : IsAddCommMagma int where
  add_comm := int.add.comm

instance : IsSemigroup int where
  mul_assoc := int.mul.assoc

instance : IsCommMagma int where
  mul_comm := int.mul.comm

instance : IsSubNegMonoid int where
  zero_add := @int.zero_add
  add_zero := @int.add_zero
  sub_eq_add_neg a b := rfl
  nsmul_zero x := by
    suffices (int.zero * x = 0) from this
    erw [int.mul.zero_left]
  nsmul_succ n x := by
    suffices (int.ofNat n.succ * x = (int.ofNat n * x) + x) from this
    rw [int.ofNat]
    dsimp
    rw [int.pos_succ.def, int.mul.inc_add]
    cases n <;> rfl
  zsmul_ofNat n x := by cases n <;> rfl
  zsmul_negSucc n x := by
    suffices ((int.neg_succ (nat.ofNat n)) * x = -(int.ofNat (n.succ) * x)) from this
    unfold int.ofNat
    dsimp
    rw [int.mul.neg_left, int.neg.pos_succ]

instance : IsAddGroup int where
  neg_add_cancel a := by rw [int.add.comm, int.add.neg_self]

instance : IsSubtractionMonoid int where
  neg_add_rev a b := by rw [int.add.neg, int.add.comm]
  neg_eq_of_add_left a b := by
    intro h
    have := @int.add.compare_right (-a) b a
    rw [int.add.neg_self, h, compare_eq_refl] at this
    exact eq_of_compare_eq this

instance : IsMulOneClass int where
  one_mul := @int.mul.one_left
  mul_one := @int.mul.one_right

instance : IsMulZeroClass int where
  zero_mul := @int.mul.zero_left
  mul_zero := @int.mul.zero_right

instance : IsMonoid int where
  npow_zero _ := rfl
  npow_succ _ _ := rfl
