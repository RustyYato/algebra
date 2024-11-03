import Algebra.Algebra.Ring.Nat

instance : Zero ℤ := ⟨0⟩
instance : One ℤ := ⟨1⟩

instance : SMul ℕ ℤ := ⟨(· * ·)⟩
instance : SMul ℤ ℤ := ⟨(· * ·)⟩

def Int.nat_smul (n: Nat) (x: Int) : n • x = n * x := rfl

instance : IsSemiring ℤ where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  natCast_zero := rfl
  natCast_succ n := rfl
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast a := rfl
  mul_assoc := Int.mul_assoc
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  nsmul_zero := Int.zero_mul
  nsmul_succ := by
    intro n a
    rw [Nat.add_one, Int.nat_smul, Int.ofNat_succ, Int.add_mul, Int.one_mul]
    rfl
  npow_zero := Int.pow_zero
  npow_succ n m := by rw [Nat.add_one, Int.pow_succ]

instance : IsRing ℤ where
  sub_eq_add_neg a b := Int.sub_eq_add_neg
  neg_add_cancel := Int.add_left_neg
  zsmul_ofNat a b := rfl
  zsmul_negSucc a b := by cases b <;> rfl
  intCast_ofNat n := rfl
  intCast_negSucc n := rfl

instance : IsAddCommMagma ℕ where
  add_comm := Nat.add_comm
instance : IsCommMagma ℕ where
  mul_comm := Nat.mul_comm

variable (M: Type*) [Zero M] [Add M] [Sub M] [SMul ℕ M] [SMul ℤ M] [Neg M]
variable [SMul R M]

instance IsAddCommGroup.toIntModule [IsAddGroup M] [IsAddCommMagma M] : IsModule ℤ M where
  one_smul := one_zsmul
  mul_smul _ _ _ := mul_zsmul _ _ _
  smul_add _ _ _ := zsmul_add _ _ _
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul _ _ _ := add_zsmul _ _ _
