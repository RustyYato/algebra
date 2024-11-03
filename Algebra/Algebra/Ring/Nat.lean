import Algebra.Algebra.Ring.Defs

instance : Zero ℕ := ⟨0⟩
instance : One ℕ := ⟨1⟩

instance : SMul ℕ ℕ := ⟨(· * ·)⟩

instance : IsSemiring ℕ where
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  natCast_zero := rfl
  natCast_succ n := rfl
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast a := rfl
  mul_assoc := Nat.mul_assoc
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  left_distrib := Nat.mul_add
  right_distrib := Nat.add_mul
  nsmul_zero := Nat.zero_mul
  nsmul_succ := Nat.succ_mul
  npow_zero := Nat.pow_zero
  npow_succ n m := by rw [Nat.add_one, Nat.pow_succ]

instance : IsAddCommMagma ℕ where
  add_comm := Nat.add_comm
instance : IsCommMagma ℕ where
  mul_comm := Nat.mul_comm

variable (M: Type*) [Zero M] [Add M] [Sub M] [SMul ℕ M] [SMul ℤ M] [Neg M]
variable [SMul R M]

instance IsAddCommGroup.toNatModule [IsAddGroup M] [IsAddCommMagma M] : IsModule ℕ M where
  one_smul := one_nsmul
  mul_smul _ _ _ := mul_nsmul _ _ _
  smul_add _ _ _ := nsmul_add _ _ _
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul _ _ _ := add_nsmul _ _ _
