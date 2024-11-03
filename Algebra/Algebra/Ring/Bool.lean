import Algebra.Int.Mul
import Algebra.Algebra.Ring.Defs

instance : Zero Bool where
  zero := false

instance : One Bool where
  one := true

instance : Add Bool where
  add := xor

instance : Mul Bool where
  mul := (· && ·)

instance : SMul ℕ Bool where
  smul n x := n % 2 != 0 && x

instance : Pow Bool ℕ where
  pow x n := x || n == 0

instance : Coe ℤ Bool where
  coe n := n % 2 != 0

instance : Neg Bool where
  neg := id

instance : Sub Bool where
  sub := Bool.xor

instance : SMul ℤ Bool where
  smul n x := n % 2 != 0 && x

instance : NatCast Bool where
  natCast n := n % 2 != 0

instance : IntCast Bool where
  intCast n := n % 2 != 0

instance : OfNat Bool n where
  ofNat := n % 2 != 0

instance : IsCommMagma Bool where
  mul_comm := by decide

def Nat.mod_two_eq : ∀(n: Nat), n % 2 = 0 ∨ n % 2 = 1
| 0 => .inl rfl
| 1 => .inr rfl
| n + 2 => by
  apply Decidable.byContradiction
  intro h
  cases not_or.mp h with | intro l r =>
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] at l r
  cases mod_two_eq n
  <;> contradiction

instance : IsRing Bool where
  add_assoc := by decide
  mul_assoc := by decide
  add_comm := by decide
  natCast_zero := by decide
  natCast_succ := by
    intro n
    suffices ((n.succ % 2) != 0) = Bool.xor (n % 2 != 0) true from this
    rw [←Nat.add_one, Nat.add_mod]
    cases Nat.mod_two_eq n <;> rename_i h
    rw [h]
    rfl
    rw [h]
    rfl
  ofNat_zero := by decide
  ofNat_one := by decide
  ofNat_eq_natCast := by
    intro n
    rfl
  zero_mul _ := rfl
  mul_zero := by decide
  mul_one := by decide
  one_mul _ := rfl
  zero_add := by decide
  add_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  neg_add_cancel := by decide
  intCast_negSucc x := by
    suffices ((Int.negSucc x) % 2 != 0) = ((x + 1) % 2 != 0) from this
    conv => {
      lhs
      unfold HMod.hMod instHMod Mod.mod Int.instMod
    }
    dsimp
    unfold Int.emod
    dsimp
    rw [Int.subNatNat_of_le]
    rw [Nat.add_mod]
    cases Nat.mod_two_eq x <;> rename_i h
    rw [h]
    rfl
    rw [h]
    rfl
    cases Nat.mod_two_eq x <;> rename_i h
    rw [h]
    decide
    rw [h]
    decide
  intCast_ofNat x := by
    suffices ((↑x: Int) % ↑(2: Nat) != 0) = (x % 2 != 0) from this
    rw [Int.ofNat_mod_ofNat]
    cases Nat.mod_two_eq x <;> rename_i h
    rw [h]
    rfl
    rw [h]
    rfl
  sub_eq_add_neg := by decide
  nsmul_zero := by decide
  nsmul_succ n a := by
    suffices ((n + 1) % 2 != 0 && a) = xor (n % 2 != 0 && a) a from this
    cases a
    rw [Bool.and_false, Bool.and_false]
    rfl
    rw [Bool.and_true, Bool.and_true, Bool.xor_true]
    suffices ((n + 1) % 2 != 0) = (n % 2 == 0) by
      erw [this, Bool.not_not]
    rw [Nat.add_mod]
    cases Nat.mod_two_eq n <;> rename_i h
    rw [h]
    rfl
    rw [h]
    rfl
  zsmul_ofNat n a := by
    suffices ((↑n: Int) % ↑(2: Nat) != 0 && a) = (n % 2 != 0 && a) from this
    rw [Int.ofNat_mod_ofNat]
    cases Nat.mod_two_eq n <;> rename_i h
    rw [h]
    rfl
    rw [h]
    rfl
  zsmul_negSucc n a := by
    suffices (Int.emod (Int.negSucc n) 2 != 0 && a) = ((n + 1) % 2 != 0 && a) from this
    unfold Int.emod
    dsimp
    rw [Int.subNatNat_of_le, Nat.add_mod]
    all_goals
      cases Nat.mod_two_eq n <;> rename_i h
      rw [h]
      trivial
      rw [h]
      trivial
  npow_zero := by decide
  npow_succ n a := by
    suffices (a || (n + 1) == 0) = and (a || n == 0) a from this
    have : (n + 1  == 0) = false := rfl
    rw [this, Bool.or_false, Bool.and_or_distrib_right, Bool.and_self]
    clear this
    cases a
    rw [Bool.false_or, Bool.and_false]
    rw [Bool.true_or]
