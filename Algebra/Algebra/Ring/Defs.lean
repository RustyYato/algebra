notation "ℕ" => Nat
notation "ℤ" => Int

class Zero (α) where
  zero: α
class One (α) where
  one: α

instance Zero.ofNat [Zero α] : OfNat α 0 := ⟨ Zero.zero ⟩
instance One.ofNat [One α] : OfNat α 1 := ⟨ One.one ⟩

variable {a b c k: a₀}

class SMul (M α) where
  smul : M -> α -> α

infixr:73 " • " => SMul.smul

class Inv (α) where
  inv: α -> α

postfix:max "⁻¹" => Inv.inv

variable (α: Type u) [Zero α] [One α] [Add α] [Mul α] [Sub α] [Div α]
variable {α₀: Type u} [Zero α₀] [One α₀] [Add α₀] [Mul α₀] [Sub α₀] [Div α₀]
variable [Pow α ℕ] [Pow α₀ ℕ] [SMul ℕ α] [SMul ℕ α₀]
variable [Pow α ℤ] [Pow α₀ ℤ] [SMul ℤ α] [SMul ℤ α₀]
variable [Neg α] [Neg α₀] [Inv α] [Inv α₀]
variable [NatCast α] [IntCast α] [NatCast α₀] [IntCast α₀] [∀n, OfNat α (n+2)] [∀n, OfNat α₀ (n+2)]

class IsAddSemigroup: Prop where
  add_assoc (a b c: α) : a + b + c = a + (b + c)
class IsSemigroup: Prop where
  mul_assoc (a b c: α) : a * b * c = a * (b * c)

def add_assoc [IsAddSemigroup α₀] (a b c: α₀) : a + b + c = a + (b + c) := IsAddSemigroup.add_assoc a b c
def mul_assoc [IsSemigroup α₀] (a b c: α₀) : a * b * c = a * (b * c) := IsSemigroup.mul_assoc a b c

class IsAddCommMagma: Prop where
  add_comm (a b: α) : a + b = b + a
class IsCommMagma: Prop where
  mul_comm (a b: α) : a * b = b * a

def add_comm [IsAddCommMagma α₀] (a b: α₀) : a + b = b + a := IsAddCommMagma.add_comm a b
def mul_comm [IsCommMagma α₀] (a b: α₀) : a * b = b * a := IsCommMagma.mul_comm a b

class IsAddLeftCancel: Prop where
  add_left_cancel (a b k: α): k + a = k + b -> a = b
class IsAddRightCancel: Prop where
  add_right_cancel (a b k: α): a + k = b + k -> a = b

class IsLeftCancel: Prop where
  mul_left_cancel (a b k: α): k * a = k * b -> a = b
class IsRightCancel: Prop where
  mul_right_cancel (a b k: α): a * k = b * k -> a = b

class IsAddCancel extends IsAddLeftCancel α, IsAddRightCancel α: Prop
class IsMulCancel extends IsLeftCancel α, IsRightCancel α: Prop


instance [IsAddLeftCancel α] [IsAddRightCancel α] : IsAddCancel α where
instance [IsLeftCancel α] [IsRightCancel α] : IsMulCancel α where

def add_left_cancel [IsAddLeftCancel α₀] {a b k: α₀}: k + a = k + b -> a = b := IsAddLeftCancel.add_left_cancel a b k
def add_right_cancel [IsAddRightCancel α₀] {a b k: α₀}: a + k = b + k -> a = b := IsAddRightCancel.add_right_cancel a b k

def mul_left_cancel [IsLeftCancel α₀] {a b k: α₀}: k * a = k * b -> a = b := IsLeftCancel.mul_left_cancel a b k
def mul_right_cancel [IsRightCancel α₀] {a b k: α₀}: a * k = b * k -> a = b := IsRightCancel.mul_right_cancel a b k

instance (priority := 50) IsAddCommMagma.toLeftCancel [IsAddCommMagma α] [IsAddRightCancel α] : IsAddLeftCancel α where
  add_left_cancel a b k := by
    rw [add_comm k, add_comm k]
    exact add_right_cancel

instance (priority := 50) IsAddCommMagma.toRightCancel [IsAddCommMagma α] [IsAddLeftCancel α] : IsAddRightCancel α where
  add_right_cancel a b k := by
    rw [add_comm _ k, add_comm _ k]
    exact add_left_cancel

instance (priority := 50) IsCommMagma.toLeftCancel [IsCommMagma α] [IsRightCancel α] : IsLeftCancel α where
  mul_left_cancel a b k := by
    rw [mul_comm k, mul_comm k]
    exact mul_right_cancel

instance (priority := 50) IsCommMagma.toRightCancel [IsCommMagma α] [IsLeftCancel α] : IsRightCancel α where
  mul_right_cancel a b k := by
    rw [mul_comm _ k, mul_comm _ k]
    exact mul_left_cancel

class IsAddZeroClass: Prop where
  zero_add (a: α): 0 + a = a
  add_zero (a: α): a + 0 = a
class IsMulOneClass: Prop where
  one_mul (a: α): 1 * a = a
  mul_one (a: α): a * 1 = a
class IsMulZeroClass: Prop where
  zero_mul (a: α): 0 * a = 0
  mul_zero (a: α): a * 0 = 0

def zero_add [IsAddZeroClass α₀] (a: α₀) : 0 + a = a := IsAddZeroClass.zero_add a
def add_zero [IsAddZeroClass α₀] (a: α₀) : a + 0 = a := IsAddZeroClass.add_zero a
def one_mul [IsMulOneClass α₀] (a: α₀) : 1 * a = a := IsMulOneClass.one_mul a
def mul_one [IsMulOneClass α₀] (a: α₀) : a * 1 = a := IsMulOneClass.mul_one a
def zero_mul [IsMulZeroClass α₀] (a: α₀) : 0 * a = 0 := IsMulZeroClass.zero_mul a
def mul_zero [IsMulZeroClass α₀] (a: α₀) : a * 0 = 0 := IsMulZeroClass.mul_zero a

def nsmulRec : ℕ -> α₀ -> α₀
| 0, _ => 0
| n + 1, a => nsmulRec n a + a

def npowRec : ℕ -> α₀ -> α₀
| 0, _ => 1
| n + 1, a => npowRec n a * a

class IsAddMonoid extends IsAddSemigroup α, IsAddZeroClass α: Prop where
  nsmul_zero (a: α) : 0 • a = 0 := by rfl
  nsmul_succ (n: ℕ) (a: α) : (n + 1) • a = n • a + a := by rfl
class IsMonoid extends IsSemigroup α, IsMulOneClass α: Prop where
  npow_zero (a: α) : a ^ 0 = 1 := by rfl
  npow_succ (n: ℕ) (a: α) : a ^ (n + 1) = a ^ n * a := by rfl

def nsmul_zero [IsAddMonoid α₀] (a: α₀) : 0 • a = 0 := IsAddMonoid.nsmul_zero a
def nsmul_succ [IsAddMonoid α₀] (n: ℕ) (a: α₀) : (n + 1) • a = n • a + a := IsAddMonoid.nsmul_succ n a
def npow_zero [IsMonoid α₀] (a: α₀) : a ^ 0 = 1 := IsMonoid.npow_zero a
def npow_succ [IsMonoid α₀] (n: ℕ) (a: α₀) : a ^ (n + 1) = a ^ n * a := IsMonoid.npow_succ n a

def nsmul_one [IsAddMonoid α₀] (a: α₀) : 1 • a = a := by rw [nsmul_succ, nsmul_zero, zero_add]
def npow_one [IsMonoid α₀] (a: α₀) : a ^ 1 = a := by rw [npow_succ, npow_zero, one_mul]

def nsmul_eq_nsmulRec [IsAddMonoid α₀] (n: ℕ) (a: α₀) : n • a = nsmulRec n a := by
  induction n with
  | zero => rw [nsmul_zero]; rfl
  | succ n ih => rw [nsmul_succ, ih]; rfl

def npow_eq_npowRec [IsMonoid α₀] (n: ℕ) (a: α₀) : a ^ n = npowRec n a := by
  induction n with
  | zero => rw [npow_zero]; rfl
  | succ n ih => rw [npow_succ, ih]; rfl

def succ_nsmul [IsAddMonoid α₀] (n: ℕ) (a: α₀) : (n + 1) • a = a + n • a := by
  have : IsAddSemigroup α₀ := IsAddMonoid.toIsAddSemigroup
  induction n with
  | zero =>
    rw [nsmul_zero, add_zero, nsmul_succ, nsmul_zero, zero_add]
  | succ n ih => rw [nsmul_succ n, ←add_assoc, ←ih, nsmul_succ (n + 1)]
def succ_npow [IsMonoid α₀] (n: ℕ) (a: α₀) : a ^ (n + 1) = a * a ^ n := by
  have : IsSemigroup α₀ := IsMonoid.toIsSemigroup
  induction n with
  | zero =>
    rw [npow_zero, mul_one, npow_succ, npow_zero, one_mul]
  | succ n ih => rw [npow_succ n, ←mul_assoc, ←ih, npow_succ (n + 1)]

def add_nsmul [IsAddMonoid α₀] (n m: ℕ) (a: α₀) : (n + m) • a = n • a + m • a := by
  have : IsAddSemigroup α₀ := IsAddMonoid.toIsAddSemigroup
  induction m with
  | zero => rw [Nat.add_zero, nsmul_zero, add_zero]
  | succ m ih => rw [Nat.add_succ, nsmul_succ, nsmul_succ, ←add_assoc, ih]
def add_npow [IsMonoid α₀] (n m: ℕ) (a: α₀) : a ^ (n + m) = a ^ n * a ^ m := by
  have : IsSemigroup α₀ := IsMonoid.toIsSemigroup
  induction m with
  | zero => rw [Nat.add_zero, npow_zero, mul_one]
  | succ m ih => rw [Nat.add_succ, npow_succ, npow_succ, ←mul_assoc, ih]

def zsmulRec : ℤ -> α₀ -> α₀
| .ofNat n, a => n • a
| .negSucc n, a => -((n + 1) • a)

def zpowRec : ℤ -> α₀ -> α₀
| .ofNat n, a => a ^ n
| .negSucc n, a => (a ^ (n + 1))⁻¹

class IsInvolutiveNeg: Prop where
  neg_neg (a: α): - -a = a
class IsInvolutiveInv: Prop where
  inv_inv (a: α): a⁻¹⁻¹ = a

def neg_neg [IsInvolutiveNeg α₀] (a: α₀) : - -a = a := IsInvolutiveNeg.neg_neg a
def inv_inv [IsInvolutiveInv α₀] (a: α₀) : a⁻¹⁻¹ = a := IsInvolutiveInv.inv_inv a

def sub' (a b: α₀) : α₀ := a + -b
def div' (a b: α₀) : α₀ := a * b⁻¹

class IsSubNegMonoid extends IsAddMonoid α: Prop where
  sub_eq_add_neg (a b: α) : a - b = a + -b
  zsmul_ofNat (n: ℕ) (a: α) : (n: ℤ) • a = n • a
  zsmul_negSucc (n: ℕ) (a: α) : (Int.negSucc n) • a = -(n.succ • a)

class IsDivInvMonoid extends IsMonoid α: Prop where
  div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
  zpow_ofNat (n: ℕ) (a: α) : a ^ (n: ℤ) = a ^ n
  zpow_negSucc (n: ℕ) (a: α) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹

def sub_eq_add_neg [IsSubNegMonoid α₀] (a b: α₀) : a - b = a + -b := IsSubNegMonoid.sub_eq_add_neg a b
def div_eq_mul_inv [IsDivInvMonoid α₀] (a b: α₀) : a / b = a * b⁻¹ := IsDivInvMonoid.div_eq_mul_inv a b
def zsmul_ofNat [IsSubNegMonoid α₀] (n: ℕ) (a: α₀) : (n: ℤ) • a = n • a := IsSubNegMonoid.zsmul_ofNat n a
def zpow_ofNat [IsDivInvMonoid α₀] (n: ℕ) (a: α₀) : a ^ (n: ℤ) = a ^ n := IsDivInvMonoid.zpow_ofNat n a
def zsmul_negSucc [IsSubNegMonoid α₀] (n: ℕ) (a: α₀) : (Int.negSucc n) • a = -(n.succ • a) := IsSubNegMonoid.zsmul_negSucc n a
def zpow_negSucc [IsDivInvMonoid α₀] (n: ℕ) (a: α₀) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹ := IsDivInvMonoid.zpow_negSucc n a

def zsmul_neg_one [IsSubNegMonoid α₀] (a: α₀) : (-1) • a = -a := by erw [zsmul_negSucc, nsmul_one]
def zpow_neg_one [IsDivInvMonoid α₀] (a: α₀) : a ^ (-1) = a⁻¹ := by erw [zpow_negSucc, npow_one]

class IsNegZeroClass: Prop where
  neg_zero: -(0: α) = 0
class IsInvOneClass: Prop where
  inv_one: (1: α)⁻¹ = 1

def neg_zero [IsNegZeroClass α₀] : -(0: α₀) = 0 := IsNegZeroClass.neg_zero
def inv_one [IsInvOneClass α₀] : (1: α₀)⁻¹ = 1 := IsInvOneClass.inv_one

class IsSubtractionMonoid extends IsSubNegMonoid α, IsInvolutiveNeg α: Prop where
  neg_add_rev (a b: α) : -(a + b) = -b + -a
  neg_eq_of_add_left (a b: α) : a + b = 0 -> -a = b

class IsDivisionMonoid extends IsDivInvMonoid α, IsInvolutiveInv α: Prop where
  inv_mul_rev (a b: α) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  inv_eq_of_mul_left (a b: α) : a * b = 1 -> a⁻¹ = b

def sub_neg_rev [IsSubtractionMonoid α₀] (a b: α₀) : -(a + b) = -b + -a := IsSubtractionMonoid.neg_add_rev a b
def neg_eq_of_add_left [IsSubtractionMonoid α₀] {a b: α₀} : a + b = 0 -> -a = b := IsSubtractionMonoid.neg_eq_of_add_left a b
def neg_eq_of_add_right [IsSubtractionMonoid α₀] {a b: α₀} : a + b = 0 -> a = -b := by
  intro h
  rw [←neg_eq_of_add_left h, neg_neg]
def inv_mul_rev [IsDivisionMonoid α₀] (a b: α₀) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := IsDivisionMonoid.inv_mul_rev a b
def inv_eq_of_mul_left [IsDivisionMonoid α₀] {a b: α₀} : a * b = 1 -> a⁻¹ = b := IsDivisionMonoid.inv_eq_of_mul_left a b
def inv_eq_of_mul_right [IsDivisionMonoid α₀] {a b: α₀} : a * b = 1 -> a = b⁻¹ := by
  intro h
  rw [←inv_eq_of_mul_left h, inv_inv]

class IsAddGroup extends IsSubNegMonoid α: Prop where
  neg_add_cancel (a: α): -a + a = 0
class IsGroup extends IsDivInvMonoid α: Prop where
  inv_mul_cancel (a: α): a⁻¹ * a = 1

def left_neg_eq_right_neg [IsAddGroup α₀] { a b c: α₀ } (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]
def left_inv_eq_right_inv [IsGroup α₀] { a b c: α₀ } (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

def neg_add_cancel [IsAddGroup α₀] (a: α₀): -a + a = 0 := IsAddGroup.neg_add_cancel a
def inv_mul_cancel [IsGroup α₀] (a: α₀): a⁻¹ * a = 1 := IsGroup.inv_mul_cancel a

private theorem neg_eq_of_add [IsAddGroup α₀] { a b: α₀ } (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (neg_add_cancel a) h
private theorem inv_eq_of_mul [IsGroup α₀] { a b: α₀ } (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

instance IsAddGroup.toInvolutNeg [IsAddGroup α] : IsInvolutiveNeg α where
  neg_neg a := neg_eq_of_add (neg_add_cancel a)
instance IsGroup.toInvolutInv [IsGroup α] : IsInvolutiveInv α where
  inv_inv a := inv_eq_of_mul (inv_mul_cancel a)

def add_neg_cancel [IsAddGroup α₀] (a: α₀): a + -a = 0 := by
  conv => { lhs; lhs; rw [←neg_neg a] }
  rw [neg_add_cancel]
def mul_inv_cancel [IsGroup α₀] (a: α₀): a * a⁻¹ = 1 := by
  conv => { lhs; lhs; rw [←inv_inv a] }
  rw [inv_mul_cancel]

class IsLeftDistrib: Prop where
  left_distrib (k a b: α): k * (a + b) = k * a + k * b
class IsRightDistrib: Prop where
  right_distrib (a b k: α): (a + b) * k = a * k + b * k

def mul_add [IsLeftDistrib α] (k a b: α): k * (a + b) = k * a + k * b := IsLeftDistrib.left_distrib k a b
def add_mul [IsRightDistrib α] (a b k: α): (a + b) * k = a * k + b * k := IsRightDistrib.right_distrib a b k

def natCastRec : ℕ -> α
| 0 => 0
| n + 1 => natCastRec n + 1

def intCastRec : ℤ -> α
| .ofNat n => NatCast.natCast n
| .negSucc n => -NatCast.natCast n.succ

abbrev ofNat' α n [o: OfNat α n] := o.ofNat

class IsAddMonoidWithOne extends IsAddMonoid α: Prop where
  natCast_zero : NatCast.natCast 0 = (0: α)
  natCast_succ (n: ℕ) : NatCast.natCast n.succ = NatCast.natCast n + (1: α)
  ofNat_zero : ofNat' α 0 = 0
  ofNat_one : ofNat' α 1 = 1
  ofNat_eq_natCast (n: ℕ): ofNat' α (n + 2) = NatCast.natCast (n + 2)

def natCast_zero [IsAddMonoidWithOne α₀] : NatCast.natCast 0 = (0: α₀) := IsAddMonoidWithOne.natCast_zero
def natCast_succ [IsAddMonoidWithOne α₀] (n: ℕ) : NatCast.natCast n.succ = NatCast.natCast n + (1: α₀) := IsAddMonoidWithOne.natCast_succ n
def ofNat_eq_natCast [IsAddMonoidWithOne α₀] (n: ℕ) : @OfNat.ofNat α₀ (n + 2) _ = NatCast.natCast (n + 2) := IsAddMonoidWithOne.ofNat_eq_natCast n

class IsAddGroupWithOne extends IsAddGroup α, IsAddMonoidWithOne α: Prop where
  intCast_ofNat (n: ℕ) : IntCast.intCast n = (NatCast.natCast n: α)
  intCast_negSucc (n: ℕ) : IntCast.intCast (Int.negSucc n) = -(NatCast.natCast n.succ: α)

def intCast_ofNat [IsAddGroupWithOne α₀] (n: ℕ) : IntCast.intCast n = (NatCast.natCast n: α₀) := IsAddGroupWithOne.intCast_ofNat n
def intCast_negSucc [IsAddGroupWithOne α₀] (n: ℕ) : IntCast.intCast (Int.negSucc n) = -(NatCast.natCast n.succ: α₀) := IsAddGroupWithOne.intCast_negSucc n

class IsSemiring extends
  IsAddCommMagma α, IsAddMonoidWithOne α,
  IsSemigroup α, IsMulZeroClass α, IsMulOneClass α,
  IsLeftDistrib α, IsRightDistrib α : Prop where

instance [IsAddCommMagma α] [IsAddMonoidWithOne α] [IsSemigroup α] [IsMulZeroClass α] [IsMulOneClass α] [IsLeftDistrib α] [IsRightDistrib α] : IsSemiring α where

class IsRing extends IsSemiring α, IsAddGroupWithOne α : Prop where

instance [IsSemiring α] [IsAddGroupWithOne α] : IsRing α where
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel

def add_one_mul [IsMulOneClass α₀] [IsRightDistrib α₀] (a b: α₀) : (a + 1) * b = a * b + b := by rw [add_mul, one_mul]
def mul_add_one [IsMulOneClass α₀] [IsLeftDistrib α₀] (a b: α₀) : a * (b + 1) = a * b + a := by rw [mul_add, mul_one]
def one_add_mul [IsMulOneClass α₀] [IsRightDistrib α₀] (a b: α₀) : (1 + a) * b = b + a * b := by rw [add_mul, one_mul]
def mul_one_add [IsMulOneClass α₀] [IsLeftDistrib α₀] (a b: α₀) : a * (1 + b) = a + a * b := by rw [mul_add, mul_one]

def two_mul [IsAddMonoidWithOne α₀] [IsRightDistrib α₀] [IsMulOneClass α₀] (a: α₀) : 2 * a = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, add_mul, one_mul]
def mul_two [IsAddMonoidWithOne α₀] [IsLeftDistrib α₀] [IsMulOneClass α₀] (a: α₀) : a * 2 = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, mul_add, mul_one]
