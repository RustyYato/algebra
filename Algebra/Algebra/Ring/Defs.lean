import Algebra.Ty.Notation
import Algebra.StdInt.Induction
import Algebra.AxiomBlame

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

variable (α: Type*) [Zero α] [One α] [Add α] [Mul α] [Sub α] [Div α]
variable {α₀ α₁: Type*} [Zero α₀] [One α₁] [Add α₀] [Mul α₁] [Sub α₀] [Div α₁]
variable [Pow α ℕ] [Pow α₁ ℕ] [SMul ℕ α] [SMul ℕ α₀]
variable [Pow α ℤ] [Pow α₁ ℤ] [SMul ℤ α] [SMul ℤ α₀]
variable [Neg α] [Neg α₀] [Inv α] [Inv α₁]
variable [NatCast α] [IntCast α] [∀n, OfNat α (n+2)]

variable {R₀: Type*} [Zero R₀] [One R₀] [Add R₀] [Mul R₀] [Sub R₀] [Div R₀]
variable [Pow R₀ ℕ] [SMul ℕ R₀]
variable [Pow R₀ ℤ] [SMul ℤ R₀]
variable [Neg R₀] [Inv R₀]
variable [NatCast R₀] [IntCast R₀] [∀n, OfNat R₀ (n+2)]

variable {M₀: Type*} [Zero M₀] [Add M₀] [Sub M₀] [SMul ℕ M₀] [SMul ℤ M₀] [Neg M₀]
variable [SMul R₀ M₀]

variable (R: Type*) [Zero R] [One R] [Add R] [Mul R] [Sub R] [Div R]
variable [Pow R ℕ] [SMul ℕ R]
variable [Pow R ℤ] [SMul ℤ R]
variable [Neg R] [Inv R]
variable [NatCast R] [IntCast R] [∀n, OfNat R (n+2)]

variable (M: Type*) [Zero M] [Add M] [Sub M] [SMul ℕ M] [SMul ℤ M] [Neg M]
variable [SMul R M]

class IsAddSemigroup: Prop where
  add_assoc (a b c: α) : a + b + c = a + (b + c)
class IsSemigroup: Prop where
  mul_assoc (a b c: α) : a * b * c = a * (b * c)

def add_assoc [IsAddSemigroup α₀] (a b c: α₀) : a + b + c = a + (b + c) := IsAddSemigroup.add_assoc a b c
def mul_assoc [IsSemigroup α₁] (a b c: α₁) : a * b * c = a * (b * c) := IsSemigroup.mul_assoc a b c

class IsAddCommMagma: Prop where
  add_comm (a b: α) : a + b = b + a
class IsCommMagma: Prop where
  mul_comm (a b: α) : a * b = b * a

def add_comm [IsAddCommMagma α₀] (a b: α₀) : a + b = b + a := IsAddCommMagma.add_comm a b
def mul_comm [IsCommMagma α₁] (a b: α₁) : a * b = b * a := IsCommMagma.mul_comm a b

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

def mul_left_cancel [IsLeftCancel α₁] {a b k: α₁}: k * a = k * b -> a = b := IsLeftCancel.mul_left_cancel a b k
def mul_right_cancel [IsRightCancel α₁] {a b k: α₁}: a * k = b * k -> a = b := IsRightCancel.mul_right_cancel a b k

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
def one_mul [IsMulOneClass α₁] (a: α₁) : 1 * a = a := IsMulOneClass.one_mul a
def mul_one [IsMulOneClass α₁] (a: α₁) : a * 1 = a := IsMulOneClass.mul_one a
def zero_mul [Zero α₁] [IsMulZeroClass α₁] (a: α₁) : 0 * a = 0 := IsMulZeroClass.zero_mul a
def mul_zero [Zero α₁] [IsMulZeroClass α₁] (a: α₁) : a * 0 = 0 := IsMulZeroClass.mul_zero a

def nsmulRec : ℕ -> α₀ -> α₀
| 0, _ => 0
| n + 1, a => nsmulRec n a + a

def npowRec : ℕ -> α₁ -> α₁
| 0, _ => 1
| n + 1, a => npowRec n a * a

class IsAddMonoid extends IsAddSemigroup α, IsAddZeroClass α: Prop where
  nsmul_zero (a: α) : 0 • a = 0 := by intros; rfl
  nsmul_succ (n: ℕ) (a: α) : (n + 1) • a = n • a + a := by intros; rfl
class IsMonoid extends IsSemigroup α, IsMulOneClass α: Prop where
  npow_zero (a: α) : a ^ 0 = 1 := by intros; rfl
  npow_succ (n: ℕ) (a: α) : a ^ (n + 1) = a ^ n * a := by intros; rfl

def zero_nsmul [IsAddMonoid α₀] (a: α₀) : 0 • a = 0 := IsAddMonoid.nsmul_zero a
def succ_nsmul [IsAddMonoid α₀] (n: ℕ) (a: α₀) : (n + 1) • a = n • a + a := IsAddMonoid.nsmul_succ n a
def npow_zero [IsMonoid α₁] (a: α₁) : a ^ 0 = 1 := IsMonoid.npow_zero a
def npow_succ [IsMonoid α₁] (n: ℕ) (a: α₁) : a ^ (n + 1) = a ^ n * a := IsMonoid.npow_succ n a
def nsmul_zero [IsAddMonoid α₀] (a: ℕ) : a • (0: α₀) = 0 := by
  induction a with
  | zero => rw [zero_nsmul]
  | succ a ih => rw [succ_nsmul, ih, add_zero]
def one_npow [IsMonoid α₁] (a: ℕ) : (1: α₁) ^ a = 1 := by
  induction a with
  | zero => rw [npow_zero]
  | succ a ih => rw [npow_succ, ih, mul_one]

def nsmul_one [IsAddMonoid α₀] (a: α₀) : 1 • a = a := by rw [succ_nsmul, zero_nsmul, zero_add]
def one_snsmul [IsAddMonoid α₀] (a: α₀) : 1 • a = a := nsmul_one a
def npow_one [IsMonoid α₁] (a: α₁) : a ^ 1 = a := by rw [npow_succ, npow_zero, one_mul]

def nsmul_eq_nsmulRec [IsAddMonoid α₀] (n: ℕ) (a: α₀) : n • a = nsmulRec n a := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, ih]; rfl

def npow_eq_npowRec [IsMonoid α₁] (n: ℕ) (a: α₁) : a ^ n = npowRec n a := by
  induction n with
  | zero => rw [npow_zero]; rfl
  | succ n ih => rw [npow_succ, ih]; rfl

def succ_nsmul' [IsAddMonoid α₀] (n: ℕ) (a: α₀) : (n + 1) • a = a + n • a := by
  have : IsAddSemigroup α₀ := IsAddMonoid.toIsAddSemigroup
  induction n with
  | zero =>
    rw [zero_nsmul, add_zero, succ_nsmul, zero_nsmul, zero_add]
  | succ n ih => rw [succ_nsmul n, ←add_assoc, ←ih, succ_nsmul (n + 1)]
def npow_succ' [IsMonoid α₁] (n: ℕ) (a: α₁) : a ^ (n + 1) = a * a ^ n := by
  have : IsSemigroup α₁ := IsMonoid.toIsSemigroup
  induction n with
  | zero =>
    rw [npow_zero, mul_one, npow_succ, npow_zero, one_mul]
  | succ n ih => rw [npow_succ n, ←mul_assoc, ←ih, npow_succ (n + 1)]

def add_nsmul [IsAddMonoid α₀] (n m: ℕ) (a: α₀) : (n + m) • a = n • a + m • a := by
  have : IsAddSemigroup α₀ := IsAddMonoid.toIsAddSemigroup
  induction m with
  | zero => rw [Nat.add_zero, zero_nsmul, add_zero]
  | succ m ih => rw [Nat.add_succ, succ_nsmul, succ_nsmul, ←add_assoc, ih]
def npow_add [IsMonoid α₁] (n m: ℕ) (a: α₁) : a ^ (n + m) = a ^ n * a ^ m := by
  have : IsSemigroup α₁ := IsMonoid.toIsSemigroup
  induction m with
  | zero => rw [Nat.add_zero, npow_zero, mul_one]
  | succ m ih => rw [Nat.add_succ, npow_succ, npow_succ, ←mul_assoc, ih]

def nsmul_add [IsAddMonoid α₀] [IsAddCommMagma α₀] (n: ℕ) (x y: α₀) : n • (x + y) = n • x + n • y := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, add_zero]
  | succ n ih =>
    rw [succ_nsmul, ih, add_assoc, add_comm _ (x + y), ←add_assoc, ←add_assoc, ←succ_nsmul, add_assoc, ←succ_nsmul']

def mul_npow [IsMonoid α₁] [IsCommMagma α₁] (n: ℕ) (x y: α₁) : (x * y) ^ n = x ^ n * y ^ n := by
  induction n with
  | zero => rw [npow_zero, npow_zero, npow_zero, mul_one]
  | succ n ih =>
    rw [npow_succ, ih, mul_assoc, mul_comm _ (x * y), ←mul_assoc, ←mul_assoc, ←npow_succ, mul_assoc, ←npow_succ']

def mul_nsmul [IsAddMonoid α₀] (n m: ℕ) (x: α₀) : (m * n) • x = m • n • x := by
  induction m with
  | zero => rw [Nat.zero_mul, zero_nsmul, zero_nsmul]
  | succ m ih => rw [succ_nsmul, Nat.succ_mul, add_nsmul, ih]

def npow_mul [IsMonoid α₁] (n m: ℕ) (x: α₁) : x ^ (m * n) = (x ^ n) ^ m := by
  induction m with
  | zero => rw [Nat.zero_mul, npow_zero, npow_zero]
  | succ m ih => rw [npow_succ, Nat.succ_mul, npow_add, ih]

def one_nsmul [IsAddMonoid α₀] (x: α₀) : 1 • x = x := by rw [succ_nsmul, zero_nsmul, zero_add]

def zsmulRec : ℤ -> α₀ -> α₀
| .ofNat n, a => n • a
| .negSucc n, a => -((n + 1) • a)

def zpowRec : ℤ -> α₁ -> α₁
| .ofNat n, a => a ^ n
| .negSucc n, a => (a ^ (n + 1))⁻¹

class IsInvolutiveNeg: Prop where
  neg_neg (a: α): - -a = a
class IsInvolutiveInv: Prop where
  inv_inv (a: α): a⁻¹⁻¹ = a

def neg_neg [IsInvolutiveNeg α₀] (a: α₀) : - -a = a := IsInvolutiveNeg.neg_neg a
def inv_inv [IsInvolutiveInv α₁] (a: α₁) : a⁻¹⁻¹ = a := IsInvolutiveInv.inv_inv a

def sub' (a b: α₀) : α₀ := a + -b
def div' (a b: α₁) : α₁ := a * b⁻¹

class IsSubNegMonoid extends IsAddMonoid α: Prop where
  sub_eq_add_neg (a b: α) : a - b = a + -b
  zsmul_ofNat (n: ℕ) (a: α) : (n: ℤ) • a = n • a
  zsmul_negSucc (n: ℕ) (a: α) : (Int.negSucc n) • a = -(n.succ • a)

class IsDivInvMonoid extends IsMonoid α: Prop where
  div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
  zpow_ofNat (n: ℕ) (a: α) : a ^ (n: ℤ) = a ^ n
  zpow_negSucc (n: ℕ) (a: α) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹

def sub_eq_add_neg [IsSubNegMonoid α₀] (a b: α₀) : a - b = a + -b := IsSubNegMonoid.sub_eq_add_neg a b
def div_eq_mul_inv [IsDivInvMonoid α₁] (a b: α₁) : a / b = a * b⁻¹ := IsDivInvMonoid.div_eq_mul_inv a b
def zsmul_ofNat [IsSubNegMonoid α₀] (n: ℕ) (a: α₀) : (Int.ofNat n) • a = n • a := IsSubNegMonoid.zsmul_ofNat n a
def zpow_ofNat [IsDivInvMonoid α₁] (n: ℕ) (a: α₁) : a ^ (Int.ofNat n) = a ^ n := IsDivInvMonoid.zpow_ofNat n a
def zsmul_negSucc [IsSubNegMonoid α₀] (n: ℕ) (a: α₀) : (Int.negSucc n) • a = -(n.succ • a) := IsSubNegMonoid.zsmul_negSucc n a
def zpow_negSucc [IsDivInvMonoid α₁] (n: ℕ) (a: α₁) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹ := IsDivInvMonoid.zpow_negSucc n a

def zsmul_neg_one [IsSubNegMonoid α₀] (a: α₀) : (-1) • a = -a := by erw [zsmul_negSucc, nsmul_one]
def zpow_neg_one [IsDivInvMonoid α₁] (a: α₁) : a ^ (-1) = a⁻¹ := by erw [zpow_negSucc, npow_one]

class IsNegZeroClass: Prop where
  neg_zero: -(0: α) = 0
class IsInvOneClass: Prop where
  inv_one: (1: α)⁻¹ = 1

def neg_zero [IsNegZeroClass α₀] : -(0: α₀) = 0 := IsNegZeroClass.neg_zero
def inv_one [IsInvOneClass α₁] : (1: α₁)⁻¹ = 1 := IsInvOneClass.inv_one

def zsmul_zero [IsSubNegMonoid α₀] [IsNegZeroClass α₀] (a: ℤ) : a • (0: α₀) = 0 := by
  cases a
  rw [zsmul_ofNat, nsmul_zero]
  rw [zsmul_negSucc, nsmul_zero, neg_zero]

def zero_zsmul [IsSubNegMonoid α₀] (a: α₀) : (0: ℤ) • a = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  rw [this, zsmul_ofNat, zero_nsmul]

def one_zsmul [IsSubNegMonoid α₀] (a: α₀) : (1: ℤ) • a = a := by
  have : 1 = Int.ofNat 1 := rfl
  rw [this, zsmul_ofNat, one_nsmul]

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
def inv_mul_rev [IsDivisionMonoid α₁] (a b: α₁) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := IsDivisionMonoid.inv_mul_rev a b
def inv_eq_of_mul_left [IsDivisionMonoid α₁] {a b: α₁} : a * b = 1 -> a⁻¹ = b := IsDivisionMonoid.inv_eq_of_mul_left a b
def inv_eq_of_mul_right [IsDivisionMonoid α₁] {a b: α₁} : a * b = 1 -> a = b⁻¹ := by
  intro h
  rw [←inv_eq_of_mul_left h, inv_inv]

class IsAddGroup extends IsSubNegMonoid α: Prop where
  neg_add_cancel (a: α): -a + a = 0
class IsGroup extends IsDivInvMonoid α: Prop where
  inv_mul_cancel (a: α): a⁻¹ * a = 1

def left_neg_eq_right_neg [IsAddGroup α₀] { a b c: α₀ } (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]
def left_inv_eq_right_inv [IsGroup α₁] { a b c: α₁ } (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

def neg_add_cancel [IsAddGroup α₀] (a: α₀): -a + a = 0 := IsAddGroup.neg_add_cancel a
def inv_mul_cancel [IsGroup α₁] (a: α₁): a⁻¹ * a = 1 := IsGroup.inv_mul_cancel a

private theorem neg_eq_of_add [IsAddGroup α₀] { a b: α₀ } (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (neg_add_cancel a) h
private theorem inv_eq_of_mul [IsGroup α₁] { a b: α₁ } (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

instance IsAddGroup.toInvolutNeg [IsAddGroup α] : IsInvolutiveNeg α where
  neg_neg a := neg_eq_of_add (neg_add_cancel a)
instance IsGroup.toInvolutInv [IsGroup α] : IsInvolutiveInv α where
  inv_inv a := inv_eq_of_mul (inv_mul_cancel a)

def add_neg_cancel [IsAddGroup α₀] (a: α₀): a + -a = 0 := by
  conv => { lhs; lhs; rw [←neg_neg a] }
  rw [neg_add_cancel]
def mul_inv_cancel [IsGroup α₁] (a: α₁): a * a⁻¹ = 1 := by
  conv => { lhs; lhs; rw [←inv_inv a] }
  rw [inv_mul_cancel]

class IsLeftDistrib: Prop where
  left_distrib (k a b: α): k * (a + b) = k * a + k * b
class IsRightDistrib: Prop where
  right_distrib (a b k: α): (a + b) * k = a * k + b * k

def mul_add [IsLeftDistrib R] (k a b: R): k * (a + b) = k * a + k * b := IsLeftDistrib.left_distrib k a b
def add_mul [IsRightDistrib R] (a b k: R): (a + b) * k = a * k + b * k := IsRightDistrib.right_distrib a b k

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

def natCast_zero [IsAddMonoidWithOne R₀] : NatCast.natCast 0 = (0: R₀) := IsAddMonoidWithOne.natCast_zero
def natCast_succ [IsAddMonoidWithOne R₀] (n: ℕ) : NatCast.natCast n.succ = NatCast.natCast n + (1: R₀) := IsAddMonoidWithOne.natCast_succ n
def natCast_one [IsAddMonoidWithOne R₀] : NatCast.natCast 1 = (1: R₀) := by
  rw [natCast_succ, natCast_zero, zero_add]
def ofNat_eq_natCast [IsAddMonoidWithOne R₀] (n: ℕ) : @OfNat.ofNat R₀ (n + 2) _ = NatCast.natCast (n + 2) := IsAddMonoidWithOne.ofNat_eq_natCast n

class IsAddGroupWithOne extends IsAddGroup α, IsAddMonoidWithOne α: Prop where
  intCast_ofNat (n: ℕ) : IntCast.intCast n = (NatCast.natCast n: α)
  intCast_negSucc (n: ℕ) : IntCast.intCast (Int.negSucc n) = -(NatCast.natCast n.succ: α)

def intCast_ofNat [IsAddGroupWithOne R₀] (n: ℕ) : IntCast.intCast (Int.ofNat n) = (NatCast.natCast n: R₀) := IsAddGroupWithOne.intCast_ofNat n
def intCast_negSucc [IsAddGroupWithOne R₀] (n: ℕ) : IntCast.intCast (Int.negSucc n) = -(NatCast.natCast n.succ: R₀) := IsAddGroupWithOne.intCast_negSucc n

class IsSemiring extends
  IsAddCommMagma α, IsAddMonoidWithOne α,
  IsSemigroup α, IsMulZeroClass α, IsMulOneClass α,
  IsLeftDistrib α, IsRightDistrib α, IsMonoid α : Prop where

instance [IsAddCommMagma α] [IsAddMonoidWithOne α] [IsSemigroup α] [IsMulZeroClass α] [IsMulOneClass α] [IsLeftDistrib α] [IsRightDistrib α] [IsMonoid α] : IsSemiring α where
  npow_zero := npow_zero
  npow_succ := npow_succ

class IsRing extends IsSemiring α, IsAddGroupWithOne α : Prop where

instance [IsSemiring α] [IsAddGroupWithOne α] : IsRing α where
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel

def mul_sub [IsRing R] (k a b: R): k * (a - b) = k * a - k * b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add]
  congr 1
  symm
  apply neg_eq_of_add
  rw [←mul_add, add_neg_cancel, mul_zero]

def sub_mul [IsRing R] (k a b: R): (a - b) * k = a * k - b * k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_mul]
  congr 1
  symm
  apply neg_eq_of_add
  rw [←add_mul, add_neg_cancel, zero_mul]

instance [IsAddGroup α] : IsSubtractionMonoid α where
  neg_add_rev := by
    intro a b
    apply neg_eq_of_add
    rw [add_assoc, ←add_assoc b, add_neg_cancel, zero_add, add_neg_cancel]
  neg_eq_of_add_left _ _ := neg_eq_of_add

instance [IsGroup α] : IsDivisionMonoid α where
  inv_mul_rev := by
    intro a b
    apply inv_eq_of_mul
    rw [mul_assoc, ←mul_assoc b, mul_inv_cancel, one_mul, mul_inv_cancel]
  inv_eq_of_mul_left _ _ := inv_eq_of_mul

def neg_mul_left [IsAddGroup R₀] [IsRightDistrib R₀] [IsMulZeroClass R₀] (a b: R₀) : -(a * b) = -a * b := by
  apply neg_eq_of_add
  rw [←add_mul, add_neg_cancel, zero_mul]
def neg_mul_right [IsAddGroup R₀] [IsLeftDistrib R₀] [IsMulZeroClass R₀] (a b: R₀) : -(a * b) = a * -b := by
  apply neg_eq_of_add
  rw [←mul_add, add_neg_cancel, mul_zero]

def nsmul_eq_natCast_mul [IsSemiring R₀] (n: ℕ) (x: R₀) : n • x = n * x := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast, natCast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast, natCast_succ, add_mul, one_mul]

def zsmul_eq_intCast_mul [IsRing R₀] (n: ℤ) (x: R₀) : n • x = n * x := by
  cases n with
  | ofNat n =>
    rw [zsmul_ofNat n, Int.cast, intCast_ofNat, nsmul_eq_natCast_mul]
  | negSucc n =>
    rw [zsmul_negSucc, Int.cast, intCast_negSucc, nsmul_eq_natCast_mul, neg_mul_left]

def add_one_mul [IsMulOneClass R₀] [IsRightDistrib R₀] (a b: R₀) : (a + 1) * b = a * b + b := by rw [add_mul, one_mul]
def mul_add_one [IsMulOneClass R₀] [IsLeftDistrib R₀] (a b: R₀) : a * (b + 1) = a * b + a := by rw [mul_add, mul_one]
def one_add_mul [IsMulOneClass R₀] [IsRightDistrib R₀] (a b: R₀) : (1 + a) * b = b + a * b := by rw [add_mul, one_mul]
def mul_one_add [IsMulOneClass R₀] [IsLeftDistrib R₀] (a b: R₀) : a * (1 + b) = a + a * b := by rw [mul_add, mul_one]

def two_mul [IsAddMonoidWithOne R₀] [IsRightDistrib R₀] [IsMulOneClass R₀] (a: R₀) : 2 * a = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, add_mul, one_mul]
def mul_two [IsAddMonoidWithOne R₀] [IsLeftDistrib R₀] [IsMulOneClass R₀] (a: R₀) : a * 2 = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, mul_add, mul_one]

class IsMulAction [IsMonoid R] : Prop where
  one_smul: ∀a: M, (1: R) • a = a
  mul_smul: ∀x y: R, ∀b: M, (x * y) • b = x • y • b

class IsDistribMulAction [IsMonoid R] [IsAddMonoid M] extends IsMulAction R M : Prop where
  smul_zero: ∀a: R, a • (0: M) = 0
  smul_add: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y

class IsModule [IsSemiring R] [IsAddCommMagma M] [IsAddMonoid M] extends IsDistribMulAction R M: Prop where
  add_smul: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x
  zero_smul: ∀x: M, (0: R) • x = 0

class IsNonUnitalNonAssocSemiring extends IsAddCommMagma α, IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsMulZeroClass α: Prop

class IsNonAssocSemiring extends IsNonUnitalNonAssocSemiring α, IsMulOneClass α, IsAddMonoidWithOne α: Prop

instance [IsSemiring α] : IsNonAssocSemiring α where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_zero := IsAddMonoidWithOne.ofNat_zero
  ofNat_one := IsAddMonoidWithOne.ofNat_one
  ofNat_eq_natCast := IsAddMonoidWithOne.ofNat_eq_natCast

instance [IsAddGroup α] : IsNegZeroClass α where
  neg_zero := by
    apply neg_eq_of_add
    rw [add_zero]

instance [IsGroup α] : IsInvOneClass α where
  inv_one := by
    apply inv_eq_of_mul
    rw [mul_one]

def neg_eq_neg_one_zsmul [IsAddGroup R₀] (a: R₀) : -a = -1 • a := by
  have : -1 = Int.negSucc 0 := rfl
  erw [this, zsmul_negSucc, one_nsmul]

def natCast_add [IsSemiring R₀] (a b: ℕ) : (NatCast.natCast (a + b): R₀) = NatCast.natCast a + NatCast.natCast b := by
  induction b with
  | zero => rw [natCast_zero, Nat.add_zero, add_zero]
  | succ b ih => rw [Nat.add_succ, natCast_succ, natCast_succ, ←add_assoc, ih]

def natCast_mul [IsSemiring R₀] (a b: ℕ) : (NatCast.natCast (a * b): R₀) = NatCast.natCast a * NatCast.natCast b := by
  induction b with
  | zero => rw [Nat.mul_zero, natCast_zero, mul_zero]
  | succ b ih => rw [Nat.mul_succ, natCast_add, natCast_succ, mul_add, mul_one, ih]

def neg_add_rev [IsAddGroup α₀] (a b: α₀) : -(a + b) = -b + -a := by
  apply neg_eq_of_add
  rw [add_assoc, ←add_assoc b, add_neg_cancel, zero_add, add_neg_cancel]

def intCast_zero [IsRing R₀] : (IntCast.intCast 0: R₀) = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  rw [this, intCast_ofNat, natCast_zero]

def intCast_succ [IsRing R₀] (a: ℤ) : (IntCast.intCast (a + 1): R₀) = IntCast.intCast a + 1 := by
  cases a with
  | ofNat a =>
    have : 1 = Int.ofNat 1 := rfl
    rw [intCast_ofNat, this,
      Int.ofNat_eq_coe,
      Int.ofNat_eq_coe,
      Int.ofNat_add_ofNat,
      ←Int.ofNat_eq_coe, intCast_ofNat, natCast_add, natCast_one]
  | negSucc a =>
    cases a with
    | zero =>
      suffices (IntCast.intCast 0: R₀) = IntCast.intCast (Int.negSucc 0) + 1 from this
      rw [intCast_zero, intCast_negSucc, natCast_one, neg_add_cancel]
    | succ a =>
      suffices (IntCast.intCast (Int.negSucc a): R₀) = IntCast.intCast (Int.negSucc (a + 1)) + 1 from this
      rw [intCast_negSucc, intCast_negSucc, natCast_succ (a + 1),]
      apply neg_eq_of_add
      rw [neg_add_rev, add_assoc, add_comm _ 1, ←add_assoc (-1), neg_add_cancel, zero_add, add_neg_cancel]
def intCast_pred [IsRing R₀] (a: ℤ) : (IntCast.intCast (a - 1): R₀) = IntCast.intCast a - 1 := by
  suffices (IntCast.intCast (a - 1): R₀) = (IntCast.intCast (a - 1) + 1) - 1 by
    rw [←intCast_succ, Int.sub_add_cancel] at this
    exact this
  rw [sub_eq_add_neg _ (1: R₀), add_assoc, add_neg_cancel, add_zero]

def intCast_add [IsRing R₀] (a b: ℤ) : (IntCast.intCast (a + b): R₀) = IntCast.intCast a + IntCast.intCast b := by
  induction b using Int.induction with
  | zero => rw [intCast_zero, add_zero, Int.add_zero]
  | succ b ih => rw [←Int.add_assoc, intCast_succ, intCast_succ, ih, add_assoc]
  | pred b ih => rw [←Int.add_sub_assoc, intCast_pred, intCast_pred, ih, sub_eq_add_neg, add_assoc, sub_eq_add_neg]

def intCast_neg [IsRing R₀] (a: ℤ) : (IntCast.intCast (-a): R₀) = -IntCast.intCast a := by
  symm
  apply neg_eq_of_add
  rw [←intCast_add, Int.add_right_neg, intCast_zero]

def intCast_sub [IsRing R₀] (a b: ℤ) : (IntCast.intCast (a - b): R₀) = IntCast.intCast a - IntCast.intCast b := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg, sub_eq_add_neg]

def intCast_mul [IsRing R₀] (a b: ℤ) : (IntCast.intCast (a * b): R₀) = IntCast.intCast a * IntCast.intCast b := by
  induction b using Int.induction with
  | zero => rw [Int.mul_zero, intCast_zero, mul_zero]
  | succ b ih => rw [Int.mul_add, Int.mul_one, intCast_succ, mul_add, intCast_add, ih, mul_one]
  | pred b ih => rw [Int.mul_sub, Int.mul_one, intCast_pred, mul_sub, intCast_sub, ih, mul_one]

def succ_zsmul [IsAddGroup α₀]  (x: ℤ) (a: α₀) : (x + 1) • a = x • a + a := by
  cases x with
  | ofNat x =>
    have : (1: ℤ) = ↑(1: ℕ) := rfl
    rw [this, Int.ofNat_eq_coe, Int.ofNat_add_ofNat, ←Int.ofNat_eq_coe, ←Int.ofNat_eq_coe, zsmul_ofNat, zsmul_ofNat, succ_nsmul]
  | negSucc x =>
  cases x with
  | zero =>
    have : Int.negSucc 0 = -1 := rfl
    rw [this, Int.add_left_neg, zero_zsmul, ←neg_eq_neg_one_zsmul, neg_add_cancel]
  | succ x =>
    have : (1: ℤ) = ↑(1: ℕ) := rfl
    rw [this, Int.negSucc_add_ofNat, Int.subNatNat_of_lt, Nat.succ_sub_succ, Nat.sub_zero, Nat.add_one, Nat.pred_succ]
    rw [zsmul_negSucc, zsmul_negSucc, succ_nsmul' x.succ, neg_add_rev, add_assoc, neg_add_cancel, add_zero]
    apply Nat.succ_lt_succ
    apply Nat.zero_lt_succ

def pred_zsmul [IsAddGroup α₀]  (x: ℤ) (a: α₀) : (x - 1) • a = x • a - a := by
  conv in x • a => {
    rw [←Int.sub_add_cancel x 1]
  }
  rw [succ_zsmul, sub_eq_add_neg _ a, add_assoc, add_neg_cancel, add_zero]

def add_zsmul [IsAddGroup α₀] (x y: ℤ) (a: α₀) : (x + y) • a = x • a + y • a := by
  induction y using Int.induction with
  | zero => rw [Int.add_zero, zero_zsmul, add_zero]
  | succ y ih => rw [←Int.add_assoc, succ_zsmul, succ_zsmul, ←add_assoc, ih]
  | pred y ih => rw [←Int.add_sub_assoc, pred_zsmul, pred_zsmul, sub_eq_add_neg (y • a) a, ←add_assoc, ih, ←sub_eq_add_neg]

def neg_zsmul [IsAddGroup α₀] (x: ℤ) (a: α₀) : (-x) • a = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←add_zsmul, Int.add_right_neg, zero_zsmul]

def zsmul_add [IsAddGroup α₀] [IsAddCommMagma α₀] (x: ℤ) (a b: α₀) : x • (a + b) = x • a + x • b := by
  induction x using Int.induction with
  | zero => rw [zero_zsmul, zero_zsmul, zero_zsmul, add_zero]
  | succ y ih => rw [succ_zsmul, ih, add_comm a b, add_assoc, ←add_assoc (y • b), ←succ_zsmul, add_comm _ a, ←add_assoc, ←succ_zsmul]
  | pred y ih => rw [pred_zsmul, ih, sub_eq_add_neg, neg_add_rev a b, add_assoc, ←add_assoc (y • b), ←sub_eq_add_neg _ b, ←pred_zsmul, add_comm _ (-a), ←add_assoc, ←sub_eq_add_neg, ←pred_zsmul]

def zsmul_neg [IsAddGroup α₀] [IsAddCommMagma α₀] (x: ℤ) (a: α₀) : x • (-a) = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←zsmul_add, add_neg_cancel, zsmul_zero]

def zsmul_sub [IsAddGroup α₀] [IsAddCommMagma α₀] (x: ℤ) (a b: α₀) : x • (a - b) = x • a - x • b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, zsmul_add, zsmul_neg]

def sub_zsmul [IsAddGroup α₀] (x y: ℤ) (a: α₀) : (x - y) • a = x • a - y • a := by
  rw [Int.sub_eq_add_neg, sub_eq_add_neg, add_zsmul, neg_zsmul]

def mul_zsmul [IsAddGroup α₀]  [IsAddCommMagma α₀] (x y: ℤ) (a: α₀) : (x * y) • a = x • y • a := by
  induction y using Int.induction with
  | zero => rw [Int.mul_zero, zero_zsmul, zsmul_zero]
  | succ y ih => rw [Int.mul_add, Int.mul_one, add_zsmul, add_zsmul, one_zsmul, zsmul_add, ih]
  | pred y ih => rw [Int.mul_sub, Int.mul_one, sub_zsmul, sub_zsmul, one_zsmul, zsmul_sub, ih]
