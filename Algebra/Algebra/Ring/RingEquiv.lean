import Algebra.Algebra.Ring.Nat
import Algebra.Algebra.Ring.Algebra
import Algebra.Equiv

variable {S: Type*} [Zero S] [Add S] [One S] [Mul S] [Pow S ℕ] [SMul ℕ S] [NatCast S] [∀n, OfNat S (n + 2)]
variable [IsSemiring S] [IsCommMagma S]

variable {A: Type*} [Zero A] [Add A] [One A] [Mul A] [Pow A ℕ] [SMul ℕ A] [NatCast A] [∀n, OfNat A (n + 2)]
variable [IsSemiring A] [SMul S A] [HasRingHom S A] [IsAlgebra S A]

variable {α: Type*}
-- variable [Zero α] [Add α] [One α] [Mul α] [Pow α ℕ] [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)]
-- variable [IsSemiring α]
variable [Add α] [Mul α]

variable {R: Type*} [Zero R] [Add R] [One R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
variable [Sub R] [Neg R] [SMul ℤ R] [IntCast R] [IsRing R]

namespace RingEquiv

inductive Rel (r: α -> α -> Prop) : α -> α -> Prop where
| refl a : Rel r a a
| symm : Rel r a b -> Rel r b a
| trans : Rel r a b -> Rel r b c -> Rel r a c
| of {a b: α} : r a b -> Rel r a b
| add_left : Rel r a b -> Rel r (a + k) (b + k)
| mul_left : Rel r a b -> Rel r (a * k) (b * k)
| mul_right : Rel r a b -> Rel r (k * a) (k * b)

def Rel.add_right [IsAddCommMagma α] {a b k: α} : Rel r a b -> Rel r (k + a) (k + b) := by
  intro r
  rw [add_comm k, add_comm k]
  apply Rel.add_left
  assumption

def Rel.neg {a b: R} : Rel r a b -> Rel r (-a) (-b) := by
  intro r
  rw [neg_eq_neg_one_zsmul a, neg_eq_neg_one_zsmul b,
    zsmul_eq_intCast_mul, zsmul_eq_intCast_mul]
  apply Rel.mul_right
  assumption

def Rel.sub_left {a b k: R} : Rel r a b -> Rel r (a - k) (b - k) := by
  intro r
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply Rel.add_left
  assumption

def Rel.sub_right {a b k: R} : Rel r a b -> Rel r (k - a) (k - b) := by
  intro r
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply Rel.add_right
  apply Rel.neg
  assumption

def Rel.smul {a b: A} {k:S} : Rel r a b -> Rel r (k • a) (k • b) := by
  intro r
  rw [IsAlgebra.smul_def, IsAlgebra.smul_def]
  apply Rel.mul_right
  assumption

variable {r: α -> α -> Prop}
variable {r₀: R -> R -> Prop}

def setoid (r: α -> α -> Prop) : Setoid α where
  r := Rel r
  iseqv := ⟨.refl,.symm,.trans⟩

/-- The quotient of a ring by an arbitrary relation. -/
structure _root_.RingQuot (r : α → α → Prop) where
  ofEquiv ::
  toEquiv : Equiv (setoid r)

def mk : α -> RingQuot r := (.ofEquiv <| Equiv.mk (setoid r) ·)

-- can't be irreducible, causes diamonds in ℕ-algebras
private def natCast [NatCast α] (n : ℕ) : RingQuot r :=
  ⟨Equiv.mk _ n⟩

@[irreducible]
private def zero [Zero α] : RingQuot r :=
  ⟨Equiv.mk _ 0⟩

@[irreducible]
private def one [One α] : RingQuot r :=
  ⟨Equiv.mk _ 1⟩

@[irreducible]
private def ofNat n [o: OfNat α n] : RingQuot r :=
  ⟨Equiv.mk _ o.ofNat⟩

@[irreducible]
private def add [IsAddCommMagma α] : RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨by
  apply Equiv.lift₂ _ _ a b
  intro a b
  exact .mk _ (a + b)
  intro a b c d ac bd
  apply Equiv.sound
  apply Rel.trans
  apply Rel.add_left
  assumption
  apply Rel.add_right
  assumption⟩

@[irreducible]
private def mul : RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨by
  apply Equiv.lift₂ _ _ a b
  intro a b
  exact .mk _ (a * b)
  intro a b c d ac bd
  apply Equiv.sound
  apply Rel.trans
  apply Rel.mul_left
  assumption
  apply Rel.mul_right
  assumption⟩

@[irreducible]
private def neg : RingQuot r₀ → RingQuot r₀
  | ⟨a⟩ => ⟨by
    apply Equiv.lift _ _ a
    intro a
    exact .mk _ (-a)
    intro a b ab
    apply Equiv.sound
    apply Rel.neg
    assumption⟩

@[irreducible]
private def sub :
  RingQuot r₀ → RingQuot r₀ → RingQuot r₀
  | ⟨a⟩, ⟨b⟩ => ⟨by
    apply Equiv.lift₂ _ _ a b
    intro a b
    exact .mk _ (a - b)
    intro a b c d ac bd
    apply Equiv.sound
    apply Rel.trans
    apply Rel.sub_left
    assumption
    apply Rel.sub_right
    assumption⟩

@[irreducible]
private def npow
  [Zero α] [One α] [Pow α ℕ] [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)]
  [IsSemiring α] (n : ℕ) : RingQuot r → RingQuot r
  | ⟨a⟩ =>
    ⟨Equiv.lift (fun a ↦ Equiv.mk _ (a ^ n))
        (fun a b (h : Rel r a b) ↦ by
          -- note we can't define a `Rel.pow` as `Rel` isn't reflexive so `Rel r 1 1` isn't true
          dsimp only
          induction n with
          | zero => rw [npow_zero, npow_zero]
          | succ n ih =>
            rw [npow_succ, npow_succ]
            apply Equiv.sound
            replace ih := Equiv.exact _ _ ih
            apply Rel.trans
            apply Rel.mul_left
            assumption
            apply Rel.mul_right
            assumption)
        a⟩

-- @[irreducible]
private def smul [IsAlgebra S A] {r: A -> A -> Prop} (n: S) : RingQuot r -> RingQuot r
  | ⟨a⟩ => ⟨by
    apply Equiv.lift _ _ a
    intro a
    exact Equiv.mk _ (n • a)
    intro a b ab
    apply Equiv.sound
    apply Rel.smul
    assumption⟩

instance [NatCast α] : NatCast (RingQuot r) :=
  ⟨natCast⟩

instance [Zero α] : Zero (RingQuot r) :=
  ⟨zero⟩

instance [One α] : One (RingQuot r) :=
  ⟨one⟩

instance (priority := 900) [OfNat α n] : OfNat (RingQuot r) n :=
  ⟨ofNat n⟩

instance [IsAddCommMagma α] : Add (RingQuot r) :=
  ⟨add⟩

instance : Mul (RingQuot r) :=
  ⟨mul⟩

instance
  [Zero α] [One α] [Pow α ℕ] [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)]
  [IsSemiring α]
  : Pow (RingQuot r) ℕ :=
  ⟨fun a b => npow b a⟩

instance : Neg (RingQuot r₀) :=
  ⟨neg⟩

instance : Sub (RingQuot r₀) :=
  ⟨sub⟩

instance [IsAlgebra S A] {r: A -> A -> Prop} : SMul S (RingQuot r) :=
  ⟨smul⟩

def zero_quot [Zero α] : (⟨Equiv.mk _ 0⟩ : RingQuot r) = 0 :=
  show _ = zero by
    delta RingEquiv.zero
    rfl

def one_quot [One α] : (⟨Equiv.mk _ 1⟩ : RingQuot r) = 1 :=
  show _ = one by
    delta RingEquiv.one
    rfl

def ofNat_quot [o: OfNat α n] : (⟨Equiv.mk _ o.ofNat⟩ : RingQuot r) = _root_.OfNat.ofNat n := by
    delta OfNat.ofNat RingEquiv.ofNat instOfNatRingQuot
    rfl

def natCast_quot [NatCast α] : (⟨Equiv.mk _ (NatCast.natCast n)⟩ : RingQuot r) = NatCast.natCast n := by rfl

theorem add_quot [IsAddCommMagma α] {a b} : (⟨Equiv.mk _ a⟩ + ⟨Equiv.mk _ b⟩ : RingQuot r) = ⟨Equiv.mk _ (a + b)⟩ := by
  show add _ _ = _
  delta add
  dsimp
  rw [Equiv.lift₂_mk]

theorem mul_quot {a b:α} : (⟨Equiv.mk _ a⟩ * ⟨Equiv.mk _ b⟩ : RingQuot r) = ⟨Equiv.mk _ (a * b)⟩ := by
  show mul _ _ = _
  delta mul
  dsimp
  rw [Equiv.lift₂_mk]

theorem npow_quot
  [Zero α] [One α] [Pow α ℕ] [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)]
  [IsSemiring α]
   {a} {n : ℕ} : (⟨Equiv.mk _ a⟩ ^ n : RingQuot r) = ⟨Equiv.mk _ (a ^ n)⟩ := by
  show npow _ _ = _
  delta npow
  dsimp
  rw [Equiv.lift_mk]

theorem neg_quot {a} :
    (-⟨Equiv.mk _ a⟩ : RingQuot r₀) = ⟨Equiv.mk _ (-a)⟩ := by
  show neg _ = _
  delta neg
  dsimp
  rw [Equiv.lift_mk]

theorem sub_quot {a b} :
    (⟨Equiv.mk _ a⟩ - ⟨Equiv.mk _ b⟩ : RingQuot r₀) = ⟨Equiv.mk _ (a - b)⟩ := by
  show sub _ _ = _
  delta sub
  dsimp
  rw [Equiv.lift₂_mk]

theorem msmul_quot {n : S} {a : A} {r: A -> A -> Prop} :
    (n • ⟨Equiv.mk _ a⟩ : RingQuot r) = ⟨Equiv.mk _ (n • a)⟩ := by
  show smul _ _ = _
  delta smul
  dsimp
  rw [Equiv.lift_mk]

variable [IsAddCommMagma α]

instance : IsAddCommMagma (RingQuot r) where
  add_comm := by
    intro ⟨a⟩ ⟨b⟩
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    rw [add_quot, add_quot, add_comm]

instance [IsAddSemigroup α] : IsAddSemigroup (RingQuot r) where
  add_assoc := by
    intro ⟨a⟩ ⟨b⟩ ⟨c⟩
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    induction c using Equiv.ind with | mk c =>
    repeat rw [add_quot]
    rw [add_assoc]

instance [IsSemigroup α] : IsSemigroup (RingQuot r) where
  mul_assoc := by
    intro ⟨a⟩ ⟨b⟩ ⟨c⟩
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    induction c using Equiv.ind with | mk c =>
    repeat rw [mul_quot]
    rw [mul_assoc]

instance [IsLeftDistrib α] : IsLeftDistrib (RingQuot r) where
  left_distrib := by
    intro ⟨a⟩ ⟨b⟩ ⟨c⟩
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    induction c using Equiv.ind with | mk c =>
    repeat first|rw [mul_quot]|rw [add_quot]
    rw [mul_add]

instance [IsRightDistrib α] : IsRightDistrib (RingQuot r) where
  right_distrib := by
    intro ⟨a⟩ ⟨b⟩ ⟨c⟩
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    induction c using Equiv.ind with | mk c =>
    repeat first|rw [mul_quot]|rw [add_quot]
    rw [add_mul]

instance [Zero α] [IsAddZeroClass α] : IsAddZeroClass (RingQuot r) where
  add_zero := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←zero_quot, add_quot, add_zero]
  zero_add := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←zero_quot, add_quot, zero_add]

instance [One α] [IsMulOneClass α] : IsMulOneClass (RingQuot r) where
  mul_one := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←one_quot, mul_quot, mul_one]
  one_mul := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←one_quot, mul_quot, one_mul]

instance [Zero α] [IsMulZeroClass α] : IsMulZeroClass (RingQuot r) where
  mul_zero := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←zero_quot, mul_quot, mul_zero]
  zero_mul := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←zero_quot, mul_quot, zero_mul]

instance
  [Zero α] [One α] [Pow α ℕ] [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)]
  [SMul ℕ α]
  [IsSemiring α] : IsSemiring (RingQuot r) where
  natCast_zero := by
    rw [←natCast_quot, natCast_zero, zero_quot]
  natCast_succ n := by
    rw [←natCast_quot, natCast_succ, ←add_quot, one_quot, natCast_quot]
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast n := by
    rw [ofNat', ←ofNat_quot, ←natCast_quot, ofNat_eq_natCast]
  nsmul_zero := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←zero_quot, msmul_quot, zero_nsmul]
  nsmul_succ := by
    intro n ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [msmul_quot, succ_nsmul, msmul_quot, add_quot]
  npow_zero := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [npow_quot, npow_zero, one_quot]
  npow_succ := by
    intro n ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [npow_quot, npow_succ, npow_quot, mul_quot]

instance
  [Zero α] [One α] [Pow α ℕ] [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)]
  [SMul ℕ α]
  [Sub α] [Neg α] [SMul ℤ α] [IntCast α]
  [IsRing α] : IsRing (RingQuot r) where
  natCast_zero := by
    rw [←natCast_quot, natCast_zero, zero_quot]
  natCast_succ n := by
    rw [←natCast_quot, natCast_succ, ←add_quot, one_quot, natCast_quot]
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast n := by
    rw [ofNat', ←ofNat_quot, ←natCast_quot, ofNat_eq_natCast]
  nsmul_zero := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [←zero_quot, smul_quot, zero_nsmul]
  nsmul_succ := by
    intro n ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [smul_quot, succ_nsmul, smul_quot, add_quot]
  npow_zero := by
    intro ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [pow_quot, npow_zero, one_quot]
  npow_succ := by
    intro n ⟨a⟩
    induction a using Equiv.ind with | mk a =>
    rw [pow_quot, npow_succ, pow_quot, mul_quot]

end RingEquiv
