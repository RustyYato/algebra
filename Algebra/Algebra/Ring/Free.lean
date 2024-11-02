import Algebra.Algebra.Ring.Algebra
import Algebra.Equiv

namespace FreeAlgebra

variable {α V: Type*}
variable [Mul α] [Zero α] [Add α] [One α] [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)] [Pow α ℕ]
variable [IsCommMagma α] [IsSemiring α]

inductive Pre (α V: Type*) where
| of (v: V)
| ofScalar (a: α)
| add  : Pre α V -> Pre α V -> Pre α V
| mul  : Pre α V -> Pre α V -> Pre α V

instance : Add (Pre α V) := ⟨.add⟩
instance : Mul (Pre α V) := ⟨.mul⟩

namespace Pre

def hasCoeGenerator : Coe V (Pre α V) := ⟨.of⟩

def hasCoeSemiring : Coe α (Pre α V) := ⟨.ofScalar⟩

def hasMul : Mul (Pre α V) := ⟨.mul⟩

def hasAdd : Add (Pre α V) := ⟨.add⟩

def hasZero : Zero (Pre α V) := ⟨.ofScalar 0⟩

def hasOne : One (Pre α V) := ⟨.ofScalar 1⟩

def hasSmul : SMul α (Pre α V) := ⟨(.mul <| .ofScalar ·)⟩

end Pre

section

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul
  Pre.hasAdd Pre.hasZero Pre.hasOne Pre.hasSmul

variable [Zero A] [One A] [Add A] [Mul A] [Pow A ℕ] [SMul ℕ A]
variable [NatCast A] [∀n, OfNat A n] [IsSemiring A] [SMul α A]
variable [HasRingHom α A]

def liftFun (f: V -> A) [IsAlgebra α A] : Pre α V -> A
| .of v => f v
| .ofScalar v => algebraMap _ _ v
| .add a b => liftFun f a + liftFun f b
| .mul a b => liftFun f a * liftFun f b

inductive Rel : Pre α V -> Pre α V -> Prop
| refl a : Rel a a
| symm : Rel a b -> Rel b a
| trans : Rel a b -> Rel b c -> Rel a c

| add_scalar {r s: α} : Rel (↑(r + s)) (↑r + ↑s)
| mul_scalar {r s: α} : Rel (↑(r * s)) (↑r * ↑s)
| central_scalar {r: α} {a: Pre α V}  : Rel (r * a) (a * r)

| add_assoc {a b c: Pre α V} : Rel (a + b + c) (a + (b + c))
| add_comm {a b: Pre α V} : Rel (a + b) (b + a)
| zero_add {a: Pre α V} : Rel (0 + a) a

| mul_assoc {a b c: Pre α V} : Rel (a * b * c) (a * (b * c))
| one_mul {a: Pre α V} : Rel (1 * a) a
| mul_one {a: Pre α V} : Rel (a * 1) a

| zero_mul {a: Pre α V} : Rel (0 * a) 0
| mul_zero {a: Pre α V} : Rel (a * 0) 0

| mul_add {k a b: Pre α V} : Rel (k * (a + b)) (k * a + k * b)
| add_mul {k a b: Pre α V} : Rel ((a + b) * k) (a * k + b * k)

| add_congr {a b c d: Pre α V} : Rel a c -> Rel b d -> Rel (a + b) (c + d)
| mul_congr {a b c d: Pre α V} : Rel a c -> Rel b d -> Rel (a * b) (c * d)

end

instance Pre.setoid (α V: Type*) [Mul α] [Add α] [Zero α] [One α] : Setoid (Pre α V) where
  r := Rel
  iseqv := ⟨.refl,.symm,.trans⟩

def _root_.FreeAlgebra (α V: Type*) [Mul α] [Add α] [Zero α] [One α] := Equiv (Pre.setoid α V)
def mk : Pre α V -> FreeAlgebra α V := Equiv.mk (Pre.setoid α V)
def get : FreeAlgebra α V -> FreeAlgebra.Pre α V := Equiv.get
def mk_get : ∀z: FreeAlgebra α V, mk z.get = z := Equiv.mk_get
def ind { motive: FreeAlgebra α V -> Prop } : (mk: ∀x, motive (mk x)) -> ∀o, motive o := Equiv.ind
def lift : (f: FreeAlgebra.Pre α V -> β) -> (all_eq: ∀x y, x ≈ y -> f x = f y) -> FreeAlgebra α V -> β := Equiv.lift
def lift₂ : (f: FreeAlgebra.Pre α V -> FreeAlgebra.Pre α V -> γ) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> FreeAlgebra α V -> FreeAlgebra α V -> γ := Equiv.lift₂
def liftProp : (f: FreeAlgebra.Pre α V -> Prop) -> (all_eq: ∀x y, x ≈ y -> (f x -> f y)) -> FreeAlgebra α V -> Prop := by
  intro f alleq
  apply Equiv.liftProp f
  intro a b ab
  apply Iff.intro
  apply alleq _ _ ab
  apply alleq _ _ ab.symm
def liftProp₂ : (f: FreeAlgebra.Pre α V -> FreeAlgebra.Pre α V -> Prop) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> (f a b -> f c d)) -> FreeAlgebra α V -> FreeAlgebra α V -> Prop := by
  intro f alleq
  apply Equiv.liftProp₂ f
  intro a b c d ac bd
  apply Iff.intro
  apply alleq _ _ _ _ ac bd
  apply alleq _ _ _ _ ac.symm bd.symm
def lift_mk : lift f all_eq (mk (α := α) (V := V) a) = f a := Equiv.lift_mk _ _ _
def lift₂_mk : lift₂ f all_eq (mk (α := α) (V := V) a) (mk b) = f a b := Equiv.lift₂_mk _ _ _ _
def liftProp_mk : liftProp f all_eq (mk (α := α) (V := V) a) ↔ f a := Equiv.liftProp_mk _ _ _
def liftProp₂_mk : liftProp₂ f all_eq (mk (α := α) (V := V) a) (mk b) ↔ f a b := Equiv.liftProp₂_mk _ _ _ _
def exact : mk (α := α) (V := V) a = mk b -> a ≈ b := Equiv.exact _ _
def sound : a ≈ b -> mk a = mk (α := α) (V := V) b := Equiv.sound _ _
def exists_rep : ∀o, ∃p, mk (α := α) (V := V) p = o := Equiv.exists_rep

section Algebra

variable [Zero α] [One α] [Add α] [Mul α]

instance : Zero (FreeAlgebra α V) where
  zero := .mk (.ofScalar 0)
instance : One (FreeAlgebra α V) where
  one := .mk (.ofScalar 1)

instance : Add (FreeAlgebra α V) where
  add := by
    intro a b
    apply FreeAlgebra.lift₂ (fun _ => _) _ a b
    intro a b
    exact .mk (.add a b)
    intro a b c d ac bd
    apply FreeAlgebra.sound
    apply FreeAlgebra.Rel.add_congr
    <;> assumption

def mk_add (a b: Pre α V) : mk a + mk b = mk (a.add b) := lift₂_mk

instance : Mul (FreeAlgebra α V) where
  mul := by
    intro a b
    apply FreeAlgebra.lift₂ (fun _ => _) _ a b
    intro a b
    exact .mk (.mul a b)
    intro a b c d ac bd
    apply FreeAlgebra.sound
    apply FreeAlgebra.Rel.mul_congr
    <;> assumption

def mk_mul (a b: Pre α V) : mk a * mk b = mk (a.mul b) := lift₂_mk

instance : SMul α (FreeAlgebra α V) where
  smul x a := mk (.ofScalar x) * a

instance : Pow (FreeAlgebra α V) ℕ := ⟨flip npowRec⟩
instance : SMul ℕ (FreeAlgebra α V) := ⟨nsmulRec⟩
instance : NatCast (FreeAlgebra α V) where
  natCast n := mk <| .ofScalar n
instance (priority := 500) : OfNat (FreeAlgebra α V) n := ⟨Nat.cast n⟩

instance : IsAddCommMagma (FreeAlgebra α V) where
  add_comm := by
    intro a b
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    rw [mk_add, mk_add]
    apply sound
    apply Rel.add_comm

instance : IsAddSemigroup (FreeAlgebra α V) where
  add_assoc := by
    intro a b c
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    induction c using ind with | mk c =>
    repeat rw [mk_add]
    apply sound
    apply Rel.add_assoc

def zero_add' (a: FreeAlgebra α V) : 0 + a = a := by
  induction a using ind with | mk a =>
  erw [mk_add]
  apply sound
  apply Rel.zero_add

instance : IsAddZeroClass (FreeAlgebra α V) where
  zero_add := zero_add'
  add_zero a := by
    rw [add_comm]
    apply zero_add'

instance : IsMulOneClass (FreeAlgebra α V) where
  one_mul a := by
    induction a using ind with | mk a =>
    erw [mk_mul]
    apply sound
    apply Rel.one_mul
  mul_one a := by
    induction a using ind with | mk a =>
    erw [mk_mul]
    apply sound
    apply Rel.mul_one

instance : IsSemigroup (FreeAlgebra α V) where
  mul_assoc a b c := by
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    induction c using ind with | mk c =>
    repeat rw [mk_mul]
    apply sound
    apply Rel.mul_assoc

instance : IsMulZeroClass (FreeAlgebra α V) where
  zero_mul a := by
    induction a using ind with | mk a =>
    erw [mk_mul]
    apply sound
    apply Rel.zero_mul
  mul_zero a := by
    induction a using ind with | mk a =>
    erw [mk_mul]
    apply sound
    apply Rel.mul_zero

instance : IsLeftDistrib (FreeAlgebra α V) where
  left_distrib k a b := by
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    induction k using ind with | mk k =>
    repeat first|rw [mk_mul]|rw [mk_add]
    apply sound
    apply Rel.mul_add

instance : IsRightDistrib (FreeAlgebra α V) where
  right_distrib k a b := by
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    induction k using ind with | mk k =>
    repeat first|rw [mk_mul]|rw [mk_add]
    apply sound
    apply Rel.add_mul

instance [IsNonAssocSemiring α] : IsSemiring (FreeAlgebra α V) where
  ofNat_zero := rfl
  ofNat_one := rfl
  natCast_zero := by
    apply sound
    rw [Nat.cast, natCast_zero]
    apply Rel.refl
  natCast_succ n := by
    erw [mk_add]
    apply sound
    rw [Nat.cast, natCast_succ]
    apply Rel.add_scalar
  ofNat_eq_natCast _ := rfl
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  npow_zero _ := rfl
  npow_succ _ _ := rfl

instance [IsNonAssocSemiring α] : HasRingHom α (FreeAlgebra α V) where
  toFun a := mk <| .ofScalar a
  map_one := rfl
  map_zero := rfl
  map_add a b := by
    dsimp
    rw [mk_add]
    apply sound
    apply Rel.add_scalar
  map_mul a b := by
    dsimp
    rw [mk_mul]
    apply sound
    apply Rel.mul_scalar

instance [IsCommMagma α] [IsSemiring α] :
  IsAlgebra α (FreeAlgebra α V) where
  smul_def _ _ := rfl
  commutes := by
    intro r x
    induction x using ind with | mk x =>
    erw [mk_mul, mk_mul]
    apply sound
    apply Rel.central_scalar

end Algebra

end FreeAlgebra
