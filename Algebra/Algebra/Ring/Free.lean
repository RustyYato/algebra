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

end FreeAlgebra
