import Algebra.Algebra.Ring.Nat
import Algebra.FunLike.Basic

variable (M: Type*) [Zero M] [One M] [Add M] [Mul M] [Sub M] [Div M]
variable [Pow M ℕ] [SMul ℕ M]
variable [Pow M ℤ] [SMul ℤ M]
variable [Neg M] [Inv M]
variable [NatCast M] [IntCast M] [∀n, OfNat M (n+2)]

variable (N: Type*) [Zero N] [One N] [Add N] [Mul N] [Sub N] [Div N]
variable [Pow N ℕ] [SMul ℕ N]
variable [Pow N ℤ] [SMul ℤ N]
variable [Neg N] [Inv N]
variable [NatCast N] [IntCast N] [∀n, OfNat N (n+2)]

variable (O: Type*) [Zero O] [One O] [Add O] [Mul O] [Sub O] [Div O]
variable [Pow O ℕ] [SMul ℕ O]
variable [Pow O ℤ] [SMul ℤ O]
variable [Neg O] [Inv O]
variable [NatCast O] [IntCast O] [∀n, OfNat O (n+2)]

variable {M₀: Type*} [Zero M₀] [One M₀] [Add M₀] [Mul M₀] [Sub M₀] [Div M₀]
variable [Pow M₀ ℕ] [SMul ℕ M₀]
variable [Pow M₀ ℤ] [SMul ℤ M₀]
variable [Neg M₀] [Inv M₀]
variable [NatCast M₀] [IntCast M₀] [∀n, OfNat M₀ (n+2)]

variable {N₀: Type*} [Zero N₀] [One N₀] [Add N₀] [Mul N₀] [Sub N₀] [Div N₀]
variable [Pow N₀ ℕ] [SMul ℕ N₀]
variable [Pow N₀ ℤ] [SMul ℤ N₀]
variable [Neg N₀] [Inv N₀]
variable [NatCast N₀] [IntCast N₀] [∀n, OfNat N₀ (n+2)]

variable {O₀: Type*} [Zero O₀] [One O₀] [Add O₀] [Mul O₀] [Sub O₀] [Div O₀]
variable [Pow O₀ ℕ] [SMul ℕ O₀]
variable [Pow O₀ ℤ] [SMul ℤ O₀]
variable [Neg O₀] [Inv O₀]
variable [NatCast O₀] [IntCast O₀] [∀n, OfNat O₀ (n+2)]

variable (F: Type*) [FunLike F M₀ N₀]
variable {F₀: Type*} [FunLike F₀ M₀ N₀]

section Add

syntax "hom_coe_inj": term

macro_rules
| `(hom_coe_inj) => `(by
    intro x y eq
    cases x; cases y
    congr
    try
      apply coe_inj
      exact eq)

structure ZeroHom where
  toFun : M -> N
  map_zero: toFun 0 = 0

class IsZeroHom: Prop where
  map_zero: ∀f: F, f 0 = 0

structure AddHom where
  toFun: M -> N
  map_add: ∀x y: M, toFun (x + y) = toFun x + toFun y

infixr:25 " →ₙ+ " => AddHom

class IsAddHom: Prop where
  map_add: ∀f: F, ∀x y: M₀, f (x + y) = f x + f y

instance : FunLike (ZeroHom M N) M N where
  coe x := x.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr

instance : FunLike (M →ₙ+ N) M N where
  coe x := x.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr

instance : IsAddHom (M →ₙ+ N) where
  map_add := AddHom.map_add

def IsAddHom.toAddHom [IsAddHom F] (f: F) : AddHom M₀ N₀ where
  toFun := f
  map_add := map_add _

instance IsAddHom.coeAddHom [IsAddHom F] : CoeTC F (M₀ →ₙ+ N₀) where
  coe := IsAddHom.toAddHom _

def map_zero [IsZeroHom F₀] (f: F₀) : f 0 = 0 := IsZeroHom.map_zero _
def map_add [IsAddHom F₀] (f: F₀) (x y: M₀) : f (x + y) = f x + f y := IsAddHom.map_add _ _ _

structure AddMonoidHom [IsAddZeroClass M] [IsAddZeroClass N] extends ZeroHom M N, AddHom M N

class IsAddMonoidHom [IsAddZeroClass M₀] [IsAddZeroClass N₀] extends IsZeroHom F, IsAddHom F: Prop

infixr:25 " →+ " => AddMonoidHom

instance [IsAddZeroClass M] [IsAddZeroClass N] : FunLike (M →+ N) M N where
  coe x := x.toFun
  coe_inj := hom_coe_inj

def IsAddMonoidHom.toAddMonoidHom [IsAddZeroClass M₀] [IsAddZeroClass N₀] [IsAddMonoidHom F] (f: F) : M₀ →+ N₀ where
  toFun := f
  map_zero := map_zero _
  map_add := map_add _

instance IsAddMonoidHom.coeAddMonoidHom [IsAddZeroClass M₀] [IsAddZeroClass N₀] [IsAddMonoidHom F] : CoeTC F (M₀ →+ N₀) where
  coe := IsAddMonoidHom.toAddMonoidHom _

def AddHom.coe_coe [IsAddHom F] (f: F) : ((f: M₀ →ₙ+ N₀): M₀ -> N₀) = f := rfl
def AddMonoidHom.coe_coe [IsAddZeroClass M₀] [IsAddZeroClass N₀] [IsAddMonoidHom F] (f: F) : ((f: M₀ →+ N₀): M₀ -> N₀) = f := rfl

end Add

section Mul

structure OneHom where
  toFun : M -> N
  map_one: toFun 1 = 1

class IsOneHom: Prop where
  map_one: ∀f: F, f 1 = 1

structure MulHom where
  toFun: M -> N
  map_mul: ∀x y: M, toFun (x * y) = toFun x * toFun y

infixr:25 " →ₙ* " => MulHom

class IsMulHom: Prop where
  map_mul: ∀f: F, ∀x y: M₀, f (x * y) = f x * f y

instance : FunLike (OneHom M N) M N where
  coe x := x.toFun
  coe_inj := hom_coe_inj

instance : FunLike (M →ₙ* N) M N where
  coe x := x.toFun
  coe_inj := hom_coe_inj

instance : IsMulHom (M →ₙ* N) where
  map_mul := MulHom.map_mul

def IsMulHom.toMulHom [IsMulHom F] (f: F) : MulHom M₀ N₀ where
  toFun := f
  map_mul := map_mul _

instance IsMulHom.coeMulHom [IsMulHom F] : CoeTC F (M₀ →ₙ* N₀) where
  coe := IsMulHom.toMulHom _

def map_one [IsOneHom F₀] (f: F₀) : f 1 = 1 := IsOneHom.map_one _
def map_mul [IsMulHom F₀] (f: F₀) (x y: M₀) : f (x * y) = f x * f y := IsMulHom.map_mul _ _ _

structure MonoidHom [IsMulOneClass M] [IsMulOneClass N] extends OneHom M N, MulHom M N

class IsMonoidHom [IsMulOneClass M₀] [IsMulOneClass N₀] extends IsOneHom F, IsMulHom F: Prop

infixr:25 " →* " => MonoidHom

instance [IsMulOneClass M] [IsMulOneClass N] : FunLike (M →* N) M N where
  coe x := x.toFun
  coe_inj := hom_coe_inj

def IsMonoidHom.toMonoidHom [IsMulOneClass M₀] [IsMulOneClass N₀] [IsMonoidHom F] (f: F) : M₀ →* N₀ where
  toFun := f
  map_one := map_one _
  map_mul := map_mul _

instance IsMonoidHom.coeMonoidHom [IsMulOneClass M₀] [IsMulOneClass N₀] [IsMonoidHom F] : CoeTC F (M₀ →* N₀) where
  coe := IsMonoidHom.toMonoidHom _

def MulHom.coe_coe [IsMulHom F] (f: F) : ((f: M₀ →ₙ* N₀): M₀ -> N₀) = f := rfl
def MonoidHom.coe_coe [IsMulOneClass M₀] [IsMulOneClass N₀] [IsMonoidHom F] (f: F) : ((f: M₀ →* N₀): M₀ -> N₀) = f := rfl

end Mul

def ZeroHom.id : ZeroHom M M where
  toFun := _root_.id
  map_zero := rfl

def ZeroHom.comp (g: ZeroHom N₀ O₀) (f: ZeroHom M₀ N₀) : ZeroHom M₀ O₀ where
  toFun := g.toFun ∘ f.toFun
  map_zero := by
    dsimp
    rw [f.map_zero, g.map_zero]

def AddHom.id : M →ₙ+ M where
  toFun := _root_.id
  map_add _ _ := rfl

def AddHom.comp (g: N₀ →ₙ+ O₀) (f: M₀ →ₙ+ N₀) : M₀ →ₙ+ O₀ where
  toFun := g.toFun ∘ f.toFun
  map_add x y := by
    dsimp
    rw [f.map_add, g.map_add]

def AddMonoidHom.id [IsAddZeroClass M] : M →+ M where
  toFun := _root_.id
  map_zero := rfl
  map_add _ _ := rfl

def AddMonoidHom.comp [IsAddZeroClass M₀] [IsAddZeroClass N₀] [IsAddZeroClass O₀] (g: N₀ →+ O₀) (f: M₀ →+ N₀) : M₀ →+ O₀ where
  toFun := g.toFun ∘ f.toFun
  map_zero := by
    dsimp
    rw [f.map_zero, g.map_zero]
  map_add x y := by
    dsimp
    rw [f.map_add, g.map_add]

def OneHom.id : OneHom M M where
  toFun := _root_.id
  map_one := rfl

def OneHom.comp (g: OneHom N₀ O₀) (f: OneHom M₀ N₀) : OneHom M₀ O₀ where
  toFun := g.toFun ∘ f.toFun
  map_one := by
    dsimp
    rw [f.map_one, g.map_one]

def MulHom.id : M →ₙ* M where
  toFun := _root_.id
  map_mul _ _ := rfl

def MulHom.comp (g: N₀ →ₙ* O₀) (f: M₀ →ₙ* N₀) : M₀ →ₙ* O₀ where
  toFun := g.toFun ∘ f.toFun
  map_mul x y := by
    dsimp
    rw [f.map_mul, g.map_mul]

def MonoidHom.id [IsMulOneClass M] : M →* M where
  toFun := _root_.id
  map_one := rfl
  map_mul _ _ := rfl

def MonoidHom.comp [IsMulOneClass M₀] [IsMulOneClass N₀] [IsMulOneClass O₀] (g: N₀ →* O₀) (f: M₀ →* N₀) : M₀ →* O₀ where
  toFun := g.toFun ∘ f.toFun
  map_one := by
    dsimp
    rw [f.map_one, g.map_one]
  map_mul x y := by
    dsimp
    rw [f.map_mul, g.map_mul]

def ZeroHom.coe_comp (g : ZeroHom N₀ O₀) (f : ZeroHom M₀ N₀) : ↑(g.comp f) = g ∘ f := rfl
def AddHom.coe_comp (g : N₀ →ₙ+ O₀) (f : M₀ →ₙ+ N₀) : ↑(g.comp f) = g ∘ f := rfl
def AddMonoidHom.coe_comp [IsAddZeroClass M₀] [IsAddZeroClass N₀] [IsAddZeroClass O₀] (g : N₀ →+ O₀) (f : M₀ →+ N₀) : ↑(g.comp f) = g ∘ f := rfl
def OneHom.coe_comp (g : OneHom N₀ O₀) (f : OneHom M₀ N₀) : ↑(g.comp f) = g ∘ f := rfl
def MulHom.coe_comp (g : N₀ →ₙ* O₀) (f : M₀ →ₙ* N₀) : ↑(g.comp f) = g ∘ f := rfl
def MonoidHom.coe_comp [IsMulOneClass M₀] [IsMulOneClass N₀] [IsMulOneClass O₀] (g : N₀ →* O₀) (f : M₀ →* N₀) : ↑(g.comp f) = g ∘ f := rfl

section NonUnitalRingHom

variable [IsNonUnitalNonAssocSemiring M] [IsNonUnitalNonAssocSemiring N] [IsNonUnitalNonAssocSemiring M₀] [IsNonUnitalNonAssocSemiring N₀] [IsNonUnitalNonAssocSemiring O₀]

structure NonUnitalRingHom [IsNonUnitalNonAssocSemiring M] [IsNonUnitalNonAssocSemiring N] extends M →ₙ* N, M →+ N where

infixr:25 " →ₙ+* " => NonUnitalRingHom

instance : FunLike (M →ₙ+* N) M N where
  coe x := x.toFun
  coe_inj := hom_coe_inj

class IsNonUnitalRingHom [IsNonUnitalNonAssocSemiring M₀] [IsNonUnitalNonAssocSemiring N₀] extends IsMulHom F, IsAddMonoidHom F: Prop where

instance : IsNonUnitalRingHom (M →ₙ+* N) where
  map_zero x := x.map_zero
  map_add x := x.map_add
  map_mul x := x.map_mul

def IsNonUnitalRingHom.toNonUnitalRingHom [IsNonUnitalRingHom F] (f: F) : M₀ →ₙ+* N₀ where
  toFun := f
  map_zero := map_zero _
  map_mul := map_mul _
  map_add := map_add _

instance IsNonUnitalRingHom.coeNonUnitalRingHom [IsNonUnitalRingHom F] : CoeTC F (M₀ →ₙ+* N₀) where
  coe := IsNonUnitalRingHom.toNonUnitalRingHom _

 end NonUnitalRingHom

section RingHom

variable [IsNonAssocSemiring M] [IsNonAssocSemiring N] [IsNonAssocSemiring M₀] [IsNonAssocSemiring N₀] [IsNonAssocSemiring O₀]

structure RingHom [IsNonAssocSemiring M] [IsNonAssocSemiring N] extends M →* N, M →+ N where

infixr:25 " →+* " => RingHom

instance : FunLike (M →+* N) M N where
  coe x := x.toFun
  coe_inj := hom_coe_inj

class IsRingHom [IsNonAssocSemiring M₀] [IsNonAssocSemiring N₀] extends IsMonoidHom F, IsAddMonoidHom F: Prop where

instance : IsRingHom (M →+* N) where
  map_zero x := x.map_zero
  map_one x := x.map_one
  map_add x := x.map_add
  map_mul x := x.map_mul

def IsRingHom.toRingHom [IsRingHom F] (f: F) : M₀ →+* N₀ where
  toFun := f
  map_zero := map_zero _
  map_one := map_one _
  map_mul := map_mul _
  map_add := map_add _

instance IsRingHom.coeRingHom [IsRingHom F] : CoeTC F (M₀ →+* N₀) where
  coe := IsRingHom.toRingHom _

 end RingHom

variable {A: Type*} [Zero A] [Add A] [One A] [NatCast A] [SMul ℕ A] [∀n, OfNat A (n + 2)] [IsAddMonoidWithOne A]
variable {B: Type*} [Zero B] [Add B] [One B] [NatCast B] [SMul ℕ B] [∀n, OfNat B (n + 2)] [IsAddMonoidWithOne B]
variable {F:Type*}

def eq_natCast' [FunLike F ℕ A] [IsAddMonoidHom F] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by
    rw [map_zero, ←natCast_zero]
  | n + 1 => by rw [map_add, h1, eq_natCast' f h1 n, Nat.add_one, ←natCast_succ]

variable [Mul A] [IsNonAssocSemiring A]

def eq_natCast [FunLike F ℕ A] [IsRingHom F] (f : F) : ∀ n, f n = n :=
  eq_natCast' f <| map_one f

theorem map_natCast' [FunLike F A B] [IsAddMonoidHom F]
    (f : F) (h : f 1 = 1) :
    ∀ n : ℕ, f n = n
  | 0 => by
    unfold Nat.cast
    rw [natCast_zero, map_zero, natCast_zero]
  | n + 1 => by
    unfold Nat.cast
    rw [natCast_succ, natCast_succ, map_add, h, map_natCast']
    assumption

def map_natCast [IsNonAssocSemiring M₀] [IsNonAssocSemiring N₀] [IsRingHom F₀] (f : F₀) : ∀ n : ℕ, f (n : M₀) = n :=
  map_natCast' f <| map_one f

def map_neg [IsRing M₀] [IsRing N₀] [IsRingHom F₀] (f: F₀) (a: M₀) : f (-a) = -f a := by
  have := map_add f (-a) a
  rw [neg_add_cancel a, map_zero] at this
  symm
  apply neg_eq_of_add_left
  rw [add_comm]
  symm
  assumption

def map_sub [IsRing M₀] [IsRing N₀] [IsRingHom F₀] (f: F₀) (a b: M₀) : f (a - b) = f a - f b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ←map_neg, ←map_add]

variable {A: Type*} [Mul A] [One A] [Pow A ℕ]
variable {B: Type*} [Mul B] [One B] [Pow B ℕ]

theorem map_npow [IsMonoid A] [IsMonoid B] [FunLike F A B] [IsMonoidHom F] (f : F) (a : A) :
    ∀ n : ℕ, f (a ^ n) = f a ^ n
  | 0 => by rw [npow_zero, npow_zero, map_one]
  | n + 1 => by rw [npow_succ, npow_succ, map_mul, map_npow f a n]
