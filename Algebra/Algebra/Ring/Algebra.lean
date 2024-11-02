import Algebra.Algebra.Ring.Hom

variable (R: Type*) [Zero R] [One R] [Add R] [Mul R] [Sub R] [Div R]
variable [Pow R ℕ] [SMul ℕ R]
variable [Pow R ℤ] [SMul ℤ R]
variable [Neg R] [Inv R]
variable [NatCast R] [IntCast R] [∀n, OfNat R (n+2)]

variable (A: Type*) [Zero A] [One A] [Add A] [Mul A] [Sub A] [Div A]
variable [Pow A ℕ] [SMul ℕ A]
variable [Pow A ℤ] [SMul ℤ A]
variable [Neg A] [Inv A]
variable [NatCast A] [IntCast A] [∀n, OfNat A (n+2)]

variable {R₀: Type*} [Zero R₀] [One R₀] [Add R₀] [Mul R₀] [Sub R₀] [Div R₀]
variable [Pow R₀ ℕ] [SMul ℕ R₀]
variable [Pow R₀ ℤ] [SMul ℤ R₀]
variable [Neg R₀] [Inv R₀]
variable [NatCast R₀] [IntCast R₀] [∀n, OfNat R₀ (n+2)]

variable {A₀: Type*} [Zero A₀] [One A₀] [Add A₀] [Mul A₀] [Sub A₀] [Div A₀]
variable [Pow A₀ ℕ] [SMul ℕ A₀]
variable [Pow A₀ ℤ] [SMul ℤ A₀]
variable [Neg A₀] [Inv A₀]
variable [NatCast A₀] [IntCast A₀] [∀n, OfNat A₀ (n+2)]

class HasRingHom [IsNonAssocSemiring R] [IsNonAssocSemiring A] where
  ring_hom : R →+* A

/-- Embedding `R →+* A` given by `Algebra` structure. -/
def algebraMap [IsNonAssocSemiring R] [IsNonAssocSemiring A] [h: HasRingHom R A] : R →+* A := h.ring_hom

class IsAlgebra [IsCommMagma R] [IsSemiring R] [IsSemiring A] [SMul R A] [HasRingHom R A] : Prop where
  commutes : ∀r x, algebraMap R A r * x = x * algebraMap R A r
  smul_def : ∀r x, r • x = algebraMap R A r * x

namespace algebraMap

variable [IsCommMagma R] [IsSemiring R] [IsSemiring A] [SMul R A] [HasRingHom R A] [IsAlgebra R A]
variable [IsCommMagma R₀] [IsSemiring R₀] [IsSemiring A₀] [SMul R₀ A₀] [HasRingHom R₀ A₀] [IsAlgebra R₀ A₀]

@[coe, reducible]
def cast : R₀ -> A₀ := algebraMap R₀ A₀

end algebraMap

namespace Semiring

variable [IsCommMagma R] [IsSemiring R] [IsSemiring A] [SMul R A] [HasRingHom R A] [IsAlgebra R A]
variable [IsCommMagma R₀] [IsSemiring R₀] [IsSemiring A₀] [SMul R₀ A₀] [HasRingHom R₀ A₀] [IsAlgebra R₀ A₀]

scoped instance coeHTCT : CoeHTCT R A := ⟨algebraMap.cast⟩

def coe_zero : ↑(0: R₀) = (0: A₀) := by apply map_zero
def coe_one : ↑(1: R₀) = (1: A₀) := by apply map_one
def coe_natCast (n: ℕ) : ↑(n: R₀) = (n: A₀) := by apply map_natCast
def coe_add (a b: R₀) : ↑(a + b: R₀) = (a + b: A₀) := by apply map_add
def coe_mul (a b: R₀) : ↑(a * b: R₀) = (a * b: A₀) := by apply map_mul
def coe_npow (a: R₀) (n: ℕ) : ↑(a ^ n: R₀) = (a ^ n: A₀) := by apply map_npow

end Semiring

namespace Ring

variable [IsCommMagma R] [IsRing R] [IsRing A] [SMul R A] [HasRingHom R A] [IsAlgebra R A]
variable [IsCommMagma R₀] [IsRing R₀] [IsRing A₀] [SMul R₀ A₀] [HasRingHom R₀ A₀] [IsAlgebra R₀ A₀]

scoped instance coeHTCT : CoeHTCT R A := ⟨algebraMap.cast⟩

def coe_neg (a: R₀) : ↑(-a: R₀) = (-a: A₀) := by apply map_neg
def coe_sub (a b: R₀) : ↑(a - b: R₀) = (a - b: A₀) := by apply map_sub

end Ring
