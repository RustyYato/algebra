import Algebra.Int.Mul
import Algebra.Algebra.Ring.Defs

inductive TrivialRing where | intro

instance : Zero TrivialRing where
  zero := ⟨⟩

instance : One TrivialRing where
  one := ⟨⟩

instance : SMul ℕ TrivialRing where
  smul _ _ := ⟨⟩

instance : Pow TrivialRing ℕ where
  pow _ _ := ⟨⟩

instance : Coe ℤ TrivialRing where
  coe _ := ⟨⟩

instance : Add TrivialRing where
  add _ _ := TrivialRing.intro

instance : Mul TrivialRing where
  mul _ _ := TrivialRing.intro

instance : Neg TrivialRing where
  neg _ := TrivialRing.intro

instance : Sub TrivialRing where
  sub _ _ := TrivialRing.intro

instance : Div TrivialRing where
  div _ _ := TrivialRing.intro

instance : SMul ℤ TrivialRing where
  smul n x := ↑n * x

instance : NatCast TrivialRing where
  natCast _ := TrivialRing.intro

instance : IntCast TrivialRing where
  intCast _ := TrivialRing.intro

instance : OfNat TrivialRing n where
  ofNat := TrivialRing.intro

instance : IsCommMagma TrivialRing where
  mul_comm _ _ := rfl

instance : IsRing TrivialRing where
  add_assoc _ _ _ := rfl
  mul_assoc _ _ _ := rfl
  add_comm _ _ := rfl
  natCast_zero := rfl
  natCast_succ _ := rfl
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast _ := rfl
  zero_mul _ := rfl
  mul_zero _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  zero_add _ := rfl
  add_zero _ := rfl
  left_distrib _ _ _ := rfl
  right_distrib _ _ _ := rfl
  neg_add_cancel _ := rfl
  intCast_negSucc _ := rfl
  intCast_ofNat _ := rfl
  sub_eq_add_neg _ _ := rfl
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl
