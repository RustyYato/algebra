import Algebra.Algebra.Ring.Defs
import Algebra.Ty.Basic

structure Perm (α: Type _) where
  eqv: Ty.EmbedIso α α

instance : CoeFun (Perm α) (fun _ => α -> α) := ⟨(·.eqv.fwd ·)⟩

instance : Mul (Perm α) where
  mul a b := Perm.mk (a.eqv.trans b.eqv)

instance : Inv (Perm α) where
  inv a := Perm.mk a.eqv.symm

instance : Div (Perm α) where
  div a b := a * b⁻¹

instance : One (Perm α) := ⟨Perm.mk (by rfl)⟩

instance : Pow (Perm α) ℕ where
  pow := flip npowRec

instance : Pow (Perm α) ℤ where
  pow := flip zpowRec

instance : IsGroup (Perm α) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
  inv_mul_cancel a := by
    show Perm.mk (a.eqv.symm.trans a.eqv) = Perm.mk (Ty.EmbedIso.refl _)
    congr
    unfold Ty.EmbedIso.symm Ty.EmbedIso.trans Ty.EmbedIso.refl
    dsimp
    congr
    funext x
    dsimp
    rw [Ty.EmbedIso.rev_fwd]
    funext x
    dsimp
    rw [Ty.EmbedIso.rev_fwd]
