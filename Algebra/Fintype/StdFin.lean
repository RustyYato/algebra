import Algebra.Fintype.Basic
import Algebra.Fintype.Fin

def Fin.equiv_fin: Ty.EmbedIso (fin (.ofNat n)) (Fin n) where
  fwd := fun x => Fin.mk x.val.toNat (by
    conv => { rhs; rw [←nat.ofNat_toNat n] }
    exact nat.toNat_lt x.isLt)
  rev := fun ⟨x,h⟩ => fin.mk (.ofNat x) (nat.ofNat_lt h)
  fwd_rev := by
    intro x
    dsimp
    conv => { lhs; arg 1; rw [nat.toNat_ofNat] }
    rw [fin.val_mk]
  rev_fwd := by
    intro x
    dsimp
    conv => { lhs; lhs; rw [fin.mk_val] }
    cases x
    congr
    dsimp
    rw [nat.ofNat_toNat]

instance Fin.FintypeInst : Fintype (Fin n) :=
  Fintype.of_equiv (Fin.equiv_fin)

def Fin.card (f: Fintype (Fin n)) : f.card = .ofNat n := by
  rw [←Fintype.card_of_equiv inferInstance f Fin.equiv_fin, fin.card]
