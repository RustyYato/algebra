import Algebra.List.Perm
import Algebra.Equiv

def Multiset α := Equiv (list.perm.setoid α)
def Multiset.mk : list α -> Multiset α := Equiv.mk (list.perm.setoid α)
def Multiset.get : Multiset α -> list α := Equiv.get
def Multiset.mk_get : ∀z: Multiset α, mk z.get = z := Equiv.mk_get
def Multiset.ind { motive: Multiset α -> Prop } : (mk: ∀x, motive (mk x)) -> ∀o, motive o := Equiv.ind
def Multiset.lift : (f: list α -> β) -> (all_eq: ∀x y, x.perm y -> f x = f y) -> Multiset α -> β := fun f eq => Equiv.lift f eq
def Multiset.lift₂ : (f: list α -> list β -> Q) -> (all_eq: ∀a b c d, a.perm c -> b.perm d -> f a b = f c d) -> Multiset α -> Multiset β -> Q := fun f eq => Equiv.lift₂ f eq
def Multiset.liftProp : (f: list α -> Prop) -> (all_eq: ∀x y, x.perm y -> (f x -> f y)) -> Multiset α -> Prop := by
  intro f alleq
  apply Equiv.liftProp f
  intro a b ab
  apply Iff.intro
  apply alleq _ _ ab
  apply alleq _ _ ab.symm
def Multiset.liftProp₂ : (f: list α -> list β -> Prop) -> (all_eq: ∀a b c d, a.perm c -> b.perm d -> (f a b -> f c d)) -> Multiset α -> Multiset β -> Prop := by
  intro f alleq
  apply Equiv.liftProp₂ f
  intro a b c d ac bd
  apply Iff.intro
  apply alleq _ _ _ _ ac bd
  apply alleq _ _ _ _ ac.symm bd.symm
def Multiset.lift_mk : lift f all_eq (mk a) = f a := Equiv.lift_mk _ _ _
def Multiset.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := Equiv.lift₂_mk _ _ _ _
def Multiset.liftProp_mk : liftProp f all_eq (mk a) ↔ f a := Equiv.liftProp_mk _ _ _
def Multiset.liftProp₂_mk : liftProp₂ f all_eq (mk a) (mk b) ↔ f a b := Equiv.liftProp₂_mk _ _ _ _
def Multiset.exact : mk a = mk b -> a.perm b := Equiv.exact _ _
def Multiset.sound : a.perm b -> mk a = mk b := fun eq => Equiv.sound _ _ eq
def Multiset.exists_rep : ∀o: Multiset α, ∃p, mk p = o := Equiv.exists_rep
