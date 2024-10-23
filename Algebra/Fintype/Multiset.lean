import Algebra.List.Perm
import Algebra.Equiv
import Algebra.AxiomBlame

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

def Multiset.Mem (x: α) : Multiset α -> Prop := by
  apply liftProp (x ∈ ·)
  intro a b a_perm_b
  exact (a_perm_b.mem x).mp

instance : Membership α (Multiset α) := ⟨Multiset.Mem⟩

def Multiset.mem.def (as: Multiset α) (x: α) : (x ∈ as) = as.Mem x := rfl

def Multiset.mk_mem (as: list α) (x: α) :
  x ∈ mk as ↔ x ∈ as := by
  rw [mem.def]
  apply liftProp_mk

def Multiset.min_count (mc: Multiset α) (x: α) (n: nat) : Prop := by
  revert mc
  apply liftProp (list.min_count x · n)
  intro a b a_perm_b
  exact list.perm.min_count a_perm_b x n

def Multiset.mk_min_count (as: list α) (x: α) (n: nat) :
  (mk as).min_count x n ↔ as.min_count x n := by apply liftProp_mk

def Multiset.Nodup : Multiset α -> Prop := by
  apply liftProp list.nodup
  intro x y a_perm_b h
  exact a_perm_b.nodup h

def Multiset.mk_nodup (as: list α)  :
  (mk as).Nodup ↔ as.nodup := by apply liftProp_mk

instance [DecidableEq α] (ms: Multiset α) : Decidable (x ∈ ms) := by
  apply EquivUnchecked.rec ms
  intro a
  exact decidable_of_iff _ (Multiset.mk_mem _ _).symm

instance [DecidableEq α] (ms: Multiset α) : Decidable (Multiset.min_count ms x n) := by
  apply EquivUnchecked.rec ms
  intro a
  exact decidable_of_iff _ (Multiset.mk_min_count _ _ _).symm

instance [DecidableEq α] (ms: Multiset α) : Decidable (Multiset.Nodup ms) := by
  apply EquivUnchecked.rec ms
  intro a
  exact decidable_of_iff _ (Multiset.mk_nodup _).symm
