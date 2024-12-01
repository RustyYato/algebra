import Algebra.Equiv
import Algebra.ClassicLogic
import Algebra.WellFounded
import Algebra.QuotLike.Basic

class SUnion (α: Type _) where
  sUnion : α -> α
class SInter (α: Type _) (β: outParam (Type _)) where
  sInter : α -> β

prefix:900 "⋃₀" => SUnion.sUnion
prefix:900 "⋂₀" => SInter.sInter

inductive Zf.Pre.{u} where
| intro (α: Type u) (mem: α -> Zf.Pre)

def Zf.Pre.ty : Zf.Pre.{u} -> Type u
| .intro a _ => a
def Zf.Pre.mem : (a: Zf.Pre.{u}) -> a.ty -> Zf.Pre.{u}
| .intro _ amem => amem

def Zf.Pre.Equiv.{u,v} : Zf.Pre.{u} -> Zf.Pre.{v} -> Prop
| .intro _ amem, .intro _ bmem =>
  (∀a₀, ∃b₀, Zf.Pre.Equiv (amem a₀) (bmem b₀)) ∧
  (∀b₀, ∃a₀, Zf.Pre.Equiv (amem a₀) (bmem b₀))

def Zf.Pre.Equiv.left' : ∀{a b}, Pre.Equiv a b -> (∀a₀, ∃b₀, Zf.Pre.Equiv (a.mem a₀) (b.mem b₀))
| .intro _ _, .intro _ _, .intro a _ => a
def Zf.Pre.Equiv.right' : ∀{a b}, Pre.Equiv a b -> (∀b₀, ∃a₀, Zf.Pre.Equiv (a.mem a₀) (b.mem b₀))
| .intro _ _, .intro _ _, .intro _ b => b

inductive Zf.Pre.Mem.{u,v} (a: Zf.Pre.{u}) : Zf.Pre.{v} -> Prop where
| intro (b₀: β) : Equiv a (bmem b₀) -> Mem a (.intro β bmem)

instance Zf.Pre.MembershipInst : Membership Zf.Pre Zf.Pre := ⟨flip Zf.Pre.Mem⟩

def Zf.Pre.mem_iff { a b: Zf.Pre } : (b ∈ a) ↔ ∃a₀: a.ty, b.Equiv (a.mem a₀) :=by
  cases a; cases b
  apply Iff.intro
  repeat (
    intro ⟨a₀,prf⟩
    exists a₀
  )

@[refl]
def Zf.Pre.Equiv.refl (a: Zf.Pre) : Equiv a a := by
    induction a with
    | intro α mem ih =>
    apply And.intro
    intro a₀
    exists  a₀
    apply ih
    intro b₀
    exists  b₀
    apply ih
@[symm]
def Zf.Pre.Equiv.symm {a b: Zf.Pre} : Equiv a b -> Equiv b a := by
    induction a generalizing b with
    | intro a amem ih =>
    cases b with
    | intro b bmem =>
    intro ⟨ab,ba⟩
    apply And.intro
    intro b₀
    have ⟨a₀,prf⟩ := ba b₀
    exists a₀
    apply ih
    assumption
    intro a₀
    have ⟨b₀,prf⟩ := ab a₀
    exists b₀
    apply ih
    assumption
def Zf.Pre.Equiv.trans {a b c: Zf.Pre} : Equiv a b -> Equiv b c -> Equiv a c := by
    revert b c
    induction a with
    | intro a amem ih =>
    intro ⟨b,bmem⟩ ⟨c,cmem⟩ ⟨ab,ba⟩ ⟨bc,cb⟩
    apply And.intro
    intro a₀
    have ⟨b₀,ab⟩  := ab a₀
    have ⟨c₀,bc⟩  := bc b₀
    exists c₀
    apply ih _ ab bc
    intro c₀
    have ⟨b₀,cb⟩  := cb c₀
    have ⟨a₀,ba⟩  := ba b₀
    exists a₀
    apply ih _ ba cb

def Zf.Pre.Equivalence : Equivalence Zf.Pre.Equiv where
  refl := .refl
  symm := .symm
  trans := .trans

instance Zf.Pre.setoid : Setoid Zf.Pre where
  r := Zf.Pre.Equiv
  iseqv := Zf.Pre.Equivalence

@[refl]
def HasEquiv.Equiv.refl [s: Setoid α] (a: α) : a ≈ a := s.iseqv.refl a
@[symm]
def HasEquiv.Equiv.symm [s: Setoid α] {a b: α} : a ≈ b -> b ≈ a := s.iseqv.symm
def HasEquiv.Equiv.trans [s: Setoid α] {a b c: α} : a ≈ b -> b ≈ c -> a ≈ c := s.iseqv.trans

def Zf := Equiv Zf.Pre.setoid
instance : QuotientLike Zf.Pre.setoid Zf := instQuotientLikeEquiv

local notation "⟦" a "⟧" => (QuotLike.mk (a: Zf.Pre): Zf)

def Zf.Mem.{u,v} : Zf.{u} -> Zf.{v} -> Prop := by
  apply quot.liftProp₂ Zf.Pre.Mem
  intro a b c d a_eq_c b_eq_d mem
  replace a_eq_c : Zf.Pre.Equiv a c := a_eq_c
  cases mem
  rename_i B bmem b₀ eqv
  cases d with
  | intro D dmem =>
  have ⟨d₀, prf⟩ := b_eq_d.left b₀
  apply Zf.Pre.Mem.intro d₀
  exact (a_eq_c.symm.trans eqv).trans prf

instance Zf.MembershipInst.{u} : Membership Zf.{u} Zf.{u} := ⟨flip Zf.Mem⟩

def Zf.mem.def (a b: Zf) : (a ∈ b) = Zf.Mem a b := rfl
def Zf.mk_mem {a b: Zf.Pre} : ⟦a⟧ ∈ ⟦b⟧ ↔ a ∈ b := by
  rw [mem.def]
  unfold Mem
  apply quot.liftProp₂_mk

def Zf.Pre.ulift.{u,v} : Zf.Pre.{u} -> Zf.Pre.{max u v}
| .intro a amem => Zf.Pre.intro (ULift.{v,u} a) (fun x => (amem x.down).ulift)

def Zf.Pre.ulift_equiv.{u,v} (a: Zf.Pre.{u}) : Equiv (Zf.Pre.ulift.{u,v} a) a := by
  induction a with
  | intro a amem ih =>
  apply And.intro
  · intro ⟨a₀⟩
    exists a₀
    apply ih
  · intro a₀
    exists ⟨a₀⟩
    apply ih

def Zf.Pre.ext (a: Zf.Pre.{u}) (b: Zf.Pre.{v}) : (∀x: Zf.Pre.{max u v}, x ∈ a ↔ x ∈ b) -> Equiv a b := by
  intro ext
  cases a with
  | intro a amem =>
  cases b with
  | intro b bmem =>
  apply And.intro
  · intro a₀
    have ⟨b₀,prf⟩ := (ext (amem a₀).ulift).mp ⟨a₀,Zf.Pre.ulift_equiv _⟩
    exists b₀
    exact ((Zf.Pre.ulift_equiv _).symm.trans prf)
  · intro b₀
    have ⟨a₀,prf⟩ := (ext (bmem b₀).ulift).mpr ⟨b₀,Zf.Pre.ulift_equiv _⟩
    exists a₀
    exact ((Zf.Pre.ulift_equiv _).symm.trans prf).symm

@[ext]
def Zf.ext (a b: Zf.{u}) : (∀x: Zf.{u}, x ∈ a ↔ x ∈ b) -> a = b := by
  induction a using quot.ind with | mk a =>
  induction b using quot.ind with | mk b =>
  intro ext
  apply quot.sound
  apply Zf.Pre.ext
  intro x
  apply Iff.intro
  exact (mk_mem.mp <| (ext ⟦x⟧).mp <| mk_mem.mpr ·)
  exact (mk_mem.mp <| (ext ⟦x⟧).mpr <| mk_mem.mpr ·)

def Zf.Pre.acc_equiv : @Acc Pre (· ∈ ·) a -> Zf.Pre.Equiv a b -> @Acc Zf.Pre (· ∈ ·) b := by
  intro acc ab
  induction acc generalizing b with
  | intro a acc_mem ih =>
  cases a with
  | intro a amem =>
  apply Acc.intro
  intro c c_in_b
  cases b with
  | intro b bmem =>
  have ⟨b₀,prf⟩ := c_in_b
  have ⟨a₀,a₀_eq_b₀⟩ := ab.right b₀
  apply ih _ _
  exact (prf.trans a₀_eq_b₀.symm).symm
  exists a₀

def Zf.Pre.mem_wf : @WellFounded Zf.Pre (· ∈ ·) := by
  apply WellFounded.intro
  intro a
  induction a with
  | intro a amem ih =>
  apply Acc.intro
  intro b
  intro b_in_a
  have ⟨a₀,prf⟩ := b_in_a
  apply acc_equiv (ih a₀)
  exact prf.symm

def Zf.mem_wf : @WellFounded Zf (· ∈ ·) := by
  apply WellFounded.intro
  intro a
  induction a using quot.ind with | mk a =>
  induction a using Zf.Pre.mem_wf.induction with
  | h a ih =>
  apply Acc.intro
  intro b b_in_a
  induction b using quot.ind with | mk b =>
  apply ih
  apply mk_mem.mp
  assumption

instance : WellFoundedRelation Zf where
  rel a b := a ∈ b
  wf := Zf.mem_wf

instance Zf.Pre.Subset : HasSubset Zf.Pre.{u} where
  Subset a b := ∀x: Zf.Pre.{u}, x ∈ a -> x ∈ b

instance Zf.Subset : HasSubset Zf.{u} where
  Subset a b := ∀x: Zf.{u}, x ∈ a -> x ∈ b

def Zf.mk_subset (a b: Zf.Pre) : ⟦a⟧ ⊆ ⟦b⟧ ↔ a ⊆ b := by
  apply Iff.intro
  · intro sub x x_in_a
    apply mk_mem.mp
    apply sub
    apply mk_mem.mpr
    assumption
  · intro sub x x_in_a
    induction x using quot.ind with | mk x =>
    apply mk_mem.mpr
    apply sub
    apply mk_mem.mp
    assumption

def Zf.ext_sub (a b: Zf) : a ⊆ b -> b ⊆ a -> a = b := by
  intro ab ba
  apply ext
  intro x
  exact ⟨ ab x, ba x ⟩

def Zf.mem_congr {k a b: Zf.Pre} : Zf.Pre.Equiv a b -> k ∈ a -> k ∈ b := by
  intro a_eq_b
  cases k with | intro k kmem =>
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  intro ⟨a₀,prf⟩
  have ⟨b₀,a₀_eq_b₀⟩ := a_eq_b.left a₀
  exists b₀
  exact prf.trans a₀_eq_b₀

def Zf.congr_mem {a b k: Zf.Pre} : Zf.Pre.Equiv a b -> a ∈ k -> b ∈ k := by
  intro a_eq_b
  cases k with | intro k kmem =>
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  intro ⟨k₀,prf⟩
  exists k₀
  exact a_eq_b.symm.trans prf

def Zf.sub_congr {k a b: Zf.Pre} : Zf.Pre.Equiv a b -> k ⊆ a -> k ⊆ b := by
  intro a_eq_b k_sub_a x x_mem_k
  apply mem_congr a_eq_b
  apply k_sub_a
  exact x_mem_k

def Zf.congr_sub {a b k: Zf.Pre} : Zf.Pre.Equiv a b -> a ⊆ k -> b ⊆ k := by
  intro a_eq_b k_sub_a x x_mem_b
  apply k_sub_a
  exact mem_congr a_eq_b.symm x_mem_b

def Zf.ulift.{u,v} (a: Zf.{u}) : Zf.{max u v} := by
  apply quot.lift (⟦·.ulift⟧) _ a
  dsimp
  intro a b ab
  apply quot.sound
  apply Zf.Pre.Equiv.trans
  apply Zf.Pre.ulift_equiv
  apply flip Zf.Pre.Equiv.trans
  symm
  apply Zf.Pre.ulift_equiv
  assumption

def Zf.Pre.empty : Pre := ⟨ Empty, Empty.elim ⟩
def Zf.empty : Zf := ⟦.empty⟧

instance : EmptyCollection Zf.Pre := ⟨.ulift .empty⟩
instance : EmptyCollection Zf := ⟨.ulift .empty⟩

def Zf.empty.def : ∅ = Zf.ulift .empty := rfl

def Zf.mk_empty : (∅: Zf) = ⟦∅⟧ := by
  rw [empty.def, ulift, empty, quot.lift_mk]
  apply quot.sound
  rfl

def Zf.not_mem_empty (x: Zf) : x ∉ (∅: Zf) := by
  intro mem
  induction x using quot.ind with | mk x =>
  rw [mk_empty] at mem
  replace mem := mk_mem.mp mem
  have ⟨⟨_⟩,_⟩ := mem
  contradiction

macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply Zf.not_mem_empty; assumption)

def Zf.ext_empty (x: Zf.{u}) : (∀y: Zf.{u}, y ∉ x) -> x = ∅ := by
  intro h
  apply ext
  intro a
  apply Iff.intro
  intro mem
  have := h a mem
  contradiction
  intro mem
  have := not_mem_empty a mem
  contradiction

def Zf.Pre.Nonempty.{u} (a: Zf.Pre.{u}) : Prop := ∃x: Zf.Pre.{u}, x ∈ a
def Zf.Nonempty.{u} (a: Zf.{u}) : Prop := ∃x: Zf.{u}, x ∈ a

def Zf.not_nonempty (a: Zf.{u}) : ¬a.Nonempty -> a = ∅ := fun h => ext_empty _ (not_exists.mp h)

def Zf.not_empty_nonempty : ¬Zf.Nonempty ∅ := by
  intro ⟨_,mem⟩
  have := not_mem_empty _ mem
  contradiction

def Zf.mk_nonempty (a: Zf.Pre) : ⟦a⟧.Nonempty ↔ a.Nonempty := by
  apply Iff.intro
  · intro ⟨b,mem⟩
    induction b using quot.ind with | mk b =>
    exists b
    exact mk_mem.mp mem
  · intro ⟨b,mem⟩
    exists ⟦b⟧
    exact mk_mem.mpr mem

def Class.setoid : Setoid (Zf -> Prop) where
  r a b := ∀x, a x ↔ b x
  iseqv := {
    refl := by intros; rfl
    symm := by intros _ _ h _; symm; apply h
    trans := by intros _ _ _ h g _; apply Iff.trans; apply h; apply g
  }

structure Class where
  ofEquiv :: mem : Equiv Class.setoid

def Class.ofMem (prop: Zf -> Prop) : Class := .ofEquiv (Equiv.mk setoid prop)

def Class.univ : Class := .ofMem fun _ => True
def Class.empty : Class := .ofMem fun _ => False
def Class.ofSet (z: Zf) : Class := .ofMem (· ∈ z)
def Class.isSet (a: Class) : Prop := ∃z, a = .ofSet z
def Class.ofSet_isSet (z: Zf) : Class.isSet (.ofSet z) := ⟨_,rfl⟩
def Class.isProper (a: Class) := ∀z: Zf, a ≠ .ofSet z
def Class.sound (a b: Zf -> Prop) : (∀x, a x ↔ b x) -> ofMem a = ofMem b := by
  intro h
  unfold ofMem
  rw [Equiv.sound]
  assumption

instance : EmptyCollection Class := ⟨Class.empty⟩

def Class.Mem (a b: Class) := by
  apply Equiv.liftProp' _ _ b.mem
  exact fun b => ∃z, b z ∧ a = .ofSet z
  intro x y x_eq_y
  intro ⟨z,xz,a_eq_z⟩
  exists z
  apply And.intro _ a_eq_z
  apply (x_eq_y _).mp
  assumption

instance : Membership Class Class := ⟨flip Class.Mem⟩

def Class.mem.def (a b: Class) : (a ∈ b) = Class.Mem a b := rfl
def Class.mk_mem {a: Class} {b: Zf -> Prop} :
  a ∈ (Class.ofMem b) ↔ ∃z, b z ∧ a = .ofSet z := by
  rw [mem.def, Mem, Equiv.liftProp']
  apply Equiv.liftProp_mk

def Class.mem_univ (a: Class) : a ∈ Class.univ ↔ a.isSet := by
  apply Iff.trans
  apply Class.mk_mem
  apply Iff.intro
  intro ⟨_,_,_⟩
  subst a
  exact ofSet_isSet _
  intro ⟨a,h⟩
  exists a

def Class.not_mem_empty (a: Class) : a ∉ (∅: Class) := by
  intro h
  have ⟨_,_,_⟩ := mk_mem.mp h
  assumption

def Class.empty_eq_ofSet_empty : ∅ = ofSet ∅ := by
  apply sound
  intro x
  apply Iff.intro False.elim
  exact Zf.not_mem_empty _

def Class.ofSet.inj {a b: Zf} : ofSet a = ofSet b -> a = b := by
  unfold ofSet ofMem
  intro h
  apply Zf.ext
  exact Equiv.exact _ _ (Class.ofEquiv.inj h)

def Class.ofSet_mem_ofSet {a b: Zf} : ofSet a ∈ ofSet b ↔ a ∈ b := by
  apply Iff.trans
  exact mk_mem
  apply Iff.intro
  intro ⟨z,_,h⟩
  cases ofSet.inj h
  assumption
  intro mem
  exists a

def Class.isSet_empty : isSet ∅ := ⟨_,empty_eq_ofSet_empty⟩
def Class.isProper_univ : isProper .univ := by
  intro z h
  have := (mem_univ (ofSet z)).mpr (ofSet_isSet _)
  rw [h] at this
  have : z ∈ z := ofSet_mem_ofSet.mp this
  exact Zf.mem_wf.irrefl this

def Zf.Pre.union : Zf.Pre.{u} -> Zf.Pre.{u} -> Zf.Pre.{u}
| .intro a amem, .intro b bmem => .intro (a ⊕ b) <| fun x => match x with
  | .inl x => amem x
  | .inr x => bmem x

def Zf.union : Zf.{u} -> Zf.{u} -> Zf.{u} := by
  apply quot.lift₂ (fun a b => ⟦Zf.Pre.union a b⟧)
  intro a b c d ac bd
  apply quot.sound
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  cases c with | intro c cmem =>
  cases d with | intro d dmem =>
  apply And.intro
  · intro x
    cases x <;> rename_i x
    have ⟨y,prf⟩ := ac.left x
    exists .inl y
    have ⟨y,prf⟩ := bd.left x
    exists .inr y
  · intro x
    cases x <;> rename_i x
    have ⟨y,prf⟩ := ac.right x
    exists .inl y
    have ⟨y,prf⟩ := bd.right x
    exists .inr y

instance : Union Zf.Pre := ⟨Zf.Pre.union⟩
instance : Union Zf.{u} := ⟨Zf.union.{u}⟩

def Zf.Pre.union.def (a b: Zf.Pre) : a ∪ b = Zf.Pre.union a b := rfl
def Zf.union.def (a b: Zf) : a ∪ b = Zf.union a b := rfl
def Zf.mk_union (a b: Zf.Pre) : ⟦a⟧ ∪ ⟦b⟧ = ⟦a ∪ b⟧ := by
  rw [union.def, union, quot.lift₂_mk]
  rfl

def Zf.mem_union {a b: Zf} : ∀{x: Zf}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  induction a using quot.ind with | mk a =>
  induction b using quot.ind with | mk b =>
  induction x using quot.ind with | mk x =>
  rw [mk_union]
  apply Iff.trans
  apply mk_mem
  apply flip Iff.trans
  symm
  · apply (Iff.intro _ _)
    exact x ∈ a ∨ x ∈ b
    intro h
    cases h <;> rename_i h
    exact Or.inl (mk_mem.mp h)
    exact Or.inr (mk_mem.mp h)
    intro h
    cases h <;> rename_i h
    exact Or.inl (mk_mem.mpr h)
    exact Or.inr (mk_mem.mpr h)
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply Iff.intro
  · intro mem
    have ⟨y,prf⟩ := mem
    split at prf
    exact Or.inl ⟨_,prf⟩
    exact Or.inr ⟨_,prf⟩
  · intro mem
    cases mem <;> (rename_i mem; have ⟨y,prf⟩ := mem)
    exact ⟨Sum.inl _,prf⟩
    exact ⟨Sum.inr _,prf⟩

def Zf.Pre.sep (pred: (Zf.Pre.{u} -> Prop)) : Zf.Pre.{u} -> Zf.Pre.{u}
| .intro a amem => .intro { x: a // pred (amem x) } (amem ∘ Subtype.val)

def Zf.sep (pred: (Zf.{u} -> Prop)) : Zf.{u} -> Zf.{u} := by
  apply quot.lift (fun _ => ⟦_⟧) _
  apply Zf.Pre.sep
  exact (pred ⟦·⟧)
  intro a b a_eq_b
  dsimp
  apply quot.sound
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply And.intro
  · dsimp
    intro ⟨a₀,a₀_prop⟩
    dsimp
    have ⟨b₀,prf⟩ := a_eq_b.left a₀
    rw [quot.sound prf] at a₀_prop
    exists ⟨_,a₀_prop⟩
  · dsimp
    intro ⟨b₀,b₀_prop⟩
    dsimp
    have ⟨a₀,prf⟩ := a_eq_b.right b₀
    rw [←quot.sound prf] at b₀_prop
    exists ⟨_,b₀_prop⟩

def Zf.mk_sep (pred: (Zf.{u} -> Prop)) (a: Zf.Pre) : Zf.sep pred ⟦a⟧ = ⟦Zf.Pre.sep (pred ⟦·⟧) a⟧ := by
  rw [sep, quot.lift_mk]

def Zf.mem_sep { prop: Zf -> Prop } { a: Zf } : ∀{x}, x ∈ a.sep prop ↔ x ∈ a ∧ prop x := by
  intro x
  induction a using quot.ind with | mk a =>
  induction x using quot.ind with | mk x =>
  cases a with | intro a amem =>
  -- cases x with | intro x xmem =>
  apply Iff.intro
  · intro mem
    rw [mk_sep] at mem
    have ⟨x₀,prf⟩  := mk_mem.mp mem
    apply And.intro
    apply mk_mem.mpr
    exists x₀.val
    have := x₀.property
    dsimp at this
    rw [quot.sound]
    exact this
    exact prf
  · intro mem
    rw [mk_sep]
    apply mk_mem.mpr
    have ⟨mem,prop_of_mem⟩ := mem
    have ⟨a₀,prf⟩ := mk_mem.mp mem
    rw [quot.sound prf] at prop_of_mem
    exists ⟨a₀,prop_of_mem⟩

def Zf.inter (a b: Zf.{u}) : Zf := a.sep (· ∈ b)

instance : Inter Zf := ⟨Zf.inter⟩

def Zf.inter.def (a b: Zf.{u}) : a ∩ b = a.inter b := rfl
def Zf.mem_inter {a b: Zf.{u}} : ∀{x: Zf.{u}}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := Zf.mem_sep

def Zf.Pre.powerset : Zf.Pre -> Zf.Pre
| .intro a amem => .intro (a -> Prop) <| fun prop => .intro { x: a // prop x } <| fun x => amem x.val

def Zf.Pre.mem_powerset {a: Zf.Pre} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  cases a with | intro a amem =>
  cases x with | intro x xmem =>
  apply Iff.intro
  intro ⟨prop,prf₀⟩ k ⟨x₀,prf₁⟩
  have ⟨⟨a₀,_⟩,prf₂⟩ := prf₀.left x₀
  dsimp at prf₂
  exists a₀
  exact prf₁.trans prf₂
  intro sub
  unfold powerset
  apply Zf.Pre.Mem.intro _ _
  intro a₀
  exact ∃x₀: x, Equiv (xmem x₀) (amem a₀)
  dsimp
  apply And.intro
  · intro x₀
    have ⟨a₀,prf⟩ := sub (xmem x₀) ⟨_,by rfl⟩
    apply Exists.intro _ _
    apply Subtype.mk a₀
    exists x₀
    assumption
  · intro ⟨a₀,x₀,prf⟩
    exists x₀

def Zf.powerset : Zf -> Zf := by
  apply quot.lift (fun _ => ⟦_⟧) _
  exact Zf.Pre.powerset
  intro a b a_eq_b
  dsimp
  apply ext
  intro x
  induction x using quot.ind with | mk x =>
  apply Iff.trans
  apply mk_mem
  apply flip Iff.trans
  symm
  apply mk_mem
  apply Iff.intro
  intro mem
  apply Zf.Pre.mem_powerset.mpr
  apply Zf.sub_congr a_eq_b
  exact Zf.Pre.mem_powerset.mp mem
  intro mem
  apply Zf.Pre.mem_powerset.mpr
  apply Zf.sub_congr a_eq_b.symm
  exact Zf.Pre.mem_powerset.mp mem

def Zf.mk_powerset (a: Zf.Pre) : ⟦a⟧.powerset = ⟦a.powerset⟧ := by
  rw [powerset, quot.lift_mk]

def Zf.mem_powerset {a: Zf} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  induction a using quot.ind with | mk a =>
  induction x using quot.ind with | mk x =>
  rw [mk_powerset]
  apply Iff.trans
  apply mk_mem
  apply flip Iff.trans; symm
  apply mk_subset
  exact Zf.Pre.mem_powerset

def Zf.Pre.sUnion : Zf.Pre -> Zf.Pre
| .intro a amem => .intro ((x: a) × (amem x).ty) fun ⟨a₀,b₀⟩ => (amem a₀).mem b₀

def Zf.sUnion : Zf -> Zf := by
  apply quot.lift (fun _ => ⟦_⟧) _
  exact Zf.Pre.sUnion
  dsimp
  intro a b a_eq_b
  apply quot.sound
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  unfold Zf.Pre.sUnion
  dsimp only
  apply And.intro
  intro ⟨a₀,a₁⟩
  have ⟨b₀,a₀_eq_b₀⟩ := a_eq_b.left a₀
  have ⟨b₁,a₁_eq_b₁⟩ := a₀_eq_b₀.left' a₁
  exists ⟨b₀,b₁⟩
  intro ⟨b₀,b₁⟩
  have ⟨a₀,a₀_eq_b₀⟩ := a_eq_b.right b₀
  have ⟨a₁,a₁_eq_b₁⟩ := a₀_eq_b₀.right' b₁
  exists ⟨a₀,a₁⟩

instance : SUnion Zf.Pre := ⟨.sUnion⟩
instance : SUnion Zf := ⟨.sUnion⟩

def Zf.sUnion.def (a: Zf) : ⋃₀ a = a.sUnion := rfl

def Zf.mk_sUnion (a: Zf.Pre) : ⋃₀ ⟦a⟧ = ⟦⋃₀ a⟧ := by
  rw [Zf.sUnion.def, sUnion, quot.lift_mk]
  rfl

def Zf.mem_sUnion {a: Zf.{u}} : ∀{x}, x ∈ ⋃₀a ↔ ∃a₀: Zf.{u}, a₀ ∈ a ∧ x ∈ a₀ := by
  intro x
  induction a using quot.ind with | mk a =>
  induction x using quot.ind with | mk x =>
  cases a with | intro a amem =>
  cases x with | intro x xmem =>
  rw [mk_sUnion]
  apply Iff.trans
  apply mk_mem
  apply Iff.intro
  · intro ⟨⟨a₀,a₁⟩,prf⟩
    exists ⟦amem a₀⟧
    apply And.intro
    apply mk_mem.mpr
    exists a₀
    apply mk_mem.mpr
    apply Zf.Pre.mem_iff.mpr
    exists a₁
  · intro ⟨b,b_in_a,x_in_b⟩
    induction b using quot.ind with | mk b =>
    cases b with | intro b bmem =>
    replace b_in_a := mk_mem.mp b_in_a
    replace x_in_b := mk_mem.mp x_in_b
    have ⟨a₀,prf₀⟩ := b_in_a
    have ⟨b₀,prf₁⟩ := x_in_b
    have ⟨a₁,prf⟩ := prf₀.left' b₀
    exists ⟨a₀,a₁⟩
    apply prf₁.trans
    apply prf

def Zf.sInter (a: Zf.{u}) : Zf := (⋃₀ a).sep <| fun x => ∀a₀: Zf.{u}, a₀ ∈ a -> x ∈ a₀

instance : SInter Zf Zf := ⟨.sInter⟩

def Zf.sInter.def (a: Zf) : ⋂₀ a = a.sInter := rfl

def Zf.mem_sInter.{u} {a: Zf.{u}} (h: a.Nonempty) : ∀{x: Zf.{u}}, x ∈ ⋂₀a ↔ ∀a₀: Zf.{u}, a₀ ∈ a -> x ∈ a₀ := by
  intro x
  rw [sInter.def]
  unfold sInter
  apply Iff.trans
  apply mem_sep
  apply Iff.intro
  intro ⟨_,prop⟩
  assumption
  intro prop
  apply And.intro _ prop
  have ⟨w,w_in_a⟩ := h
  apply mem_sUnion.mpr
  exists w
  apply And.intro w_in_a
  apply prop _ w_in_a

def Zf.Pre.singleton (a: Zf.Pre) : Zf.Pre := .intro Unit <| fun _ => a
def Zf.singleton : Zf -> Zf := by
  apply quot.lift (fun _ => ⟦_⟧) _
  exact .singleton
  intro a b a_eq_b
  apply quot.sound
  unfold Zf.Pre.singleton
  apply And.intro <;> (intro; exists ⟨⟩)

instance : Singleton Zf.Pre Zf.Pre := ⟨.singleton⟩
instance : Singleton Zf Zf := ⟨.singleton⟩

def Zf.singleton.def (a: Zf) : { a } = a.singleton := rfl
def Zf.mk_singleton (a: Zf.Pre) : ({ ⟦a⟧ }: Zf) = ⟦{ a }⟧ := by
  rw [singleton.def, singleton, quot.lift_mk]
  rfl

def Zf.mem_singleton {a: Zf} : ∀{x: Zf}, x ∈ ({ a }: Zf) ↔ x = a := by
  intro x
  induction a using quot.ind with | mk a =>
  induction x using quot.ind with | mk x =>
  rw [mk_singleton]
  apply Iff.trans
  apply mk_mem
  apply Iff.intro
  intro ⟨_,_⟩
  apply quot.sound; assumption
  intro
  exists ⟨⟩
  apply quot.exact (Q := Zf)
  assumption

def Zf.Pre.insert (a b: Zf.Pre) : Zf.Pre := {a} ∪ b
def Zf.insert (a b: Zf) : Zf := {a} ∪ b

instance : Insert Zf.Pre Zf.Pre := ⟨.insert⟩
instance : Insert Zf Zf := ⟨.insert⟩

def Zf.mem_insert {a b: Zf} : ∀{x: Zf}, x ∈ Insert.insert a b ↔ x = a ∨ x ∈ b := by
  intro x
  apply Iff.intro
  intro h
  cases mem_union.mp h <;> rename_i h
  apply Or.inl; apply mem_singleton.mp; assumption
  apply Or.inr; assumption
  intro h
  apply mem_union.mpr
  cases h <;> rename_i h
  apply Or.inl; apply mem_singleton.mpr; assumption
  apply Or.inr; assumption

def Zf.mem_pair {a b: Zf} : ∀{x}, x ∈ ({ a, b }: Zf) ↔ x = a ∨ x = b := by
  intro x
  apply Iff.intro
  intro h
  cases Zf.mem_insert.mp h
  apply Or.inl; assumption
  apply Or.inr; apply Zf.mem_singleton.mp; assumption
  intro h
  apply Zf.mem_insert.mpr
  cases h
  apply Or.inl; assumption
  apply Or.inr; apply Zf.mem_singleton.mpr; assumption

def Zf.mem_pair_left {a b: Zf} : a ∈ ({ a, b }: Zf) := mem_pair.mpr (Or.inl rfl)
def Zf.mem_pair_right {a b: Zf} : b ∈ ({ a, b }: Zf) := mem_pair.mpr (Or.inr rfl)

def Zf.insert_nonempty (a b: Zf) : (Insert.insert a b).Nonempty := ⟨a,Zf.mem_insert.mpr (Or.inl rfl)⟩

def Zf.sUnion_pair_eq_union (a b: Zf) : ⋃₀ {a, b} = a ∪ b := by
  apply ext
  intro x
  apply Iff.intro
  intro h
  apply mem_union.mpr
  have ⟨w,w_mem,x_mem⟩ := mem_sUnion.mp h
  cases mem_pair.mp w_mem <;> subst w
  apply Or.inl; assumption
  apply Or.inr; assumption
  intro h
  apply mem_sUnion.mpr
  cases mem_union.mp h
  exists a
  apply And.intro
  apply mem_pair.mpr
  apply Or.inl; rfl
  assumption
  exists b
  apply And.intro
  apply mem_pair.mpr
  apply Or.inr; rfl
  assumption

def Zf.sInter_pair_eq_inter (a b: Zf) : ⋂₀ ({a, b}: Zf) = a ∩ b := by
  apply ext
  intro x
  have := @mem_sInter _ (Zf.insert_nonempty a {b})
  apply Iff.intro
  intro h
  replace h := this.mp h
  apply mem_inter.mpr
  apply And.intro <;> apply h
  exact mem_pair_left
  exact mem_pair_right
  intro h
  have ⟨l,r⟩ := mem_inter.mp h
  apply this.mpr
  intro a₀ h
  cases mem_pair.mp h <;> (subst a₀; assumption)

@[refl]
def Zf.sub.refl (a: Zf) : a ⊆ a := fun _ => id
def Zf.sub.trans {a b c: Zf} : a ⊆ b -> b ⊆ c -> a ⊆ c := fun ab bc x mem => bc x (ab x mem)

def Zf.inter_sub_left (a b: Zf) : a ∩ b ⊆ a := fun _ mem => (mem_inter.mp mem).left
def Zf.inter_sub_right (a b: Zf) : a ∩ b ⊆ b := fun _ mem => (mem_inter.mp mem).right

def Zf.sub_union_left (a b: Zf) : a ⊆ a ∪ b := fun _ mem => (mem_union.mpr (.inl mem))
def Zf.sub_union_right (a b: Zf) : b ⊆ a ∪ b := fun _ mem => (mem_union.mpr (.inr mem))

def Zf.sdiff (a b: Zf) : Zf := a.sep (· ∉ b)

instance : SDiff Zf := ⟨.sdiff⟩

def Zf.sdiff.def (a b: Zf) : a \ b = a.sdiff b := rfl

def Zf.mem_sdiff {a b: Zf} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by
  intro x
  show x ∈ Zf.sdiff _ _ ↔ _
  exact mem_sep

def Zf.sdiff_eq_empty_iff_sub {a b: Zf} : a \ b = ∅ ↔ a ⊆ b := by
  apply Iff.intro
  intro h x x_in_a
  have := not_mem_empty x
  rw [←h] at this
  have := fun g: x ∉ b => this (by
    apply mem_sdiff.mpr
    apply And.intro
    assumption
    assumption)
  exact ClassicLogic.byContradiction this
  intro sub
  apply ext_empty
  intro y y_mem
  have ⟨y_in_a,y_notin_b⟩ := mem_sdiff.mp y_mem
  apply y_notin_b
  apply sub
  assumption

def Zf.Pre.map (f: Zf.Pre -> Zf.Pre) : Zf.Pre -> Zf.Pre
| .intro a amem => .intro a (fun a₀ => f (amem a₀))

def Zf.map : (Zf -> Zf) -> Zf -> Zf := by
  intro f
  apply quot.lift (fun _ => ⟦_⟧) _
  exact Zf.Pre.map (unwrapQuot ∘ f ∘ (⟦·⟧))
  dsimp
  intro a b a_eq_b
  apply quot.sound
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  unfold Pre.map
  dsimp
  apply And.intro
  · intro a₀
    have ⟨b₀,prf⟩  := a_eq_b.left a₀
    exists b₀
    dsimp
    rw [quot.sound prf]
  · intro b₀
    have ⟨a₀,prf⟩  := a_eq_b.right b₀
    exists a₀
    dsimp
    rw [quot.sound prf]

def Zf.Pre.pmap
  (P: Zf.Pre -> Prop)
  (x: Zf.Pre)
  (ph: ∀y ∈ x, P y)
  (f: (∀y, P y -> Zf.Pre)): Zf.Pre :=
  match x with
  | .intro a amem => .intro a (fun x => f (amem x) (ph _ ⟨_, by rfl⟩))

def Zf.pmap (P: Zf -> Prop) (x: Zf) (ph: ∀y ∈ x, P y) (f: (∀y, P y -> Zf)): Zf := by
  apply quot.liftWith (P := (· = x)) _ _ x
  rfl
  intro x' h
  apply ⟦x'.pmap _ _ _⟧
  intro x'
  apply P ⟦x'⟧
  intro y y_in_x
  apply ph
  subst x
  apply mk_mem.mpr
  assumption
  intro y py
  apply unwrapQuot (Q := Zf)
  apply f
  assumption
  intro a b r h₀ h₁
  apply quot.sound
  replace r : a ≈ b := r
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply And.intro
  · intro a₀
    have ⟨b₀, prf⟩ := r.left a₀
    exists b₀
    dsimp
    conv in QuotLike.mk (amem a₀) => {
      rw [quot.sound prf]
    }
  · intro b₀
    have ⟨a₀, prf⟩ := r.right b₀
    exists a₀
    dsimp
    conv in QuotLike.mk (bmem b₀) => {
      rw [←quot.sound prf]
    }

def Zf.mapAttach (x: Zf) (f: ∀y ∈ x, Zf): Zf := by
  apply x.pmap (P := (· ∈ x))
  intro
  exact id
  assumption

def Zf.mem_mapAttach {a: Zf} {f: ∀b ∈ a, Zf} : ∀{x}, x ∈ a.mapAttach f ↔ ∃b, ∃h: b ∈ a, x = f b h := by
  intro x
  induction x using quot.ind with | mk x =>
  induction a using quot.ind with | mk a =>
  cases a with | intro a amem =>
  unfold mapAttach pmap Zf.Pre.pmap
  rw [quot.liftWith_mk]
  apply Iff.trans mk_mem
  dsimp
  apply Iff.intro
  intro ⟨x₀, h⟩
  exists ⟦amem x₀⟧
  refine ⟨?_, ?_⟩
  apply mk_mem.mpr
  exists x₀
  apply Eq.trans
  apply quot.sound
  assumption
  rw [mk_unwrapQuot]
  intro ⟨b, h, prf⟩
  induction b using quot.ind with | mk b =>
  replace h := mk_mem.mp h
  obtain ⟨a₀, b_eq⟩ := h
  exists a₀
  apply quot.exact (Q := Zf)
  rw [mk_unwrapQuot, prf]
  congr 1
  apply quot.sound
  assumption

def Zf.mapAttach_nil {f: ∀b ∈ ∅, Zf} : Zf.mapAttach ∅ f = ∅ := by
  apply ext_empty
  intro x mem
  have ⟨_,mem,_⟩  := mem_mapAttach.mp mem
  exact not_mem_empty _ mem

def Zf.mapAttach_congr (a b: Zf) (h: a = b) {f: ∀b ∈ a, Zf} : a.mapAttach f = b.mapAttach (fun x g => f x (h ▸ g)) := by
  subst h
  rfl

def Zf.mapAttach_insert {f} : (Zf.insert a b).mapAttach f = Zf.insert (f a (by
  apply Zf.mem_insert.mpr (.inl rfl))) (b.mapAttach (by
  intro y mem
  apply f
  apply Zf.mem_insert.mpr
  right; assumption)) := by
  ext x
  apply Iff.intro
  · intro h
    replace ⟨x₀, h, prf⟩  := Zf.mem_mapAttach.mp h
    subst x
    cases Zf.mem_insert.mp h <;> rename_i h
    subst x₀
    apply Zf.mem_insert.mpr; left; rfl
    apply Zf.mem_insert.mpr; right
    apply Zf.mem_mapAttach.mpr
    refine ⟨_, ?_, rfl⟩
    assumption
  · intro h
    apply Zf.mem_mapAttach.mpr
    cases Zf.mem_insert.mp h <;> rename_i h
    subst x
    refine ⟨_, ?_, rfl⟩
    apply Zf.mem_insert.mpr; left; rfl
    replace ⟨b', h, _⟩  := Zf.mem_mapAttach.mp h
    subst x
    refine ⟨_, ?_, rfl⟩
    apply Zf.mem_insert.mpr
    right; assumption

def Zf.sUnion_insert : ⋃₀(Zf.insert a b) = a ∪ ⋃₀b := by
  ext x
  apply Iff.intro
  · intro h
    replace ⟨x₀, h, prf⟩  := Zf.mem_sUnion.mp h
    apply Zf.mem_union.mpr
    cases Zf.mem_insert.mp h
    subst x₀; left; assumption
    right
    apply Zf.mem_sUnion.mpr
    exists x₀
  · intro h
    apply Zf.mem_sUnion.mpr
    cases Zf.mem_union.mp h
    exists a
    apply And.intro
    apply Zf.mem_insert.mpr; left; rfl
    assumption
    rename_i h
    replace ⟨x₀, h, prf⟩ := Zf.mem_sUnion.mp h
    exists x₀
    apply And.intro
    apply Zf.mem_insert.mpr
    right; assumption
    assumption

def Zf.mk_map (f: Zf -> Zf) (a: Zf.Pre) : ⟦a⟧.map f = ⟦(a.map (unwrapQuot ∘ f ∘ (⟦·⟧)))⟧ := by
  rw [map, quot.lift_mk]

def Zf.mem_map {f: Zf -> Zf} {a: Zf} : ∀{x}, x ∈ a.map f ↔ ∃a₀ ∈ a, f a₀ = x := by
  intro x
  induction a using quot.ind with | mk a =>
  induction x using quot.ind with | mk x =>
  cases a with | intro a amem =>
  cases x with | intro x xmem =>
  rw [mk_map]
  apply Iff.intro
  intro h
  replace ⟨a₀,prf⟩ :=  mk_mem.mp h
  dsimp at prf
  exists ⟦amem a₀⟧
  apply And.intro
  apply mk_mem.mpr
  exists a₀
  rw [←mk_unwrapQuot (f _)]
  apply quot.sound
  exact prf.symm
  intro ⟨a₀,a₀_in_a, fa_eq_x⟩
  induction a₀ using quot.ind with | mk a₀ =>
  rw [←fa_eq_x]
  rw [←mk_unwrapQuot (f _)]
  apply mk_mem.mpr
  have ⟨a₁,prf⟩ := mk_mem.mp a₀_in_a
  exists a₁
  dsimp
  rw [quot.sound prf]

def Zf.sUnion_least_upper_bound (a: Zf) :
  ∀x, ⋃₀a ⊆ x ↔ ∀a₀ ∈ a, a₀ ⊆ x := by
  intro x
  apply Iff.intro
  · intro usubx a₀ a₀_in_a a₁ a₁_in_a₀
    apply fun y h hx hy => usubx y (mem_sUnion.mpr ⟨h,hx,hy⟩) <;> assumption
  · intro subx a₁ a₁_in_u
    have ⟨a₀,a₀_in_a,a₁_in_a₀⟩ := mem_sUnion.mp a₁_in_u
    apply subx <;> assumption

def Zf.sUnion_upper_bound (a: Zf) : ∀a₀ ∈ a, a₀ ⊆ ⋃₀a :=
  (Zf.sUnion_least_upper_bound a _).mp (Zf.sub.refl _)

def Zf.sInter_most_lower_bound (a: Zf) (h: a.Nonempty) :
  ∀x, x ⊆ ⋂₀a ↔ ∀a₀ ∈ a, x ⊆ a₀ := by
  intro x
  apply Iff.intro
  · intro isubx a₀ a₀_in_a a₁ a₁_in_x
    exact (mem_sInter h).mp (isubx _ a₁_in_x) a₀ a₀_in_a
  · intro subx a₁ a₁_in_u
    apply (mem_sInter h).mpr
    intro a₀ a₀_in_a
    apply subx <;> assumption

def Zf.sInter_lower_bound (a: Zf) (h: a.Nonempty) : ∀a₀ ∈ a, ⋂₀a ⊆ a₀ :=
  (Zf.sInter_most_lower_bound a h _).mp (Zf.sub.refl _)

-- ⋂₀∅ should be the collection of all sets, but that's not a set
-- and making ⋂₀ return a Class would be messy
def Zf.sInter_empty : ⋂₀ (∅: Zf) = ∅ := by
  show Zf.sInter _ = _
  apply ext_empty
  intro a a_mem_sinter
  have ⟨a_sunion,_⟩ := mem_sep.mp a_mem_sinter
  have ⟨z,z_in_empty,_⟩ := mem_sUnion.mp a_sunion
  exact not_mem_empty _ z_in_empty

def Zf.mem_inductionOn (X: Zf)
  (motive: Zf -> Prop) :
  (mem: ∀x ∈ X, (∀y ∈ X, y ∈ x -> motive y) -> (motive x)) ->
  ∀x ∈ X, motive x := by
  intro mem x x_in_X
  induction x using mem_wf.induction with
  | h x ih =>
  apply mem
  assumption
  intro y y_in_X y_in_x
  apply ih
  assumption
  assumption

def Zf.exists_min_element (Y: Zf):
  Nonempty Y ->
  ∃x ∈ Y, ∀y ∈ Y, y ∉ x :=by
  intro nonempty_Y
  apply ClassicLogic.byContradiction
  intro h
  have := Zf.mem_inductionOn Y (fun x => x ∉ Y) (by
    intro x _ ih x_in_Y
    dsimp at ih
    have := not_and.mp <| not_exists.mp h x
    have ⟨ w, h ⟩ := ClassicLogic.not_forall.mp (this x_in_Y)
    have ⟨ w_in_Y, w_in_x ⟩ := ClassicLogic.not_imp.mp h
    have := ClassicLogic.not_not.mp w_in_x
    have := ih w w_in_Y this
    contradiction)
  clear h
  dsimp at this
  have ⟨y₀,y₀_in_Y⟩ := nonempty_Y
  have := this y₀ y₀_in_Y
  contradiction

def Zf.sUnion_nil : ⋃₀ (∅: Zf) = ∅ := by
  apply ext_empty
  intro x mem
  have ⟨y₀, mem, _⟩  := mem_sUnion.mp mem
  exact not_mem_empty _ mem

def Zf.union_nil (a: Zf) : a ∪ ∅ = a := by
  ext x
  apply Iff.intro
  intro mem
  cases mem_union.mp mem <;> trivial
  intro mem
  apply mem_union.mpr
  left; assumption

def Zf.nil_union (a: Zf) : ∅ ∪ a = a := by
  ext x
  apply Iff.intro
  intro mem
  cases mem_union.mp mem <;> trivial
  intro mem
  apply mem_union.mpr
  right; assumption

def Zf.mapAttach_singleton (a: Zf) {f} : Zf.mapAttach {a} f = {f a (Zf.mem_singleton.mpr rfl)} := by
  ext x
  apply Iff.trans _ Zf.mem_singleton.symm
  apply Iff.trans Zf.mem_mapAttach
  apply Iff.intro
  intro ⟨a', h, eq⟩
  cases Zf.mem_singleton.mp h
  assumption
  intro h
  exists a
  exists Zf.mem_singleton.mpr rfl

def Zf.sUnion_singleton (a: Zf) : ⋃₀ {a} = a := by
  ext x
  apply Iff.trans Zf.mem_sUnion
  apply Iff.intro
  intro ⟨a', h, eq⟩
  cases Zf.mem_singleton.mp h
  assumption
  intro h
  exists a
  exists Zf.mem_singleton.mpr rfl

def Zf.sub_union (a b: Zf) : a ⊆ b -> a ∪ b = b := by
  intro s
  ext x
  apply Iff.trans Zf.mem_union
  apply Iff.intro
  intro h
  cases h
  apply s
  assumption
  assumption
  intro h
  right; assumption

def Zf.sub_inter (a b: Zf) : a ⊆ b -> a ∩ b = a := by
  intro s
  ext x
  apply Iff.trans Zf.mem_inter
  apply Iff.intro
  intro ⟨_, _⟩
  assumption
  intro h
  apply And.intro
  assumption
  apply s
  assumption

def Zf.union_sub (a b: Zf) : a ⊆ b -> b ∪ a = b := by
  intro s
  ext x
  apply Iff.trans Zf.mem_union
  apply Iff.intro
  intro h
  cases h
  assumption
  apply s
  assumption
  intro h
  left; assumption

def Zf.inter_sub (a b: Zf) : a ⊆ b -> b ∩ a = a := by
  intro s
  ext x
  apply Iff.trans Zf.mem_inter
  apply Iff.intro
  intro ⟨_, _⟩
  assumption
  intro h
  apply And.intro
  apply s
  assumption
  assumption
