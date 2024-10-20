import Algebra.Equiv

class SUnion (α: Type _) where
  sUnion : α -> α
class SInter (α: Type _) where
  sInter : α -> α

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

instance Zf.Pre.MembershipInst : Membership Zf.Pre Zf.Pre := ⟨Zf.Pre.Mem⟩

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
def Zf.mk : Zf.Pre -> Zf := Equiv.mk Zf.Pre.setoid
def Zf.ind { motive: Zf -> Prop } : (mk: ∀x, motive (mk x)) -> ∀o, motive o := Equiv.ind
def Zf.lift : (f: Zf.Pre -> α) -> (all_eq: ∀x y, x ≈ y -> f x = f y) -> Zf -> α := Equiv.lift
def Zf.lift₂ : (f: Zf.Pre -> Zf.Pre -> α) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> Zf -> Zf -> α := Equiv.lift₂
def Zf.liftProp : (f: Zf.Pre -> Prop) -> (all_eq: ∀x y, x ≈ y -> (f x -> f y)) -> Zf -> Prop := by
  intro f alleq
  apply Equiv.liftProp f
  intro a b ab
  apply Iff.intro
  apply alleq _ _ ab
  apply alleq _ _ ab.symm
def Zf.liftProp₂ : (f: Zf.Pre -> Zf.Pre -> Prop) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> (f a b -> f c d)) -> Zf -> Zf -> Prop := by
  intro f alleq
  apply Equiv.liftProp₂ f
  intro a b c d ac bd
  apply Iff.intro
  apply alleq _ _ _ _ ac bd
  apply alleq _ _ _ _ ac.symm bd.symm
def Zf.lift_mk : lift f all_eq (mk a) = f a := Equiv.lift_mk _ _ _
def Zf.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := Equiv.lift₂_mk _ _ _ _
def Zf.liftProp_mk : liftProp f all_eq (mk a) ↔ f a := Equiv.liftProp_mk _ _ _
def Zf.liftProp₂_mk : liftProp₂ f all_eq (mk a) (mk b) ↔ f a b := Equiv.liftProp₂_mk _ _ _ _
def Zf.exact : mk a = mk b -> a ≈ b := Equiv.exact _ _
def Zf.sound : a ≈ b -> mk a = mk b := Equiv.sound _ _
def Zf.exists_rep : ∀o, ∃p, mk p = o := Equiv.exists_rep

def Zf.Mem.{u,v} : Zf.{u} -> Zf.{v} -> Prop := by
  apply liftProp₂ Zf.Pre.Mem
  intro a b c d a_eq_c b_eq_d mem
  replace a_eq_c : Zf.Pre.Equiv a c := a_eq_c
  cases mem
  rename_i B bmem b₀ eqv
  cases d with
  | intro D dmem =>
  have ⟨d₀, prf⟩ := b_eq_d.left b₀
  apply Zf.Pre.Mem.intro d₀
  exact (a_eq_c.symm.trans eqv).trans prf

instance Zf.MembershipInst.{u} : Membership Zf.{u} Zf.{u} := ⟨Zf.Mem⟩

def Zf.mem.def (a b: Zf) : (a ∈ b) = Zf.Mem a b := rfl
def Zf.mk_mem {a b: Zf.Pre} : (mk a ∈ mk b) ↔ (a ∈ b) := by
  rw [mem.def]
  unfold Mem
  apply liftProp₂_mk

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

def Zf.ext (a b: Zf.{u}) : (∀x: Zf.{u}, x ∈ a ↔ x ∈ b) -> a = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  intro ext
  apply sound
  apply Zf.Pre.ext
  intro x
  apply Iff.intro
  exact (mk_mem.mp <| (ext (mk x)).mp <| mk_mem.mpr ·)
  exact (mk_mem.mp <| (ext (mk x)).mpr <| mk_mem.mpr ·)

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
  induction a using ind with | mk a =>
  induction a using Zf.Pre.mem_wf.induction with
  | h a ih =>
  apply Acc.intro
  intro b b_in_a
  induction b using ind with | mk b =>
  apply ih
  apply mk_mem.mp
  assumption

#print axioms Zf.mem_wf

instance Zf.Pre.Subset : HasSubset Zf.Pre.{u} where
  Subset a b := ∀x: Zf.Pre.{u}, x ∈ a -> x ∈ b

instance Zf.Subset : HasSubset Zf.{u} where
  Subset a b := ∀x: Zf.{u}, x ∈ a -> x ∈ b

def Zf.mk_subset (a b: Zf.Pre) : mk a ⊆ mk b ↔ a ⊆ b := by
  apply Iff.intro
  · intro sub x x_in_a
    apply mk_mem.mp
    apply sub
    apply mk_mem.mpr
    assumption
  · intro sub x x_in_a
    induction x using ind with | mk x =>
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
  apply Zf.lift (mk ∘ Pre.ulift) _ a
  dsimp
  intro a b ab
  apply sound
  apply Zf.Pre.Equiv.trans
  apply Zf.Pre.ulift_equiv
  apply flip Zf.Pre.Equiv.trans
  symm
  apply Zf.Pre.ulift_equiv
  assumption

def Zf.Pre.empty : Pre := ⟨ Empty, Empty.elim ⟩
def Zf.empty : Zf := Zf.mk .empty

instance : EmptyCollection Zf.Pre := ⟨.ulift .empty⟩
instance : EmptyCollection Zf := ⟨.ulift .empty⟩

def Zf.empty.def : ∅ = Zf.ulift .empty := rfl

def Zf.mk_empty : ∅ = mk ∅ := by
  rw [empty.def, ulift, empty, lift_mk]
  apply sound
  rfl

def Zf.not_mem_empty (x: Zf) : x ∉ (∅: Zf) := by
  intro mem
  induction x using ind with | mk x =>
  rw [mk_empty] at mem
  replace mem := mk_mem.mp mem
  have ⟨⟨_⟩,_⟩ := mem
  contradiction

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

def Zf.not_empty_nonempty : ¬Zf.Nonempty ∅ := by
  intro ⟨_,mem⟩
  have := not_mem_empty _ mem
  contradiction

def Zf.mk_nonempty (a: Zf.Pre) : (mk a).Nonempty ↔ a.Nonempty := by
  apply Iff.intro
  · intro ⟨b,mem⟩
    induction b using ind with | mk b =>
    exists b
    exact mk_mem.mp mem
  · intro ⟨b,mem⟩
    exists mk b
    exact mk_mem.mpr mem

def Zf.Pre.union : Zf.Pre.{u} -> Zf.Pre.{u} -> Zf.Pre.{u}
| .intro a amem, .intro b bmem => .intro (a ⊕ b) <| fun x => match x with
  | .inl x => amem x
  | .inr x => bmem x

def Zf.union : Zf.{u} -> Zf.{u} -> Zf.{u} := by
  apply lift₂ (fun a b => mk (Zf.Pre.union a b))
  intro a b c d ac bd
  apply sound
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
def Zf.mk_union (a b: Zf.Pre) : mk a ∪ mk b = mk (a ∪ b) := by
  rw [union.def, union, lift₂_mk]
  rfl

def Zf.mem_union {a b: Zf} : ∀{x: Zf}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction x using ind with | mk x =>
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
  apply lift (fun _ => mk _) _
  apply Zf.Pre.sep
  exact pred ∘ mk
  intro a b a_eq_b
  dsimp
  apply sound
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply And.intro
  · dsimp
    intro ⟨a₀,a₀_prop⟩
    dsimp
    have ⟨b₀,prf⟩ := a_eq_b.left a₀
    rw [sound prf] at a₀_prop
    exists ⟨_,a₀_prop⟩
  · dsimp
    intro ⟨b₀,b₀_prop⟩
    dsimp
    have ⟨a₀,prf⟩ := a_eq_b.right b₀
    rw [←sound prf] at b₀_prop
    exists ⟨_,b₀_prop⟩

def Zf.mk_sep (pred: (Zf.{u} -> Prop)) (a: Zf.Pre) : Zf.sep pred (mk a) = mk (Zf.Pre.sep (pred ∘ mk) a) := by
  rw [sep, lift_mk]

def Zf.mem_sep { prop: Zf -> Prop } { a: Zf } : ∀{x}, x ∈ a.sep prop ↔ x ∈ a ∧ prop x := by
  intro x
  induction a using ind with | mk a =>
  induction x using ind with | mk x =>
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
    rw [sound]
    exact this
    exact prf
  · intro mem
    rw [mk_sep]
    apply mk_mem.mpr
    have ⟨mem,prop_of_mem⟩ := mem
    have ⟨a₀,prf⟩ := mk_mem.mp mem
    rw [sound prf] at prop_of_mem
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
  apply lift (fun _ => mk _) _
  exact Zf.Pre.powerset
  intro a b a_eq_b
  dsimp
  apply ext
  intro x
  induction x using ind with | mk x =>
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

def Zf.mk_powerset (a: Zf.Pre) : (mk a).powerset = mk a.powerset := by
  rw [powerset, lift_mk]

def Zf.mem_powerset {a: Zf} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  induction a using ind with | mk a =>
  induction x using ind with | mk x =>
  rw [mk_powerset]
  apply Iff.trans
  apply mk_mem
  apply flip Iff.trans; symm
  apply mk_subset
  exact Zf.Pre.mem_powerset

def Zf.Pre.sUnion : Zf.Pre -> Zf.Pre
| .intro a amem => .intro ((x: a) × (amem x).ty) fun ⟨a₀,b₀⟩ => (amem a₀).mem b₀

def Zf.sUnion : Zf -> Zf := by
  apply lift (fun _ => mk _) _
  exact Zf.Pre.sUnion
  dsimp
  intro a b a_eq_b
  apply sound
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

def Zf.mk_sUnion (a: Zf.Pre) : ⋃₀ mk a = mk (⋃₀ a) := by
  rw [Zf.sUnion.def, sUnion, lift_mk]
  rfl

def Zf.mem_sUnion {a: Zf.{u}} : ∀{x}, x ∈ ⋃₀a ↔ ∃a₀: Zf.{u}, a₀ ∈ a ∧ x ∈ a₀ := by
  intro x
  induction a using ind with | mk a =>
  induction x using ind with | mk x =>
  cases a with | intro a amem =>
  cases x with | intro x xmem =>
  rw [mk_sUnion]
  apply Iff.trans
  apply mk_mem
  apply Iff.intro
  · intro ⟨⟨a₀,a₁⟩,prf⟩
    exists mk (amem a₀)
    apply And.intro
    apply mk_mem.mpr
    exists a₀
    apply mk_mem.mpr
    apply Zf.Pre.mem_iff.mpr
    exists a₁
  · intro ⟨b,b_in_a,x_in_b⟩
    induction b using ind with | mk b =>
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

instance : SInter Zf := ⟨.sInter⟩

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
  apply lift (fun _ => mk _) _
  exact .singleton
  intro a b a_eq_b
  apply sound
  unfold Zf.Pre.singleton
  apply And.intro <;> (intro; exists ⟨⟩)

instance : Singleton Zf.Pre Zf.Pre := ⟨.singleton⟩
instance : Singleton Zf Zf := ⟨.singleton⟩

def Zf.singleton.def (a: Zf) : { a } = a.singleton := rfl
def Zf.mk_singleton (a: Zf.Pre) : { mk a } = mk { a } := by
  rw [singleton.def, singleton, lift_mk]
  rfl

def Zf.mem_singleton {a: Zf} : ∀{x: Zf}, x ∈ ({ a }: Zf) ↔ x = a := by
  intro x
  induction a using ind with | mk a =>
  induction x using ind with | mk x =>
  rw [mk_singleton]
  apply Iff.trans
  apply mk_mem
  apply Iff.intro
  intro ⟨_,_⟩
  apply sound; assumption
  intro
  exists ⟨⟩
  apply exact
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

def Zf.sInter_pair_eq_inter (a b: Zf) : ⋂₀ {a, b} = a ∩ b := by
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
