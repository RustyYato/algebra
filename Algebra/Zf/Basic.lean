import Algebra.Equiv

inductive Zf.Pre.{u} where
| intro (α: Type u) (mem: α -> Zf.Pre)

def Zf.Pre.Equiv.{u,v} : Zf.Pre.{u} -> Zf.Pre.{v} -> Prop
| .intro _ amem, .intro _ bmem =>
  (∀a₀, ∃b₀, Zf.Pre.Equiv (amem a₀) (bmem b₀)) ∧
  (∀b₀, ∃a₀, Zf.Pre.Equiv (amem a₀) (bmem b₀))

inductive Zf.Pre.Mem.{u,v} (a: Zf.Pre.{u}) : Zf.Pre.{v} -> Prop where
| intro (b₀: β) : Equiv a (bmem b₀) -> Mem a (.intro β bmem)

instance Zf.Pre.MembershipInst : Membership Zf.Pre Zf.Pre := ⟨Zf.Pre.Mem⟩

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

instance Zf.MembershipInst.{u,v} : Membership Zf.{u} Zf.{v} := ⟨Zf.Mem⟩

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
