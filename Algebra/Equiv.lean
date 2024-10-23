-- The smallest equivalence relation generated by r
inductive Relation.EquivGen (r: α -> α -> Prop) : α -> α -> Prop where
| lift : r a b -> EquivGen r a b
| refl (a: α) : EquivGen r a a
| symm : EquivGen r a b -> EquivGen r b a
| trans : EquivGen r a b -> EquivGen r b c -> EquivGen r a c

def Relation.EquivGen.Equivalence (r: α -> α -> Prop) : Equivalence (Relation.EquivGen r) where
  refl := .refl
  symm := .symm
  trans := .trans

def Relation.EquivGen.iffRel {rel: α -> α -> Prop} (eqv: _root_.Equivalence rel) :
  ∀{a b}, rel a b ↔ EquivGen rel a b := by
  intro a b
  apply Iff.intro EquivGen.lift
  intro h
  induction h
  assumption
  apply eqv.refl
  apply eqv.symm; assumption
  apply eqv.trans <;> assumption

structure equiv_class_builder (α: Sort u) (rel: α -> α -> Prop) where
  build ::
  Q: Sort u

  mk: α -> Q
  get: Q -> α

  -- this addition would be unsound with EquivUnchecked.sound
  -- since it would allow you to prove that mk is injective
  -- but that is clearly incompatible with EquivUnchecked.sound
  -- so we must not ever show that mk is injective
  -- get_mk: ∀q: α, get (mk q) = q

  -- this relates get and mk in a way that doesn't imply that mk is injective
  -- this does imply that get is injective, and that is useful
  mk_get: ∀q: Q, mk (get q) = q

  ind: ∀{motive: Q -> Prop}, (ih: ∀x, motive (mk x)) -> ∀q, motive q
  exact: ∀a b: α, mk a = mk b -> Relation.EquivGen rel a b

opaque equiv_class_builder_inst α rel: equiv_class_builder α rel := by
  apply equiv_class_builder.build α id id
  intro; rfl
  intro; exact id
  intro a b eq
  subst eq
  apply Relation.EquivGen.refl

variable {rel: α -> α -> Prop}

def EquivUnchecked (rel: α -> α -> Prop) := (equiv_class_builder_inst α rel).Q
def EquivUnchecked.mk (rel: α -> α -> Prop) : α -> EquivUnchecked rel := (equiv_class_builder_inst α rel).mk
def EquivUnchecked.get : EquivUnchecked rel -> α := (equiv_class_builder_inst α rel).get
def EquivUnchecked.ind { motive: EquivUnchecked rel -> Prop } (mk: ∀x, motive (mk rel x)) (q: EquivUnchecked rel) : motive q := (equiv_class_builder_inst α rel).ind mk q
def EquivUnchecked.mk_get (q: EquivUnchecked rel) : mk rel q.get = q := (equiv_class_builder_inst α rel).mk_get q
def EquivUnchecked.get.inj : ∀a b: EquivUnchecked rel, a.get = b.get -> a = b := by
  intro a b h
  have : mk rel a.get = mk rel b.get := by rw [h]
  rw [mk_get, mk_get] at this
  exact this
def EquivUnchecked.exact : ∀a b: α, mk rel a = mk rel b -> Relation.EquivGen rel a b := (equiv_class_builder_inst α rel).exact
def EquivUnchecked.exists_rep : ∀a, ∃b, mk rel b = a := by
  intro a
  induction a using ind with | mk a =>
  exists a
axiom EquivUnchecked.sound { α: Sort _ } (rel: α -> α -> Prop) :
  ∀a b, rel a b -> EquivUnchecked.mk rel a = EquivUnchecked.mk rel b
def EquivUnchecked.get_sound :
  ∀a b: EquivUnchecked rel, rel a.get b.get -> a = b := by
  intro a b r
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  replace r := sound _ _ _ r
  rw [mk_get, mk_get] at r
  exact r
@[irreducible]
def EquivUnchecked.lift (f: α -> β) (_all_eq: ∀a b: α, r a b -> f a = f b) (q: EquivUnchecked r) : β := f q.get
example : (∀α: Type, (rel: α -> α -> Prop) -> ∀x: α, (EquivUnchecked.mk rel x).get = x) -> False := by
  intro mk_inj
  let rel := fun _ _: Bool => True
  let a := EquivUnchecked.mk rel true
  let b := EquivUnchecked.mk rel false
  have : a = b := EquivUnchecked.sound rel _ _ True.intro
  have : a.get = b.get := by rw [this]
  rw [mk_inj, mk_inj] at this
  contradiction
def EquivUnchecked.rec
    { motive: EquivUnchecked rel -> Sort _}
    (q : EquivUnchecked rel)
    (f : (a : α) → motive (EquivUnchecked.mk rel a))
    : motive q := by
    rw [←mk_get q]
    apply f

def Equiv (s: Setoid α) := EquivUnchecked s.r
def Equiv.mk (s: Setoid α) : α -> Equiv s := EquivUnchecked.mk s.r
def Equiv.mk' [s: Setoid α] : α -> Equiv s := EquivUnchecked.mk s.r
def Equiv.get {s: Setoid α} : Equiv s -> α := EquivUnchecked.get
def Equiv.mk_get {s: Setoid α} (q: Equiv s) : mk s q.get = q := EquivUnchecked.mk_get q
def Equiv.get.inj {s: Setoid α} : ∀a b: Equiv s, a.get = b.get -> a = b := EquivUnchecked.get.inj
def Equiv.sound {s: Setoid α} : ∀a b: α, a ≈ b -> mk s a = mk s b := EquivUnchecked.sound s.r
def Equiv.ind {s: Setoid α} {motive: Equiv s -> Prop} : (mk: ∀x, motive (mk s x)) -> ∀q, motive q := EquivUnchecked.ind
@[irreducible]
def Equiv.lift {s: Setoid α} (f: α -> β) (_all_eq: ∀a b: α, a ≈ b -> f a = f b) (q: Equiv s) : β := f q.get
@[irreducible]
def Equiv.lift₂ {s₀: Setoid α₀} {s₁: Setoid α₁} (f: α₀ -> α₁ -> β) (_all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (q₀: Equiv s₀) (q₁: Equiv s₁) : β := f q₀.get q₁.get
@[irreducible]
def Equiv.liftProp {s: Setoid α} (f: α -> Prop) (_all_eq: ∀a b: α, a ≈ b -> (f a ↔ f b)) (q: Equiv s) : Prop := f q.get
@[irreducible]
def Equiv.liftProp' {s: Setoid α} (f: α -> Prop) (all_eq: ∀a b: α, a ≈ b -> (f a -> f b)) (q: Equiv s) : Prop :=
  liftProp f (by
    intro a b a_eq_b
    apply Iff.intro
    apply all_eq <;> assumption
    apply all_eq <;> (apply s.iseqv.symm; assumption))
    q
@[irreducible]
def Equiv.liftProp₂ {s₀: Setoid α₀} {s₁: Setoid α₁} (f: α₀ -> α₁ -> Prop) (_all_eq: ∀a b c d, a ≈ c -> b ≈ d -> (f a b ↔ f c d)) (q₀: Equiv s₀) (q₁: Equiv s₁) : Prop := f q₀.get q₁.get
def Equiv.exact {s: Setoid α} : ∀a b, mk s a = mk s b -> a ≈ b :=
  fun _ _ h => (Relation.EquivGen.iffRel s.iseqv).mpr <| EquivUnchecked.exact _ _ h
def Equiv.exact_get {s: Setoid α} : ∀a b: Equiv s, a = b -> a.get ≈ b.get := by
  intro a b h
  subst h
  exact s.iseqv.refl _
def Equiv.lift_mk {s: Setoid α} (f: α -> β) (all_eq: ∀a b: α, a ≈ b -> f a = f b) (a: α) :
  lift f all_eq (mk s a) = f a := by
  unfold lift
  apply all_eq
  apply exact
  rw [mk_get]
def Equiv.lift₂_mk {s₀: Setoid α₀} {s₁: Setoid α₁} (f: α₀ -> α₁ -> β) (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a: α₀) (b: α₁) :
  lift₂ f all_eq (mk s₀ a) (mk s₁ b) = f a b := by
  unfold lift₂
  apply all_eq
  apply exact
  rw [mk_get]
  apply exact
  rw [mk_get]
def Equiv.liftProp_mk {s: Setoid α} (f: α -> Prop) (all_eq: ∀a b: α, a ≈ b -> (f a ↔ f b)) (a: α) :
  liftProp f all_eq (mk s a) ↔ f a := by
  unfold liftProp
  apply all_eq
  apply exact
  rw [mk_get]
def Equiv.liftProp₂_mk {s₀: Setoid α₀} {s₁: Setoid α₁} (f: α₀ -> α₁ -> Prop) (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> (f a b ↔ f c d)) (a: α₀) (b: α₁) :
  liftProp₂ f all_eq (mk s₀ a) (mk s₁ b) ↔ f a b := by
  unfold liftProp₂
  apply all_eq
  apply exact
  rw [mk_get]
  apply exact
  rw [mk_get]
def Equiv.get_equiv { s: Setoid α } (a: α) : (mk s a).get ≈ a := by
  apply exact
  rw [mk_get]
def Equiv.exists_rep : ∀a, ∃b, mk s b = a := EquivUnchecked.exists_rep
def Equiv.get_sound { s: Setoid α } :
  ∀a b:  Equiv s, a.get ≈ b.get -> a = b := EquivUnchecked.get_sound

example : ∀a b: EquivUnchecked rel, a ≠ b -> a.get ≠ b.get := by
  intro a b eq h
  apply eq
  exact EquivUnchecked.get.inj _ _ h

instance Equiv.instSubsingleton [s: Setoid α] [Subsingleton α] : Subsingleton (Equiv s) where
  allEq a b := by
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    rw [Subsingleton.allEq a b]

def squash.setoid α : Setoid α where
  r _ _ := True
  iseqv := {
    refl := fun _ => True.intro
    symm := fun _ => True.intro
    trans := fun _ _ => True.intro
  }
def squash α := Equiv (squash.setoid α)
def squash.mk : α -> squash α := Equiv.mk _
def squash.get : squash α -> α := Equiv.get
instance squash.instSubsingleton : Subsingleton (squash α) where
  allEq a b := by
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    apply Equiv.sound
    trivial

def ident.setoid α : Setoid α where
  r a b := a = b
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₀ h₁ => h₀.trans h₁
  }
def ident α := Equiv (ident.setoid α)
def ident.mk : α -> ident α := Equiv.mk _
def ident.get : ident  α -> α := Equiv.get
def ident.mk.inj : ∀a b: α, mk a = mk b -> a = b := Equiv.exact
def ident.get.inj : ∀a b: ident α, a.get = b.get -> a = b := Equiv.get.inj
