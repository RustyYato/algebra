import Init.Data.List.Basic

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
  exact: Equivalence rel -> ∀a b: α, mk a = mk b -> rel a b

opaque equiv_class_builder_inst α rel: equiv_class_builder α rel := by
  apply equiv_class_builder.build α id id
  intro; rfl
  intro; exact id
  intro eqv a b eq
  subst eq
  apply eqv.refl

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
axiom EquivUnchecked.sound { α: Sort _ } (rel: α -> α -> Prop) :
  ∀a b, rel a b -> EquivUnchecked.mk rel a = EquivUnchecked.mk rel b

example : (∀α: Type, (rel: α -> α -> Prop) -> ∀x: α, (EquivUnchecked.mk rel x).get = x) -> False := by
  intro mk_inj
  let rel := fun _ _: Bool => True
  let a := EquivUnchecked.mk rel true
  let b := EquivUnchecked.mk rel false
  have : a = b := EquivUnchecked.sound rel _ _ True.intro
  have : a.get = b.get := by rw [this]
  rw [mk_inj, mk_inj] at this
  contradiction

def Equiv (s: Setoid α) := EquivUnchecked s.r
def Equiv.mk (s: Setoid α) : α -> Equiv s := EquivUnchecked.mk s.r
def Equiv.mk' [s: Setoid α] : α -> Equiv s := EquivUnchecked.mk s.r
def Equiv.get {s: Setoid α} : Equiv s -> α := EquivUnchecked.get
def Equiv.mk_get {s: Setoid α} (q: Equiv s) : mk s q.get = q := EquivUnchecked.mk_get q
def Equiv.get.inj {s: Setoid α} : ∀a b: Equiv s, a.get = b.get -> a = b := EquivUnchecked.get.inj
def Equiv.sound {s: Setoid α} : ∀a b: α, a ≈ b -> mk s a = mk s b := EquivUnchecked.sound s.r
def Equiv.ind {s: Setoid α} {motive: Equiv s -> Prop} : (mk: ∀x, motive (mk s x)) -> ∀q, motive q := EquivUnchecked.ind
def Equiv.lift {s: Setoid α} (f: α -> β) (_all_eq: ∀a b: α, a ≈ b -> f a = f b) (q: Equiv s) : β := f q.get
def Equiv.lift₂ {s₀: Setoid α₀} {s₁: Setoid α₁} (f: α₀ -> α₁ -> β) (_all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (q₀: Equiv s₀) (q₁: Equiv s₁) : β := f q₀.get q₁.get
def Equiv.exact {s: Setoid α} : ∀a b, mk s a = mk s b -> a ≈ b := (equiv_class_builder_inst α s.r).exact s.iseqv
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
def Equiv.get_equiv { s: Setoid α } (a: α) : (mk s a).get ≈ a := by
  apply exact
  rw [mk_get]

example : ∀a b: EquivUnchecked rel, a ≠ b -> a.get ≠ b.get := by
  intro a b eq h
  apply eq
  exact EquivUnchecked.get.inj _ _ h

def squash α := EquivUnchecked (fun _ _: α => True)
def squash.mk : α -> squash α := EquivUnchecked.mk _
def squash.get : squash α -> α := EquivUnchecked.get
instance squash.instSubsingleton : Subsingleton (squash α) where
  allEq a b := by
    induction a using EquivUnchecked.ind with | mk a =>
    induction b using EquivUnchecked.ind with | mk b =>
    apply EquivUnchecked.sound
    trivial

instance Equiv.instSubsingleton [s: Setoid α] [Subsingleton α] : Subsingleton (Equiv s) where
  allEq a b := by
    induction a using Equiv.ind with | mk a =>
    induction b using Equiv.ind with | mk b =>
    rw [Subsingleton.allEq a b]
