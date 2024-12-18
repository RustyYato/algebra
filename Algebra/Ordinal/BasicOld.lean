import Algebra.ClassicLogic
import Algebra.Equiv
import Algebra.WellFounded

open ClassicLogic

inductive Sum.Lex (alt: α -> α -> Prop) (blt: β -> β -> Prop) : α ⊕ β -> α ⊕ β -> Prop where
| inl : alt x y -> Lex alt blt (inl x) (inl y)
| inl_inr: Lex alt blt (inl x) (inr y)
| inr : blt x y -> Lex alt blt (inr x) (inr y)

class IsWellOrder (rel: α -> α -> Prop) where
  wf: WellFounded rel
  tri: ∀a b: α, rel a b ∨ a = b ∨ rel b a
  trans: ∀a b c: α, rel a b -> rel b c -> rel a c

structure WellOrder.{u} where
  ty: Type u
  rel: ty -> ty -> Prop
  wo: IsWellOrder rel

structure Embedding (α β: Sort _) where
  f: α -> β
  -- the function is injective, this proves that β has at least as many elements as α
  inj: ∀x y, f x = f y -> x = y

structure RelEmbedding (r: α -> α -> Prop) (s: β -> β -> Prop) extends Embedding α β where
  -- f preserves relations between elements
  resp: ∀{x y}, r x y ↔ s (f x) (f y)

structure RelInitialSeg (r: α -> α -> Prop) (s: β -> β -> Prop) extends RelEmbedding r s where
  mk' ::
  init: ∀a b, s a (f b) -> ∃x, f x = a

def RelInitialSeg.mk (f: α -> β) :
  (∀x y, f x = f y -> x = y) ->
  (∀{x y}, r x y ↔ s (f x) (f y)) ->
  (∀a b, s a (f b) -> ∃x, f x = a) ->
  RelInitialSeg r s := fun inj resp init => .mk' (.mk (.mk f inj) resp) init

structure RelPrincipalSeg (r: α -> α -> Prop) (s: β -> β -> Prop) extends RelEmbedding r s where
  mk' ::
  top: β
  lt_top: ∀b, s (f b) top
  of_lt_top: ∀x, s x top -> ∃y, f y = x

def RelPrincipalSeg.mk (f: α -> β) (top: β) :
  (∀x y, f x = f y -> x = y) ->
  (∀{x y}, r x y ↔ s (f x) (f y)) ->
  (∀b, s (f b) top) ->
  (∀x, s x top -> ∃y, f y = x) ->
  RelPrincipalSeg r s := fun inj resp => .mk' (.mk (.mk f inj) resp) top

inductive WellOrder.Le : WellOrder.{u} -> WellOrder.{v} -> Prop where
| mk { r₀: α₀ -> α₀ -> Prop } { r₁: α₁ -> α₁ -> Prop } { to₀: IsWellOrder r₀ } { to₁: IsWellOrder r₁ } :
  RelInitialSeg r₀ r₁ -> Le (.mk α₀ r₀ to₀) (.mk α₁ r₁ to₁)

inductive WellOrder.Lt : WellOrder.{u} -> WellOrder.{v} -> Prop where
| mk { r₀: α₀ -> α₀ -> Prop } { r₁: α₁ -> α₁ -> Prop } { to₀: IsWellOrder r₀ } { to₁: IsWellOrder r₁ } :
  RelPrincipalSeg r₀ r₁ -> Lt (.mk α₀ r₀ to₀) (.mk α₁ r₁ to₁)

def IsWellOrder.ext {r: α -> α -> Prop} [wo: IsWellOrder r] (a b: α) :
  (∀x, r x a ↔ r x b) -> a = b := by
  intro rel_iff
  cases wo.tri a b <;> rename_i h
  have := (rel_iff _).mpr h
  have := wo.wf.irrefl this
  contradiction
  cases h <;> rename_i h
  assumption
  have := (rel_iff _).mp h
  have := wo.wf.irrefl this
  contradiction

def Embedding.refl α : Embedding α α := .mk id (fun _ _ => id)
def RelEmbedding.refl (r: α -> α -> Prop) : RelEmbedding r r := .mk (.refl _) (Iff.refl _)
def RelInitialSeg.refl (r: α -> α -> Prop) : RelInitialSeg r r := .mk' (.refl _) fun a _ _ => ⟨a,rfl⟩

def RelPrincipalSeg.toRelInitalSeg [swo: IsWellOrder s] (seg: RelPrincipalSeg r s) : RelInitialSeg r s := by
  apply RelInitialSeg.mk' seg.toRelEmbedding
  intro b a b_lt_fa
  have b_lt_top := swo.trans _ _ _ b_lt_fa (seg.lt_top a)
  have ⟨ a₀, prf ⟩ := seg.of_lt_top _ b_lt_top
  exists a₀

def RelInitialSeg.eq {r: α -> α -> Prop} [rwo: IsWellOrder r] [swo: IsWellOrder s] (a b: RelInitialSeg r s) (x: α) : a.f x = b.f x := by
  rename_i β
  induction x using rwo.wf.induction with
  | h x ih =>
  apply swo.ext
  intro y
  apply Iff.intro
  · intro y_lt_ax
    have ⟨ y₀, prf ⟩ := a.init y x y_lt_ax
    rw [←prf] at y_lt_ax
    have y₀_lt_x := a.resp.mpr y_lt_ax
    have := ih y₀ y₀_lt_x
    rw [this] at prf
    subst y
    exact b.resp.mp y₀_lt_x
  · intro y_lt_bx
    have ⟨ y₀, prf ⟩ := b.init y x y_lt_bx
    rw [←prf] at y_lt_bx
    have y₀_lt_x := b.resp.mpr y_lt_bx
    have := ih y₀ y₀_lt_x
    rw [←this] at prf
    subst y
    exact a.resp.mp y₀_lt_x

def RelInitialSeg.leSum (r: α -> α -> Prop) (s: β -> β -> Prop) :
  RelInitialSeg r (Sum.Lex r s) := by
  apply RelInitialSeg.mk Sum.inl (fun _ _ => Sum.inl.inj) _ _
  intro _ _
  apply Iff.intro
  exact Sum.Lex.inl
  intro h
  cases h
  assumption
  intro x a r
  cases r <;> rename_i x _
  exists x

def RelInitialSeg.lt_or_eq.{u,v}
  { α: Type u }
  { β: Type v }
  (r: α -> α -> Prop) (s: β -> β -> Prop)
  [rwo: IsWellOrder r] [swo: IsWellOrder s]
   :
  Nonempty (RelInitialSeg r s) ∨ Nonempty (RelInitialSeg s r) := by
  sorry

def RelInitialSeg.total.{u,v}
  { α: Type u }
  { β: Type v }
  (r: α -> α -> Prop) (s: β -> β -> Prop)
  [rwo: IsWellOrder r] [swo: IsWellOrder s] :
  Nonempty (RelInitialSeg r s) ∨ Nonempty (RelInitialSeg s r) := by
  sorry

inductive WellOrder.Equiv : WellOrder.{u} -> WellOrder.{v} -> Type _ where
| mk (f: α₀ -> α₁) (g: α₁ -> α₀) :
    (∀x, f (g x) = x) ->
    (∀x, g (f x) = x) ->
    (f_resp: ∀x y, r₀ x y -> r₁ (f x) (f y)) ->
    (g_resp: ∀x y, r₁ x y -> r₀ (g x) (g y)) ->
    Equiv (.mk α₀ r₀ to₀) (.mk α₁ r₁ to₁)

@[refl]
def WellOrder.Le.refl (a: WellOrder) : Le a a := Le.mk (.mk id (fun _ _ => id) (Iff.refl _) (fun a _ _ => ⟨ a, rfl ⟩))

def WellOrder.Le.trans {a b c: WellOrder} : Le a b -> Le b c -> Le a c
| .mk ab, .mk bc => by
  apply Le.mk (.mk (bc.f ∘ ab.f) _ _ _)
  · intro x y h
    exact ab.inj _ _ (bc.inj _ _ h)
  · intro x y
    apply Iff.intro
    intro h
    apply bc.resp.mp
    apply ab.resp.mp
    exact h
    intro h
    apply ab.resp.mpr
    apply bc.resp.mpr
    exact h
  · intro a₀ b₀ r
    have ⟨ x, prf ⟩ := bc.init _ _ r
    subst a₀
    replace r := bc.resp.mpr r
    have ⟨ x, prf ⟩ := ab.init _ _ r
    subst prf
    exists x

@[refl]
def WellOrder.Equiv.refl (a: WellOrder) : Equiv a a :=
  ⟨ id, id, fun _ => rfl, fun _ => rfl, fun {_ _} => id, fun {_ _} => id ⟩

@[symm]
def WellOrder.Equiv.symm { a b: WellOrder } : Equiv a b -> Equiv b a
| .mk f g fg gf fresp gresp => .mk g f gf fg gresp fresp

@[symm]
def WellOrder.Equiv.symm_symm (ab: Equiv a b) : ab.symm.symm = ab := by
  cases ab
  rfl

def WellOrder.Equiv.trans { a b c: WellOrder } : Equiv a b -> Equiv b c -> Equiv a c
| .mk ab ba abba baab ab_resp ba_resp,
  .mk bc cb bccb cbbc bc_resp cb_resp => by
  apply Equiv.mk (bc ∘ ab) (ba ∘ cb)
  all_goals dsimp
  · intro x
    rw [abba, bccb]
  · intro x
    rw [cbbc, baab]
  · intro x y xy
    apply bc_resp
    apply ab_resp
    exact xy
  · intro x y xy
    apply ba_resp
    apply cb_resp
    exact xy

def WellOrder.Equiv.left : Equiv a b -> a.1 -> b.1
| .mk f _ _ _ _ _ => f
def WellOrder.Equiv.right : Equiv a b -> b.1 -> a.1
| .mk _ g  _ _ _ _ => g
def WellOrder.Equiv.right_left : ∀(h: Equiv a b), ∀x, h.left (h.right x) = x
| .mk _ _ prf _ _ _ => prf
def WellOrder.Equiv.left_right : ∀(h: Equiv a b), ∀x, h.right (h.left x) = x
| .mk _ _ _ prf _ _ => prf
def WellOrder.Equiv.left_resp : ∀(h: Equiv a b), ∀x y, a.2 x y -> b.2 (h.left x) (h.left y)
| .mk _ _ _ _ prf _ => prf
def WellOrder.Equiv.right_resp : ∀(h: Equiv a b), ∀x y, b.2 x y -> a.2 (h.right x) (h.right y)
| .mk _ _ _ _ _ prf => prf

def WellOrder.Equiv.left_inj (h: Equiv a b) : ∀x y, h.left x = h.left y -> x = y := by
  intro x y hx_eq_hy
  have : h.right (h.left x) = h.right (h.left y) := by rw [hx_eq_hy]
  rw [h.left_right, h.left_right] at this
  exact this

def WellOrder.Equiv.right_inj (h: Equiv a b) : ∀x y, h.right x = h.right y -> x = y := by
  intro x y hx_eq_hy
  have : h.left (h.right x) = h.left (h.right y) := by rw [hx_eq_hy]
  rw [h.right_left, h.right_left] at this
  exact this

def WellOrder.Equiv.le_left (h: Equiv a b) : Le a b := by
  apply Le.mk (.mk _ _ _ _)
  · exact h.left
  · exact h.left_inj
  · intro x y
    apply Iff.intro
    intro r
    apply h.left_resp
    assumption
    intro r
    have := h.right_resp _ _ r
    rw [h.left_right, h.left_right] at this
    exact this
  · intro b₀ a₀ _
    exists h.right b₀
    rw [h.right_left]
def WellOrder.Equiv.le_right (h: Equiv a b) : Le b a := h.symm.le_left

instance WellOrder.setoid : Setoid WellOrder where
  r a b := Nonempty (Equiv a b)
  iseqv := {
    refl := fun a => Nonempty.intro (.refl a)
    symm := fun ⟨ ab ⟩ => Nonempty.intro (.symm ab)
    trans := fun ⟨ ab ⟩ ⟨ bc ⟩  => Nonempty.intro (.trans ab bc)
  }

@[refl]
def Ordinal.Equiv.refl (a: WellOrder) : a ≈ a := by
  exact ⟨.refl _⟩
@[symm]
def Ordinal.Equiv.symm {a b: WellOrder} : a ≈ b -> b ≈ a := by
  intro ⟨ab⟩
  exact ⟨ab.symm⟩
def Ordinal.Equiv.trans {a b c: WellOrder} : a ≈ b -> b ≈ c -> a ≈ c := by
  intro ⟨ab⟩ ⟨bc⟩
  exact ⟨ab.trans bc⟩

def Ordinal := Equiv WellOrder.setoid
def Ordinal.mk : WellOrder -> Ordinal := Equiv.mk WellOrder.setoid
def Ordinal.ind { motive: Ordinal -> Prop } : (mk: ∀x, motive (mk x)) -> ∀o, motive o := Equiv.ind
def Ordinal.lift : (f: WellOrder -> α) -> (all_eq: ∀x y, x ≈ y -> f x = f y) -> Ordinal -> α := Equiv.lift
def Ordinal.lift₂ : (f: WellOrder -> WellOrder -> α) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> Ordinal -> Ordinal -> α := Equiv.lift₂
def Ordinal.liftProp : (f: WellOrder -> Prop) -> (all_eq: ∀x y, x ≈ y -> (f x ↔ f y)) -> Ordinal -> Prop := Equiv.liftProp
def Ordinal.liftProp₂ : (f: WellOrder -> WellOrder -> Prop) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> (f a b ↔ f c d)) -> Ordinal -> Ordinal -> Prop := Equiv.liftProp₂
def Ordinal.lift_mk : lift f all_eq (mk a) = f a := Equiv.lift_mk _ _ _
def Ordinal.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := Equiv.lift₂_mk _ _ _ _
def Ordinal.liftProp_mk : liftProp f all_eq (mk a) ↔ f a := Equiv.liftProp_mk _ _ _
def Ordinal.liftProp₂_mk : liftProp₂ f all_eq (mk a) (mk b) ↔ f a b := Equiv.liftProp₂_mk _ _ _ _
def Ordinal.exact : mk a = mk b -> a ≈ b := Equiv.exact _ _
def Ordinal.sound : a ≈ b -> mk a = mk b := Equiv.sound _ _
def Ordinal.sound' : WellOrder.Equiv a b -> mk a = mk b := sound ∘ Nonempty.intro
def Ordinal.exists_rep : ∀o, ∃p, mk p = o := Equiv.exists_rep

def Ordinal.le_congr (a b c d: WellOrder) :
  a.Equiv c -> b.Equiv d ->
  a.Le b -> c.Le d := by
  intro ac bd
  intro ⟨emb⟩
  apply WellOrder.Le.mk (.mk (bd.left ∘ emb.f ∘ ac.right) _ _ _)
  · intro c₀ c₁ h
    dsimp at h
    apply ac.right_inj
    apply emb.inj
    apply bd.left_inj
    assumption
  · intro c₀ c₁
    apply Iff.intro
    intro h
    apply bd.left_resp
    apply emb.resp.mp
    apply ac.right_resp
    assumption
    intro h
    dsimp at h
    replace h := bd.right_resp _ _ h
    rw [bd.left_right, bd.left_right] at h
    replace h := emb.resp.mpr h
    replace h := ac.left_resp _ _ h
    rw [ac.right_left, ac.right_left] at h
    exact h
  · dsimp
    intro d₀ c₀ r
    replace r := bd.right_resp _ _ r
    rw [bd.left_right] at r
    have ⟨ x, prf ⟩ := emb.init (bd.right d₀) (ac.right c₀) r
    rw [←prf] at r
    replace r := emb.resp.mpr r
    replace r := ac.left_resp _ _ r
    rw [ac.right_left] at r
    exists ac.left x
    rw [ac.left_right, prf, bd.right_left]

def Ordinal.le (a b: Ordinal) : Prop := by
  apply liftProp₂ WellOrder.Le _ a b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply Iff.intro
  apply le_congr <;> assumption
  apply le_congr <;> (symm; assumption)

def Ordinal.lt_congr (a b c d: WellOrder) :
  a.Equiv c -> b.Equiv d ->
  a.Lt b -> c.Lt d := by
  intro ac bd
  intro ⟨emb⟩
  apply WellOrder.Lt.mk (.mk (bd.left ∘ emb.f ∘ ac.right) _ _ _ _ _)
  · exact bd.left emb.top
  · intro c₀ c₁ h
    dsimp at h
    apply ac.right_inj
    apply emb.inj
    apply bd.left_inj
    assumption
  · intro c₀ c₁
    apply Iff.intro
    intro h
    apply bd.left_resp
    apply emb.resp.mp
    apply ac.right_resp
    assumption
    intro h
    dsimp at h
    replace h := bd.right_resp _ _ h
    rw [bd.left_right, bd.left_right] at h
    replace h := emb.resp.mpr h
    replace h := ac.left_resp _ _ h
    rw [ac.right_left, ac.right_left] at h
    exact h
  · dsimp
    intro c₀
    apply bd.left_resp
    apply emb.lt_top
  · dsimp
    intro d₀ lt_top
    rw [←bd.right_left d₀] at lt_top
    have := bd.right_resp _ _ lt_top
    rw [bd.left_right, bd.left_right] at this
    have ⟨ y, prf ⟩ := emb.of_lt_top (bd.right d₀) this
    exists ac.left y
    rw [ac.left_right, prf, bd.right_left]

def Ordinal.lt (a b: Ordinal) : Prop := by
  apply liftProp₂ WellOrder.Lt _ a b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply Iff.intro
  apply lt_congr <;> assumption
  apply lt_congr <;> (symm; assumption)

instance : LE Ordinal := ⟨Ordinal.le⟩
def Ordinal.le.def (a b: Ordinal) : (a ≤ b) = a.le b := rfl
def Ordinal.mk_le (a b: WellOrder) : (mk a ≤ mk b) ↔ a.Le b := liftProp₂_mk

instance : LT Ordinal := ⟨Ordinal.lt⟩
def Ordinal.lt.def (a b: Ordinal) : (a < b) = a.lt b := rfl
def Ordinal.mk_lt (a b: WellOrder) : (mk a < mk b) ↔ a.Lt b := liftProp₂_mk

def ULift.up.inj.{u₀,v₀} {α: Type v₀} (a b: α) :
  (ULift.up a: ULift.{u₀,v₀} α) = ULift.up b -> a = b := by
  intro h
  rw [←ULift.down_up.{v₀,u₀} a, ←ULift.down_up.{v₀,u₀} b, h]

def ULift.down.inj (a b: ULift α) :
  a.down = b.down -> a = b := by
  intro h
  rw [←ULift.up_down a, ←ULift.up_down b, h]

def WellOrder.ulift (o: WellOrder) : WellOrder := by
  apply WellOrder.mk (ULift o.ty) _ _
  intro ⟨x⟩ ⟨y⟩
  exact o.rel x y
  apply IsWellOrder.mk <;> dsimp
  · apply WellFounded.intro
    intro ⟨x⟩
    induction x using o.wo.wf.induction with | h x ih =>
    apply Acc.intro
    intro ⟨y⟩ r
    apply ih
    assumption
  · intro ⟨x⟩ ⟨y⟩
    dsimp
    cases o.wo.tri x y <;> rename_i h
    apply Or.inl h
    apply Or.inr
    cases h <;> rename_i h
    apply Or.inl
    rw [h]
    exact Or.inr h
  · intro ⟨x⟩ ⟨y⟩ ⟨z⟩
    apply o.wo.trans

def WellOrder.ulift_equiv_self (o: WellOrder) : Equiv (ulift o) o := by
  apply Equiv.mk _ _ _ _ _ _
  exact ULift.down
  exact ULift.up
  intros; rfl
  intros; rfl
  exact fun _ _ => id
  exact fun _ _ => id

def WellOrder.ulift_equiv_left (a b: WellOrder) : Equiv a b -> Equiv (ulift a) b := by
  intro eq
  apply WellOrder.Equiv.trans
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.ulift_equiv_right (a b: WellOrder) : Equiv a b -> Equiv a (ulift b) := by
  intro eq
  apply flip WellOrder.Equiv.trans
  apply WellOrder.Equiv.symm
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.of_ulift_equiv_left (a b: WellOrder) : Equiv (ulift a) b -> Equiv a b := by
  intro eq
  apply WellOrder.Equiv.trans
  apply WellOrder.Equiv.symm
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.of_ulift_equiv_right (a b: WellOrder) : Equiv a (ulift b) -> Equiv a b := by
  intro eq
  apply flip WellOrder.Equiv.trans
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.ulift_equiv_ulift (a b: WellOrder) : Equiv a b -> Equiv (ulift a) (ulift b) := by
  intro eq
  apply ulift_equiv_left
  apply ulift_equiv_right
  exact eq

def WellOrder.Equiv.ulift_equiv_ulift (a b: WellOrder) : a ≈ b -> (ulift a) ≈ (ulift b) := by
  intro ⟨eq⟩
  apply Nonempty.intro
  apply WellOrder.ulift_equiv_ulift _ _ eq

def WellOrder.of_ulift_equiv_ulift (a b: WellOrder) : Equiv (ulift a) (ulift b) -> Equiv a b := by
  intro eq
  apply of_ulift_equiv_left
  apply of_ulift_equiv_right
  exact eq

def WellOrder.ulift_le_left.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Le a b -> Le (ulift.{u,w} a) b := by
  intro ⟨emb⟩
  apply WellOrder.Le.mk (.mk (emb.f ∘ ULift.down) _ _ _) <;> dsimp
  intro x y h
  exact ULift.down.inj _ _ (emb.inj _ _ h)
  intro x y
  exact emb.resp
  intro b₀ a₀ r
  have ⟨a₁, prf⟩  := emb.init b₀ a₀.down r
  exists ⟨a₁⟩

def WellOrder.ulift_le_right.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Le a b -> Le a (ulift.{v,w} b) := by
  intro ⟨emb⟩
  apply WellOrder.Le.mk (.mk (ULift.up ∘ emb.f) _ _ _) <;> dsimp
  intro x y h
  exact emb.inj _ _ (ULift.up.inj _ _ h)
  exact emb.resp
  intro b₀ a₀ r
  have ⟨a₁, prf⟩  := emb.init b₀.down a₀ r
  exists a₁
  rw [prf]

def WellOrder.ulift_le_ulift.{u,v,w₀,w₁} (a: WellOrder.{u}) (b: WellOrder.{v}) : Le a b -> Le (ulift.{u,w₀} a) (ulift.{v,w₁} b) := by
  intro h
  apply WellOrder.ulift_le_left
  apply WellOrder.ulift_le_right
  exact h

def WellOrder.of_ulift_le_left.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Le (ulift.{u,w} a) b -> Le a b := by
  intro ⟨emb⟩
  apply WellOrder.Le.mk (.mk (emb.f ∘ ULift.up) _ _ _) <;> dsimp
  intro x y h
  exact ULift.up.inj _ _ (emb.inj _ _ h)
  exact emb.resp
  intro b₀ a₀ r
  have ⟨x,prf⟩ := emb.init _ _ r
  exists x.down

def WellOrder.of_ulift_le_right.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Le a (ulift.{v,w} b) -> Le a b := by
  intro ⟨emb⟩
  apply WellOrder.Le.mk (.mk (ULift.down ∘ emb.f) _ _ _) <;> dsimp
  intro x y h
  exact emb.inj _ _ (ULift.down.inj _ _ h)
  exact emb.resp
  intro _ _ r
  have ⟨x,prf⟩ := emb.init _ _ r
  exists x
  rw [prf]

def WellOrder.of_ulift_le_ulift.{u,v,w₀,w₁} (a: WellOrder.{u}) (b: WellOrder.{v}) : Le a b -> Le (ulift.{u,w₀} a) (ulift.{v,w₁} b) := by
  intro h
  apply WellOrder.ulift_le_left
  apply WellOrder.ulift_le_right
  exact h

def WellOrder.ulift_lt_left.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Lt a b -> Lt (ulift.{u,w} a) b := by
  intro ⟨emb⟩
  apply WellOrder.Lt.mk (.mk (emb.f ∘ ULift.down) emb.top _ _ _ _) <;> dsimp
  intro x y h
  exact ULift.down.inj _ _ (emb.inj _ _ h)
  intro x y
  exact emb.resp
  intro; exact emb.lt_top _
  intro b₀ r
  have ⟨ y, prf ⟩  := emb.of_lt_top b₀ r
  exists ⟨y⟩

def WellOrder.ulift_lt_right.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Lt a b -> Lt a (ulift.{v,w} b) := by
  intro ⟨emb⟩
  apply WellOrder.Lt.mk (.mk (ULift.up ∘ emb.f) ⟨emb.top⟩ _ _ _ _) <;> dsimp
  intro x y h
  exact emb.inj _ _ (ULift.up.inj _ _ h)
  exact emb.resp
  intro; exact emb.lt_top _
  intro b₀ r
  have ⟨ y, prf ⟩  := emb.of_lt_top b₀.down r
  exists y
  rw [prf]

def WellOrder.ulift_lt_ulift.{u,v,w₀,w₁} (a: WellOrder.{u}) (b: WellOrder.{v}) : Lt a b -> Lt (ulift.{u,w₀} a) (ulift.{v,w₁} b) := by
  intro h
  apply WellOrder.ulift_lt_left
  apply WellOrder.ulift_lt_right
  exact h

def WellOrder.of_ulift_lt_left.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Lt (ulift.{u,w} a) b -> Lt a b := by
  intro ⟨emb⟩
  apply WellOrder.Lt.mk (.mk (emb.f ∘ ULift.up) emb.top _ _ _ _) <;> dsimp
  intro x y h
  exact ULift.up.inj _ _ (emb.inj _ _ h)
  exact emb.resp
  intro; exact emb.lt_top _
  intro b₀ r
  have ⟨ y, prf ⟩  := emb.of_lt_top b₀ r
  exists y.down

def WellOrder.of_ulift_lt_right.{u,v,w} (a: WellOrder.{u}) (b: WellOrder.{v}) : Lt a (ulift.{v,w} b) -> Lt a b := by
  intro ⟨emb⟩
  apply WellOrder.Lt.mk (.mk (ULift.down ∘ emb.f) emb.top.down _ _ _ _) <;> dsimp
  intro x y h
  exact emb.inj _ _ (ULift.down.inj _ _ h)
  exact emb.resp
  intro; exact emb.lt_top _
  intro b₀ r
  have ⟨ y, prf ⟩  := emb.of_lt_top ⟨b₀⟩ r
  exists y
  rw [prf]

def WellOrder.of_ulift_lt_ulift.{u,v,w₀,w₁} (a: WellOrder.{u}) (b: WellOrder.{v}) : Lt a b -> Lt (ulift.{u,w₀} a) (ulift.{v,w₁} b) := by
  intro h
  apply WellOrder.ulift_lt_left
  apply WellOrder.ulift_lt_right
  exact h

def Ordinal.ulift (o: Ordinal) : Ordinal := by
  apply o.lift (mk ∘ WellOrder.ulift) _
  · intro a b ⟨ab⟩
    apply sound'
    apply WellOrder.Equiv.mk _ _ _ _ _ _
    · exact ULift.up ∘ ab.left ∘ ULift.down
    · exact ULift.up ∘ ab.right ∘ ULift.down
    · intro ⟨x⟩
      dsimp
      rw [ab.right_left]
    · intro ⟨x⟩
      dsimp
      rw [ab.left_right]
    · intro ⟨x⟩ ⟨y⟩ r
      exact ab.left_resp _ _ r
    . intro ⟨x⟩ ⟨y⟩ r
      exact ab.right_resp _ _ r

def Ordinal.mk_ulift (o: WellOrder) : Ordinal.ulift.{u,v} (mk o) = mk o.ulift := by
  unfold ulift
  rw [lift_mk]
  rfl

def Ordinal.ulift_eq_self (o: Ordinal) : ulift o = o := by
  induction o using ind with | mk o =>
  unfold ulift
  rw [lift_mk]
  dsimp
  apply sound'
  apply WellOrder.ulift_equiv_self

def WellOrder.empty : WellOrder := by
  apply WellOrder.mk Empty
  apply IsWellOrder.mk
  apply WellFounded.intro
  repeat exact fun x => x.elim
def Ordinal.empty : Ordinal := Ordinal.mk WellOrder.empty

def Ordinal.unit : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk Unit (fun _ _ => False)
  apply IsWellOrder.mk
  apply WellFounded.intro
  intro
  apply Acc.intro
  intro _ _
  contradiction
  intro a b
  apply Or.inr
  apply Or.inl
  rfl
  intros
  contradiction

def Ordinal.bool : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk Bool (fun a b => a < b)
  apply IsWellOrder.mk
  apply WellFounded.intro
  intro x
  apply Acc.intro
  intro y r
  cases x <;> cases y
  any_goals contradiction
  apply Acc.intro
  intro z _
  cases z <;> contradiction
  intro a b
  cases a <;> cases b <;> trivial
  intro a b c
  cases a <;> cases b <;> cases c <;> trivial

def WellOrder.ofNat (n: Nat) : WellOrder := by
  apply WellOrder.mk (Fin n) _ _
  exact (· < ·)
  apply IsWellOrder.mk
  · apply WellFounded.intro
    rintro ⟨x, xLt⟩
    induction x using Nat.lt_wfRel.wf.induction with | h x ih =>
    apply Acc.intro
    intro y r
    apply ih
    exact r
  · rintro ⟨a, aLt⟩ ⟨b, bLt⟩
    cases Nat.decLt b a <;> rename_i h
    cases Nat.lt_or_eq_of_le (Nat.le_of_not_lt h)
    apply Or.inl
    assumption
    apply Or.inr
    apply Or.inl
    congr
    apply Or.inr
    apply Or.inr
    assumption
  · apply Fin.lt_trans

def Ordinal.ofNat (n: Nat) : Ordinal := Ordinal.mk (WellOrder.ofNat n)

def Ordinal.omega : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk Nat _ _
  exact (· < ·)
  apply IsWellOrder.mk
  exact Nat.lt_wfRel.wf
  exact Nat.lt_trichotomy
  apply Nat.lt_trans

instance : OfNat Ordinal n := ⟨ Ordinal.ulift (Ordinal.ofNat n) ⟩

def Ordinal.ofNat.def : @OfNat.ofNat Ordinal n _ = (Ordinal.ofNat n).ulift := rfl

def WellOrder.add_rel (a b: WellOrder) : a.ty ⊕ b.ty -> a.ty ⊕ b.ty -> Prop := Sum.Lex a.rel b.rel

def WellOrder.add (a b: WellOrder) : WellOrder := by
  apply WellOrder.mk _ (add_rel a b) _
  apply IsWellOrder.mk
  · apply WellFounded.intro
    intro  x
    have ind_left : ∀a₀: a.1, Acc (a.add_rel b) (Sum.inl a₀) := by
      intro a₀
      induction a₀ using a.wo.wf.induction with | h a₀ ih =>
      apply Acc.intro
      intro y r
      cases y with
      | inl y =>
        apply ih
        cases r
        assumption
      | inr y => contradiction
    cases x with
    | inl a₀ => apply ind_left
    | inr b₀ =>
      induction b₀ using b.wo.wf.induction with | h b₀ ih =>
      apply Acc.intro
      intro y r
      cases y with
      | inr y =>
        apply ih
        cases r
        assumption
      | inl y =>
        clear r
        apply ind_left
  · intro x y
    cases x <;> cases y <;> rename_i x y
    · cases a.wo.tri x y <;> rename_i h
      apply Or.inl
      apply Sum.Lex.inl
      exact h
      apply Or.inr
      cases h <;> rename_i h
      apply Or.inl
      congr
      apply Or.inr
      apply Sum.Lex.inl
      exact h
    · apply Or.inl
      apply Sum.Lex.inl_inr
    · apply Or.inr
      apply Or.inr
      apply Sum.Lex.inl_inr
    · cases b.wo.tri x y <;> rename_i h
      apply Or.inl
      apply Sum.Lex.inr
      exact h
      apply Or.inr
      cases h <;> rename_i h
      apply Or.inl
      congr
      apply Or.inr
      apply Sum.Lex.inr
      exact h
  · intro x y z xy yz
    cases xy <;> cases yz
    apply Sum.Lex.inl
    apply a.wo.trans <;> assumption
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inr
    apply b.wo.trans <;> assumption

def WellOrder.add_congr : ∀a b c d: WellOrder, Equiv a c -> Equiv b d -> Equiv (a.add b) (c.add d) := by
  intro a b c d ac bd
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · intro x
    cases x <;> rename_i x
    apply Sum.inl (ac.left x)
    apply Sum.inr (bd.left x)
  · intro x
    cases x <;> rename_i x
    apply Sum.inl (ac.right x)
    apply Sum.inr (bd.right x)
  · intro x
    cases x <;> dsimp
    rw [ac.right_left]
    rw [bd.right_left]
  · intro x
    cases x <;> dsimp
    rw [ac.left_right]
    rw [bd.left_right]
  · intro x y r
    cases r <;> dsimp
    apply Sum.Lex.inl
    apply ac.left_resp
    assumption
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inr
    apply bd.left_resp
    assumption
  · intro x y r
    cases r <;> dsimp
    apply Sum.Lex.inl
    apply ac.right_resp
    assumption
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inr
    apply bd.right_resp
    assumption

def Ordinal.add (a b: Ordinal) : Ordinal := by
  apply lift₂ (fun a b => mk (WellOrder.add a b)) _ a b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound'
  apply WellOrder.add_congr <;> assumption

instance : HAdd Ordinal Ordinal Ordinal := ⟨ Ordinal.add ⟩
def Ordinal.add.def.{u,v} (a: Ordinal.{u}) (b: Ordinal.{v}) : a + b = a.add b := rfl

def Ordinal.mk_add (a: WellOrder.{u}) (b: WellOrder.{v}) : mk a + mk b = mk (a.add b) := by
  rw [add.def, add, lift₂_mk]

def WellOrder.mul_rel (a b: WellOrder) : a.ty × b.ty -> a.ty × b.ty -> Prop := Prod.Lex a.rel b.rel

def WellOrder.mul (a b: WellOrder) : WellOrder := by
  apply WellOrder.mk _ (mul_rel b a) _
  apply IsWellOrder.mk
  · exact ⟨fun (b₀, a₀) => Prod.lexAccessible (WellFounded.apply b.wo.wf b₀) (WellFounded.apply a.wo.wf) a₀⟩
  · rintro ⟨xl,xr⟩ ⟨yl,yr⟩
    cases b.wo.tri xl yl <;> rename_i h
    apply Or.inl
    apply Prod.Lex.left
    assumption
    cases h
    subst yl
    cases a.wo.tri xr yr <;> rename_i h
    apply Or.inl
    apply Prod.Lex.right
    assumption
    cases h
    subst yr
    apply Or.inr
    apply Or.inl
    rfl
    apply Or.inr
    apply Or.inr
    apply Prod.Lex.right
    assumption
    apply Or.inr
    apply Or.inr
    apply Prod.Lex.left
    assumption
  · intro x y z xy yz
    cases xy <;> cases yz
    apply Prod.Lex.left
    apply b.wo.trans <;> assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.right
    apply a.wo.trans <;> assumption

def WellOrder.mul_congr : ∀a b c d: WellOrder, Equiv a c -> Equiv b d -> Equiv (a.mul b) (c.mul d) := by
  intro a b c d ac bd
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · rintro ⟨ b₀, a₀ ⟩
    exact ⟨ bd.left b₀, ac.left a₀ ⟩
  · rintro ⟨ d₀, c₀ ⟩
    exact ⟨ bd.right d₀, ac.right c₀ ⟩
  · rintro ⟨ d₀, c₀ ⟩
    dsimp
    rw [ac.right_left, bd.right_left]
  · rintro ⟨ c₀, d₀ ⟩
    dsimp
    rw [ac.left_right, bd.left_right]
  · rintro ⟨ xl, xr ⟩ ⟨ yl, yr ⟩ r
    dsimp
    cases r <;> rename_i r
    apply Prod.Lex.left
    apply bd.left_resp
    assumption
    apply Prod.Lex.right
    apply ac.left_resp
    assumption
  · rintro ⟨ xl, xr ⟩ ⟨ yl, yr ⟩ r
    dsimp
    cases r <;> rename_i r
    apply Prod.Lex.left
    apply bd.right_resp
    assumption
    apply Prod.Lex.right
    apply ac.right_resp
    assumption

def Ordinal.mul (a b: Ordinal) : Ordinal := by
  apply lift₂ (fun a b => mk (WellOrder.mul a b)) _ a b
  clear a b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound'
  apply WellOrder.mul_congr <;> assumption

instance : HMul Ordinal Ordinal Ordinal := ⟨ Ordinal.mul ⟩
def Ordinal.mul.def.{u,v} (a: Ordinal.{u}) (b: Ordinal.{v}) : a * b = a.mul b := rfl

def Ordinal.mk_mul (a: WellOrder.{u}) (b: WellOrder.{v}) : mk a * mk b = mk (a.mul b) := by
  rw [mul.def, mul, lift₂_mk]

def Ordinal.zero_eq_ulift_empty : 0 = ulift empty := by
  rw [ofNat.def, ofNat, empty, mk_ulift, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  apply WellOrder.Equiv.mk
  exact fun x => x.elim
  exact fun x => x.elim0
  exact fun x => x.elim0
  exact fun x => x.elim
  exact fun x => x.elim0
  exact fun x => x.elim

def Ordinal.one_eq_ulift_unit : 1 = ulift unit := by
  rw [ofNat.def, ofNat, unit, mk_ulift, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  apply WellOrder.Equiv.mk (fun _ => ⟨⟩) (fun _ => 0)
  intro; rfl
  intro x; apply Subsingleton.allEq
  intro ⟨x,xLt⟩ ⟨y,yLt⟩ h
  cases x <;> cases y <;> contradiction
  intros; contradiction

def Ordinal.two_eq_ulift_bool : 2 = ulift bool := by
  rw [ofNat.def, ofNat, bool, mk_ulift, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  intro ⟨x,xLt⟩
  match x with
  | 0 => exact false
  | 1 => exact true
  intro b
  match b with
  | false => exact 0
  | true => exact 1
  intro b
  cases b <;> rfl
  intro ⟨x,xLt⟩
  match x with
  | 0 => rfl
  | 1 => rfl
  intro x y lt
  match x, y with
  | 0, 1 => rfl
  | 0, 0 | 1, 0 | 1, 1 => contradiction
  intro x y lt
  cases x <;> cases y <;> trivial

def Ordinal.zero_eq_empty : 0 = empty := by
  rw [zero_eq_ulift_empty, ulift_eq_self]

def Ordinal.one_eq_unit : 1 = unit := by
  rw [one_eq_ulift_unit, ulift_eq_self]

def Ordinal.two_eq_unit : 2 = bool := by
  rw [two_eq_ulift_bool, ulift_eq_self]

def Ordinal.ulift_add.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : ulift.{u,w} a + b = ulift.{max u v,w} (a + b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_ulift, mk_add, mk_add, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.add_congr a.ulift b a b
  exact a.ulift_equiv_self
  rfl
  rfl

def Ordinal.add_ulift.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : a + ulift.{v,w} b = ulift.{max u v,w} (a + b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_ulift, mk_add, mk_add, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.add_congr a b.ulift a b
  rfl
  exact b.ulift_equiv_self
  rfl

def Ordinal.ulift_mul.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : ulift.{u,w} a * b = ulift.{max u v,w} (a * b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_ulift, mk_mul, mk_mul, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.mul_congr a.ulift b a b
  exact a.ulift_equiv_self
  rfl
  rfl

def Ordinal.mul_ulift.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : a * ulift.{v,w} b = ulift.{max u v,w} (a * b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_ulift, mk_mul, mk_mul, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.mul_congr a b.ulift a b
  rfl
  exact b.ulift_equiv_self
  rfl

def Ordinal.zero_add (a: Ordinal) : 0 + a = a := by
  induction a using ind with | mk a =>
  rw [zero_eq_ulift_empty, ulift_add, empty, mk_add, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.add
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x
  cases x; contradiction
  assumption
  intro x
  exact Sum.inr x
  intro x; rfl
  intro x; cases x; contradiction; rfl
  intro x y r
  cases x; contradiction
  cases y; contradiction
  cases r
  assumption
  intro x y r
  apply Sum.Lex.inr
  assumption

def Ordinal.add_zero (a: Ordinal) : a + 0 = a := by
  induction a using ind with | mk a =>
  rw [zero_eq_ulift_empty, add_ulift, empty, mk_add, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.add
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x
  cases x; assumption; contradiction
  intro x
  exact Sum.inl x
  intro x; rfl
  intro x; cases x; rfl; contradiction
  intro x y r
  cases x
  cases y
  cases r
  assumption
  repeat contradiction
  intro x y r
  apply Sum.Lex.inl
  assumption

def Ordinal.one_mul (a: Ordinal) : 1 * a = a := by
  induction a using ind with | mk a =>
  rw [one_eq_ulift_unit, ulift_mul, unit, mk_mul, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.mul WellOrder.mul_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x; exact x.1
  intro x; exact ⟨x, ⟨⟩⟩
  intros; rfl
  intros; rfl
  intro x y r
  cases r; assumption; contradiction
  intro x y r
  apply Prod.Lex.left; assumption

def Ordinal.mul_one (a: Ordinal) : a * 1 = a := by
  induction a using ind with | mk a =>
  rw [one_eq_ulift_unit, mul_ulift, unit, mk_mul, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.mul WellOrder.mul_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x; exact x.2
  intro x; exact ⟨⟨⟩, x⟩
  intros; rfl
  intros; rfl
  intro x y r
  cases r; contradiction; assumption
  intro x y r
  apply Prod.Lex.right; assumption

def Ordinal.zero_mul (a: Ordinal) : 0 * a = 0 := by
  induction a using ind with | mk a =>
  rw [zero_eq_ulift_empty, ulift_mul, empty, mk_mul, mk_ulift, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  unfold WellOrder.mul WellOrder.mul_rel
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro ⟨_,_⟩; contradiction
  intro; contradiction
  intro; contradiction
  intro ⟨_,_⟩; contradiction
  intro ⟨_,_⟩; contradiction
  intro; contradiction

def Ordinal.mul_zero (a: Ordinal) : a * 0 = 0 := by
  induction a using ind with | mk a =>
  rw [zero_eq_ulift_empty, mul_ulift, empty, mk_mul, mk_ulift, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  unfold WellOrder.mul WellOrder.mul_rel
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro ⟨_,_⟩; contradiction
  intro; contradiction
  intro; contradiction
  intro ⟨_,_⟩; contradiction
  intro ⟨_,_⟩; contradiction
  intro; contradiction

def Ordinal.le_zero (a: Ordinal) : a ≤ 0 -> a = 0 := by
  induction a using ind with | mk a =>
  rw [zero_eq_ulift_empty, empty, mk_ulift, le.def]
  intro h
  replace h := (mk_le _ _).mp h
  have ⟨emb⟩ := WellOrder.of_ulift_le_right _ _ h
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.mk emb.f Empty.elim _ _ _ _
  any_goals (intro x; contradiction)
  all_goals (intro x; have := emb.f x; contradiction)

def Ordinal.mul_eq_zero (a b: Ordinal) : a * b = 0 -> a = 0 ∨ b = 0 := by
  rw [zero_eq_ulift_empty]
  intro h
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_mul, empty, mk_ulift] at h
  replace ⟨h⟩ := exact h
  replace h := WellOrder.of_ulift_equiv_right _ _ h
  have ⟨ f, g, fg, gf, f_resp, g_resp ⟩ := h
  clear fg g_resp gf g f_resp
  apply byCases (Nonempty a.ty)
  · intro ⟨a₀⟩
    apply byCases (Nonempty b.ty)
    · intro ⟨b₀⟩
      have := f ⟨b₀,a₀⟩
      contradiction
    · intro h₀
      apply Or.inr
      rw [empty, mk_ulift]
      apply sound'
      apply WellOrder.ulift_equiv_right
      apply WellOrder.Equiv.mk _ _ _ _ _ _
      · intro x
        have := h₀ ⟨x⟩
        contradiction
      · intro; contradiction
      · intro; contradiction
      · intro x
        have := h₀ ⟨x⟩
        contradiction
      · intro x
        have := h₀ ⟨x⟩
        contradiction
      · intro; contradiction
  · intro h₀
    apply Or.inl
    rw [empty, mk_ulift]
    apply sound'
    apply WellOrder.ulift_equiv_right
    apply WellOrder.Equiv.mk _ _ _ _ _ _
    · intro x
      have := h₀ ⟨x⟩
      contradiction
    · intro; contradiction
    · intro; contradiction
    · intro x
      have := h₀ ⟨x⟩
      contradiction
    · intro x
      have := h₀ ⟨x⟩
      contradiction
    · intro; contradiction

def Ordinal.two_mul (a: Ordinal) : a * 2 = a + a := by
  induction a using ind with | mk a =>
  rw [two_eq_ulift_bool, mul_ulift, bool, mk_mul, mk_add, mk_ulift]
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.mul WellOrder.mul_rel WellOrder.add WellOrder.add_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  rintro ⟨b,x⟩
  cases b
  exact .inl x
  exact .inr x
  intro x
  cases x <;> rename_i x
  exact ⟨false,x⟩
  exact ⟨true,x⟩
  intro x
  cases x <;> rfl
  intro ⟨b,x⟩
  cases b <;> rfl
  intro ⟨b₀,x₀⟩ ⟨b₁,x₁⟩ r
  cases b₀ <;> cases b₁ <;> dsimp
  any_goals contradiction
  cases r; contradiction
  apply Sum.Lex.inl; assumption
  apply Sum.Lex.inl_inr
  cases r; contradiction
  apply Sum.Lex.inr; assumption
  intro x y r
  cases r <;> dsimp
  any_goals apply Prod.Lex.right; assumption
  apply Prod.Lex.left; trivial

def Ordinal.omega_mul_fin (n: Nat) : ofNat (n+1) * omega = omega := by
  unfold omega ofNat
  rw [mk_mul]
  apply sound'
  unfold WellOrder.mul WellOrder.mul_rel WellOrder.ofNat
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · intro ⟨x,y⟩
    exact x * n.succ + y
  · intro x
    exact ⟨x/n.succ,Fin.ofNat x⟩
  · intro x
    dsimp
    rw [Fin.ofNat]
    dsimp
    rw [Nat.mul_comm]
    apply Nat.div_add_mod
  · intro ⟨x,y,yLt⟩
    dsimp
    congr
    rw [Nat.div_eq_of_lt_le]
    apply Nat.le_add_right
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left yLt (x * (n + 1))
    rw [Fin.ofNat]
    congr
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
    assumption
  · intro ⟨x₀,x₁⟩ ⟨y₀,y₁⟩ r
    dsimp
    cases r
    apply Nat.lt_of_lt_of_le
    apply Nat.add_lt_add_left
    exact x₁.isLt
    rw [←Nat.succ_mul, ←Nat.add_zero (x₀.succ * _)]
    apply Nat.add_le_add
    apply Nat.mul_le_mul_right
    apply Nat.succ_le_of_lt
    assumption
    apply Nat.zero_le
    apply Nat.add_lt_add_left
    assumption
  · intro x y x_lt_y
    cases Nat.decLt (x / n.succ) (y / n.succ) <;> rename_i r
    replace r := Nat.le_of_not_lt r
    have : x / n.succ ≤ y / n.succ := by
      refine (Nat.le_div_iff_mul_le ?k0).mpr ?_
      apply Nat.zero_lt_succ
      rw [Nat.mul_comm]
      apply Nat.le_trans
      apply Nat.le_add_right
      exact x % n.succ
      rw [Nat.div_add_mod]
      apply Nat.le_of_lt
      assumption
    have := Nat.le_antisymm this r
    rw [this]
    apply Prod.Lex.right
    rw [←Nat.div_add_mod x n.succ, ←Nat.div_add_mod y n.succ] at x_lt_y
    rw [this] at x_lt_y
    exact Nat.lt_of_add_lt_add_left x_lt_y
    apply Prod.Lex.left
    assumption

def Ordinal.omega_add_fin (n: Nat) : ofNat n + omega = omega := by
  unfold omega ofNat
  rw [mk_add]
  apply sound'
  unfold WellOrder.add WellOrder.add_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · intro x
    match x with
    | .inl x => exact x.val
    | .inr x => exact x + n
  · intro x
    match Nat.decLt x n with
    | .isTrue h => exact .inl ⟨ x, h ⟩
    | .isFalse _ => exact .inr (x - n)
  · intro x
    cases Nat.decLt x n
    dsimp
    rw [Nat.sub_add_cancel]
    apply Nat.le_of_not_lt
    assumption
    rfl
  · intro x
    cases x <;> (rename_i x; dsimp)
    split
    rfl
    have := x.isLt
    contradiction
    split
    have := Nat.not_lt_of_le (Nat.le_add_left n x)
    contradiction
    rw [Nat.add_sub_cancel]
  · intro x y r
    cases x <;> rename_i x <;> cases y <;> rename_i y <;> dsimp
    cases r
    assumption
    apply Nat.lt_of_lt_of_le x.isLt
    apply Nat.le_add_left
    cases r
    apply Nat.add_lt_add_right
    cases r
    assumption
  · intro x y x_lt_y
    split <;> split
    apply Sum.Lex.inl
    assumption
    apply Sum.Lex.inl_inr
    rename_i h₀ _ _ h₁ _
    have := Nat.lt_of_lt_of_le h₁ (Nat.le_of_not_lt h₀)
    have := Nat.lt_irrefl _ (Nat.lt_trans this x_lt_y)
    contradiction
    apply Sum.Lex.inr
    refine Nat.sub_lt_sub_right ?h_2.h_2.a.a x_lt_y
    apply Nat.le_of_not_lt
    assumption

def Ordinal.mul_add (k a b: Ordinal) : k * (a + b) = k * a + k * b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction k using ind with | mk k =>
  repeat first| rw [mk_mul]|rw [mk_add]
  apply sound'
  unfold WellOrder.add WellOrder.mul WellOrder.add_rel WellOrder.mul_rel
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  · intro ⟨a₀,k₀⟩
    match a₀ with
    | .inl a₀ => exact .inl ⟨a₀,k₀⟩
    | .inr a₀ => exact .inr ⟨a₀,k₀⟩
  · intro ak
    match ak with
    | .inl ak => exact ⟨.inl ak.1, ak.2⟩
    | .inr ak => exact ⟨.inr ak.1, ak.2⟩
  · intro x
    cases x <;> rfl
  · intro ⟨x,_⟩
    cases x <;> rfl
  · intro ⟨xl,xr⟩ ⟨yl,yr⟩
    cases xl <;> cases yl <;> (dsimp; rename_i xr yr; intro r)
    any_goals cases r
    any_goals rename_i r
    any_goals cases r
    · apply Sum.Lex.inl
      apply Prod.Lex.left
      assumption
    · apply Sum.Lex.inl
      apply Prod.Lex.right
      assumption
    · apply Sum.Lex.inl_inr
    · apply Sum.Lex.inr
      apply Prod.Lex.left
      assumption
    · apply Sum.Lex.inr
      apply Prod.Lex.right
      assumption
  · intro ak₀ ak₁
    cases ak₀ <;> cases ak₁ <;> (
      dsimp
      rename_i ak₀ ak₁
      have ⟨a₀,k₀⟩ := ak₀
      have ⟨a₁,k₁⟩ := ak₁
      intro r
      cases r)
    · rename_i r
      cases r
      apply Prod.Lex.left
      apply Sum.Lex.inl
      assumption
      apply Prod.Lex.right
      assumption
    · apply Prod.Lex.left
      apply Sum.Lex.inl_inr
    · rename_i r
      cases r
      apply Prod.Lex.left
      apply Sum.Lex.inr
      assumption
      apply Prod.Lex.right
      assumption

def Ordinal.ofNat_add (n m: Nat) : ofNat (n + m) = ofNat n + ofNat m := by
  unfold ofNat
  rw [mk_add]
  apply sound'
  unfold WellOrder.ofNat WellOrder.add WellOrder.add_rel
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  · intro ⟨x,xLt⟩
    if h:x < n then
      exact .inl ⟨x,h⟩
    else
      replace h := Nat.le_of_not_lt h
      rw [←Nat.sub_add_cancel h, Nat.add_comm] at xLt
      exact .inr ⟨_,Nat.lt_of_add_lt_add_left xLt⟩
  · intro x
    match x with
    | .inl x => exact ⟨x.val, Nat.lt_of_lt_of_le x.isLt (Nat.le_add_right _ _)⟩
    | .inr x => exact ⟨n+x.val, Nat.add_lt_add_left x.isLt _⟩
  · intro x
    cases x <;> (rename_i x; have ⟨x,xLt⟩ := x; dsimp)
    rw [dif_pos xLt]
    rw [dif_neg (Nat.not_lt_of_le (Nat.le_add_right _ _))]
    congr
    rw [Nat.add_comm, Nat.add_sub_cancel]
  · intro ⟨x,xLt⟩
    dsimp
    if h:x < n then
      rw [dif_pos h]
    else
      rw [dif_neg h]
      dsimp
      congr
      rw [Nat.add_comm, Nat.sub_add_cancel]
      apply Nat.le_of_not_lt; assumption
  · intro ⟨x,xLt⟩ ⟨y,yLt⟩ x_lt_y
    replace x_lt_y : x < y := x_lt_y
    dsimp
    split <;> rename_i hx
    split <;> rename_i hx
    apply Sum.Lex.inl
    assumption
    apply Sum.Lex.inl_inr
    replace hx := Nat.le_of_not_lt hx
    have hy := Nat.lt_of_le_of_lt hx x_lt_y
    rw [dif_neg (Nat.not_lt_of_gt hy)]
    apply Sum.Lex.inr
    apply Nat.sub_lt_sub_right
    assumption
    assumption
  · intro x y r
    cases r <;> dsimp
    trivial
    rename_i x y
    apply Nat.lt_of_lt_of_le x.isLt
    apply Nat.le_add_right
    apply Nat.add_lt_add_left
    assumption

def Ordinal.zero_lt_one : (0: Ordinal) < (1: Ordinal) := by
  rw [Ordinal.zero_eq_ulift_empty, Ordinal.one_eq_ulift_unit,
    Ordinal.empty, Ordinal.unit, Ordinal.mk_ulift, Ordinal.mk_ulift,
    Ordinal.mk_lt]
  apply WellOrder.ulift_lt_ulift
  apply WellOrder.Lt.mk (.mk _ _ _ _ _ _)
  any_goals (intros; contradiction)
  exact ⟨⟩

def Ordinal.lt_trans { a b c: Ordinal } : a < b -> b < c -> a < c := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction c using ind with | mk c =>
  rw [mk_lt, mk_lt, mk_lt]
  intro ⟨ab⟩ ⟨bc⟩
  apply WellOrder.Lt.mk (.mk _ _ _ _ _ _)
  exact bc.f ∘ ab.f
  -- exact bc.top
  exact bc.f ab.top
  intro a₀ a₁ r
  have r := bc.inj _ _ r
  have r := ab.inj _ _ r
  exact r
  intro a₀ a₁
  dsimp
  rw [←bc.resp, ←ab.resp]
  intro a₀
  apply bc.resp.mp
  apply ab.lt_top
  intro c₀ r
  have := c.wo
  have init := bc.toRelInitalSeg.init
  unfold RelPrincipalSeg.toRelInitalSeg at init
  dsimp at init
  have ⟨ b₀, prf ⟩ := init c₀ ab.top r
  subst c₀
  have r := bc.resp.mpr r
  have ⟨ a₀, prf ⟩  := ab.of_lt_top _ r
  exists a₀
  dsimp
  rw [prf]

def Ordinal.le_trans { a b c: Ordinal } : a ≤ b -> b ≤ c -> a ≤ c := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction c using ind with | mk c =>
  rw [mk_le, mk_le, mk_le]
  intro ⟨ab⟩ ⟨bc⟩
  apply WellOrder.Le.mk (.mk _ _ _ _)
  exact bc.f ∘ ab.f
  intro a₀ a₁ r
  have r := bc.inj _ _ r
  have r := ab.inj _ _ r
  exact r
  intro a₀ a₁
  dsimp
  rw [←bc.resp, ←ab.resp]
  intro c₀ b₀ r
  have ⟨ b₁, prf ⟩  := bc.init _ _ r
  subst c₀
  have ⟨ a₁, prf ⟩  := ab.init _ _ (bc.resp.mpr r)
  subst b₁
  exists a₁

def Ordinal.le_of_lt {a b: Ordinal} : a < b -> a ≤ b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_lt, mk_le]
  intro ⟨princ_seg⟩
  have := b.wo
  exact ⟨princ_seg.toRelInitalSeg⟩

def Ordinal.irrefl (a: Ordinal) : ¬(a < a) := by
  induction a using ind with | mk a =>
  rw [mk_lt]
  intro ⟨princ_seg⟩
  have f_top_eq_top : princ_seg.f princ_seg.top = princ_seg.top := by
    have := a.wo
    exact RelInitialSeg.eq princ_seg.toRelInitalSeg (RelInitialSeg.refl a.rel) princ_seg.top
  have := princ_seg.lt_top princ_seg.top
  rw [f_top_eq_top] at this
  exact a.wo.wf.irrefl this

def Ordinal.init_seg_of (a b: Ordinal) : a < b ∨ a = b ∨ b < a := by
  sorry

def Ordinal.tri (a b: Ordinal) : a < b ∨ a = b ∨ b < a := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_lt, mk_lt]
  apply byContradiction
  intro h
  replace ⟨ not_lt, h ⟩ := not_or.mp h
  replace ⟨ not_eq, not_gt ⟩ := not_or.mp h
  clear h
  apply not_eq
  apply sound'
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  ·
    sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

def Ordinal.not_lt_zero (o: Ordinal) : ¬o < 0 := by
  induction o using ind with | mk o =>
  rw [ofNat.def, ofNat, mk_ulift, mk_lt]
  intro ⟨seg⟩
  dsimp at seg
  exact seg.top.down.elim0

def Ordinal.ofNat_eq_OfNat (n: Nat) : Ordinal.ofNat n = @OfNat.ofNat Ordinal n _ := by
  unfold OfNat.ofNat instOfNatOrdinal
  dsimp
  rw [ulift_eq_self]

def Ordinal.lt_succ_self (o: Ordinal) : o < o + 1 := by
  induction o using ind with | mk o =>
  rw [one_eq_ulift_unit, unit, add_ulift, mk_add, mk_ulift, mk_lt]
  apply WellOrder.ulift_lt_right
  unfold WellOrder.add WellOrder.add_rel
  apply WellOrder.Lt.mk (.mk _ _ _ _ _ _) <;> dsimp
  · exact Sum.inl
  · exact .inr ⟨⟩
  · intro x y
    exact Sum.inl.inj
  · intro x y
    apply Iff.intro
    exact Sum.Lex.inl
    intro r
    cases r
    assumption
  · intro b
    apply Sum.Lex.inl_inr
  · intro x r
    cases r
    any_goals contradiction
    rename_i x _
    exists x

def Ordinal.of_lt_succ (a b: Ordinal) : a < b + 1 -> a < b ∨ a = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [one_eq_ulift_unit, unit, add_ulift, mk_add, mk_ulift, mk_lt, mk_lt]
  unfold WellOrder.add WellOrder.add_rel
  intro r
  replace ⟨r⟩ := WellOrder.of_ulift_lt_right _ _ r
  dsimp at r

  sorry

def Ordinal.ofNat_lt (m n: Nat) : ofNat n < ofNat m ↔ n < m := by
  induction m with
  | zero =>
    rw [ofNat_eq_OfNat 0]
    apply Iff.intro
    exact False.elim ∘ (not_lt_zero _)
    exact False.elim ∘ (Nat.not_lt_zero _)
  | succ m ih =>
    rw [ofNat_add, ofNat_eq_OfNat 1]

    sorry

def Ordinal.ofNat_le (m n: Nat) : ofNat n ≤ ofNat m ↔ n ≤ m := by
  unfold ofNat
  rw [mk_le]
  apply Iff.intro
  · intro h
    cases h <;> rename_i h
    cases h with | mk' h init =>
    cases h with | mk h resp =>
    cases h with | mk f inj =>
    dsimp at resp init
    clear resp init
    induction m with
    | zero =>
      sorry
    | succ m ih =>
      sorry
  · intro h
    sorry

def Ordinal.ofNat_mul (n m: Nat) : ofNat (n * m) = ofNat n * ofNat m := by
  unfold ofNat
  rw [mk_mul]
  apply sound'
  unfold WellOrder.ofNat WellOrder.mul WellOrder.mul_rel
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
