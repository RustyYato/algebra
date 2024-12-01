import Algebra.WellFounded
import Algebra.Ty.Basic
import Algebra.Function.Basic
import Algebra.ClassicLogic

namespace Relation

variable (rel: α -> α -> Prop)
variable {r: α -> α -> Prop} {s: β -> β -> Prop} {t: α₁ -> α₁ -> Prop}

class IsWellFounded: Prop where
  wf: WellFounded rel
def wellFounded [inst: IsWellFounded rel] := inst.wf
def wfInduction [inst: IsWellFounded rel] := @WellFounded.induction _ _ inst.wf

class IsTrans: Prop where
  trans: ∀{a b c}, rel a b -> rel b c -> rel a c
def trans [IsTrans r] : ∀{a b c}, r a b -> r b c -> r a c := IsTrans.trans

instance [IsTrans rel] : Trans rel rel rel where
  trans := trans

class IsTrichotomous: Prop where
  tri: ∀a b, rel a b ∨ a = b ∨ rel b a
def trichotomous [IsTrichotomous rel] : ∀(a b: α), rel a b ∨ a = b ∨ rel b a := IsTrichotomous.tri

class IsIrrefl: Prop where
  irrefl: ∀{a}, ¬rel a a
def irrefl [IsIrrefl r] : ∀{a}, ¬r a a := IsIrrefl.irrefl

instance IsWellFounded.toIsIrrefl [wf: IsWellFounded rel] : IsIrrefl rel where
  irrefl := wf.wf.irrefl

class IsWellOrder extends IsWellFounded rel, IsTrans rel, IsTrichotomous rel: Prop where
instance [IsWellFounded rel] [IsTrans rel] [IsTrichotomous rel] : IsWellOrder rel where

instance IsWellOrder.toIsIrrefl [wo: IsWellOrder rel] : IsIrrefl rel where
  irrefl := wo.wf.irrefl

structure Embed (r: α -> α -> Prop) (s: β -> β -> Prop) extends Ty.Embed α β where
  resp: ∀{x y}, r x y ↔ s (embed x) (embed y)
instance : CoeFun (Embed r s) (fun _ => α -> β) := ⟨fun x => x.embed⟩

structure EmbedIso (r: α -> α -> Prop) (s: β -> β -> Prop) extends Ty.EmbedIso α β where
  fwd_resp: ∀{x y}, r x y -> s (fwd x) (fwd y)
  rev_resp: ∀{x y}, s x y -> r (rev x) (rev y)

@[symm]
def EmbedIso.refl (r: α -> α -> Prop) : EmbedIso r r where
  fwd := id
  rev := id
  fwd_rev _ := rfl
  rev_fwd _ := rfl
  fwd_resp := id
  rev_resp := id

@[symm]
def EmbedIso.symm (e: EmbedIso r s) : EmbedIso s r := by
  apply EmbedIso.mk e.toEmbedIso.symm
  exact e.rev_resp
  exact e.fwd_resp

@[symm]
def EmbedIso.trans (h: EmbedIso r s) (g: EmbedIso s t) : EmbedIso r t := by
  apply EmbedIso.mk (h.toEmbedIso.trans g.toEmbedIso) <;> (unfold Ty.EmbedIso.trans; dsimp)
  intro x y xy
  apply g.fwd_resp
  apply h.fwd_resp
  assumption
  intro x y xy
  apply h.rev_resp
  apply g.rev_resp
  assumption

@[symm]
def EmbedIso.rev_resp_iff (h: EmbedIso r s) : s x y ↔ r (h.rev x) (h.rev y) := by
  apply Iff.intro
  exact h.rev_resp
  intro
  rw [←h.rev_fwd x, ←h.rev_fwd y]
  apply h.fwd_resp
  assumption

@[symm]
def EmbedIso.fwd_resp_iff (h: EmbedIso r s) : r x y ↔ s (h.fwd x) (h.fwd y) := h.symm.rev_resp_iff

def EmbedIso.fwdEmbed (e: EmbedIso r s) : Embed r s where
  embed := e.fwd
  embed_inj := e.fwd_inj
  resp := by
    intro x y
    apply Iff.intro
    exact e.fwd_resp
    intro rel
    have := e.rev_resp rel
    rw [e.fwd_rev, e.fwd_rev] at this
    exact this
def EmbedIso.revEmbed (e: EmbedIso r s) : Embed s r := e.symm.fwdEmbed

structure InitialSeg (r: α -> α -> Prop) (s: β -> β -> Prop) extends Embed r s where
  init: ∀a b, s a (embed b) -> ∃x, embed x = a
instance : CoeFun (InitialSeg r s) (fun _ => α -> β) := ⟨fun x => x.embed⟩

structure PrincipalSeg (r: α -> α -> Prop) (s: β -> β -> Prop) extends Embed r s where
  top: β
  lt_top: ∀{x}, s x top ↔ ∃y, embed y = x
instance : CoeFun (PrincipalSeg r s) (fun _ => α -> β) := ⟨fun x => x.embed⟩

def Embed.refl : Embed rel rel := ⟨ .refl _, Iff.refl _ ⟩
def InitialSeg.refl : InitialSeg rel rel := ⟨ .refl _, fun a _ _ => ⟨ a, rfl ⟩ ⟩

def PrincipalSeg.toInitialSeg [IsTrans s] (seg: PrincipalSeg r s) : InitialSeg r s where
  embed := seg.embed
  embed_inj := seg.embed_inj
  resp := seg.resp
  init b a b_lt_sa := by
    dsimp at b_lt_sa
    dsimp
    have b_lt_top := trans b_lt_sa (seg.lt_top.mpr ⟨ a, rfl ⟩)
    exact seg.lt_top.mp b_lt_top

instance PrincipalSeg.coeInitialSeg [IsTrans s] : Coe (PrincipalSeg r s) (InitialSeg r s) := ⟨PrincipalSeg.toInitialSeg⟩

def ext [IsIrrefl rel] [IsTrichotomous rel] (a b: α) :
  (∀x, rel x a ↔ rel x b) -> a = b := by
  intro rel_iff
  cases trichotomous rel a b <;> rename_i h
  have := (rel_iff _).mpr h
  have := irrefl this
  contradiction
  cases h <;> rename_i h
  assumption
  have := (rel_iff _).mp h
  have := irrefl this
  contradiction

def InitialSeg.eq {r: α -> α -> Prop} [rwo: IsWellOrder r] [swo: IsWellOrder s] (a b: InitialSeg r s) (x: α) : a x = b x := by
  induction x using rwo.wf.induction with
  | h x ih =>
  apply ext s
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

end Relation

namespace Relation

variable {r₀: α₀ -> α₀ -> Prop} {s₀: β₀ -> β₀ -> Prop}
variable {r₁: α₁ -> α₁ -> Prop} {s₁: β₁ -> β₁ -> Prop}

def IsWellFounded.transfer (h: EmbedIso r₀ s₀) :
  IsWellFounded r₀ -> IsWellFounded s₀ := by
  intro ⟨wf⟩
  apply IsWellFounded.mk
  apply WellFounded.intro
  intro a
  rw [←h.rev_fwd a]
  generalize h.rev a = a'
  induction a' using wf.induction with | h a ih =>
  apply Acc.intro
  intro b r
  rw [←h.rev_fwd b]
  apply ih
  rw [←h.fwd_rev a]
  apply h.rev_resp
  assumption

def IsWellFounded.transfer_iff (h: EmbedIso r₀ s₀) :
  IsWellFounded r₀ ↔ IsWellFounded s₀ := by
  apply Iff.intro
  apply transfer
  assumption
  apply transfer
  symm; assumption

def IsTrans.transfer (h: EmbedIso r₀ s₀) :
  IsTrans r₀ -> IsTrans s₀ := by
  intro
  apply IsTrans.mk
  intro a b c ab bc
  apply h.rev_resp_iff.mpr
  have := h.rev_resp ab
  have := h.rev_resp bc
  apply Relation.trans <;> assumption

def IsTrans.transfer_iff (h: EmbedIso r₀ s₀) :
  IsTrans r₀ ↔ IsTrans s₀ := by
  apply Iff.intro
  apply transfer
  assumption
  apply transfer
  symm; assumption

def IsTrans.transferInit (h: InitialSeg r₀ s₀) :
  IsTrans s₀ -> IsTrans r₀ := by
  intro
  apply IsTrans.mk
  intro a b c ab bc
  apply h.resp.mpr
  have := h.resp.mp ab
  have := h.resp.mp bc
  apply Relation.trans <;> assumption

def IsTrichotomous.transfer (h: EmbedIso r₀ s₀) :
  IsTrichotomous r₀ -> IsTrichotomous s₀ := by
  intro
  apply IsTrichotomous.mk
  intro a b
  rcases trichotomous r₀ (h.rev a) (h.rev b) with ab | eq | ba
  left
  apply h.rev_resp_iff.mpr; assumption
  right; left
  apply h.rev_inj; assumption
  right; right
  apply h.rev_resp_iff.mpr; assumption

def IsTrichotomous.transfer_iff (h: EmbedIso r₀ s₀) :
  IsTrichotomous r₀ ↔ IsTrichotomous s₀ := by
  apply Iff.intro
  apply transfer
  assumption
  apply transfer
  symm; assumption

def IsIrrefl.transfer (h: EmbedIso r₀ s₀) :
  IsIrrefl r₀ -> IsIrrefl s₀ := by
  intro
  apply IsIrrefl.mk
  intro a
  apply (not_iff_not h.rev_resp_iff).mpr
  apply irrefl

def IsIrrefl.transfer_iff (h: EmbedIso r₀ s₀) :
  IsIrrefl r₀ ↔ IsIrrefl s₀ := by
  apply Iff.intro
  apply transfer
  assumption
  apply transfer
  symm; assumption

def IsWellOrder.transfer (h: EmbedIso r₀ s₀) :
  IsWellOrder r₀ -> IsWellOrder s₀ := by
  intro g
  have := g.toIsWellFounded.transfer h
  have := g.toIsTrichotomous.transfer h
  have := g.toIsTrans.transfer h
  apply IsWellOrder.mk

def IsWellOrder.transfer_iff (h: EmbedIso r₀ s₀) :
  IsWellOrder r₀ ↔ IsWellOrder s₀ := by
  apply Iff.intro
  apply transfer
  assumption
  apply transfer
  symm; assumption

def InitialSeg.transfer (h₁: EmbedIso r₀ r₁) (h₂: EmbedIso s₀ s₁) (seg: InitialSeg r₀ s₀) : InitialSeg r₁ s₁ where
  embed := h₂.fwd ∘ seg.embed ∘ h₁.rev
  embed_inj := by
    apply Function.Injective.comp
    apply Function.Injective.comp
    exact h₁.rev_inj
    exact seg.embed_inj
    exact h₂.fwd_inj
  init := by
    intro b a r
    dsimp at r
    have := h₂.rev_resp r
    rw [h₂.fwd_rev] at this
    have ⟨x, prf⟩ := seg.init _ _ this
    exists h₁.fwd x
    dsimp
    apply h₂.rev_inj
    rw [←prf]
    rw [h₂.fwd_rev, h₁.fwd_rev]
  resp := by
    intro x y
    dsimp
    apply Iff.trans _ h₂.fwd_resp_iff
    apply Iff.trans _ seg.resp
    apply Iff.trans _ h₁.rev_resp_iff
    rfl

def PrincipalSeg.transfer (h₁: EmbedIso r₀ r₁) (h₂: EmbedIso s₀ s₁) (seg: PrincipalSeg r₀ s₀) : PrincipalSeg r₁ s₁ where
  embed := h₂.fwd ∘ seg.embed ∘ h₁.rev
  embed_inj := by
    apply Function.Injective.comp
    apply Function.Injective.comp
    exact h₁.rev_inj
    exact seg.embed_inj
    exact h₂.fwd_inj
  resp := by
    intro x y
    dsimp
    apply Iff.trans _ h₂.fwd_resp_iff
    apply Iff.trans _ seg.resp
    apply Iff.trans _ h₁.rev_resp_iff
    rfl
  top := h₂.fwd seg.top
  lt_top := by
    intro x
    dsimp
    apply Iff.trans h₂.rev_resp_iff
    rw [h₂.fwd_rev]
    apply Iff.trans seg.lt_top
    apply Iff.intro
    intro ⟨y, prf⟩
    exists h₁.fwd y
    apply h₂.rev_inj
    rwa [h₁.fwd_rev, h₂.fwd_rev]
    intro ⟨y, prf⟩
    exists h₁.rev y
    apply h₂.fwd_inj
    rwa [h₂.rev_fwd]

end Relation

namespace Sum

variable (alt: α -> α -> Prop) (blt: β -> β -> Prop)

instance
  LexIsWellFounded
  [Relation.IsWellFounded alt]
  [Relation.IsWellFounded blt] : Relation.IsWellFounded (Lex alt blt) where
  wf := by
    have : ∀x, Acc (Lex alt blt) (inl x) := by
      intro x
      induction x using Relation.wfInduction alt with
      | h x ih =>
        apply Acc.intro
        intro y r
        cases r <;> rename_i y r
        exact ih _ r
    apply WellFounded.intro
    intro a
    cases a with
    | inl a => apply this
    | inr b =>
      induction b using Relation.wfInduction blt with
      | h x ih =>
        apply Acc.intro
        intro y r
        cases r <;> rename_i y r
        exact ih _ r
        apply this

instance
  LexIsTrans
  [Relation.IsTrans alt]
  [Relation.IsTrans blt] : Relation.IsTrans (Lex alt blt) where
  trans := by
    intro a b c ab bc
    cases ab <;> cases bc
    any_goals apply Lex.inl
    any_goals apply Lex.inr
    any_goals apply Lex.sep
    rename_i ab _ bc
    apply trans ab bc
    rename_i ab _ bc
    apply trans ab bc

instance
  LexIsTrichotomous
  [Relation.IsTrichotomous alt]
  [Relation.IsTrichotomous blt] : Relation.IsTrichotomous (Lex alt blt) where
  tri := by
    intro a b
    cases a <;> cases b
    any_goals apply Or.inl (Lex.sep _ _)
    any_goals apply Or.inr (Or.inr (Lex.sep _ _))
    all_goals rename_i x y
    cases Relation.trichotomous alt x y <;> rename_i h
    apply Or.inl; apply Lex.inl; assumption
    apply Or.inr
    cases h
    apply Or.inl; congr
    apply Or.inr; apply Lex.inl; assumption
    cases Relation.trichotomous blt x y <;> rename_i h
    apply Or.inl; apply Lex.inr; assumption
    apply Or.inr
    cases h
    apply Or.inl; congr
    apply Or.inr; apply Lex.inr; assumption

end Sum

namespace Relation

variable (rel: α -> α -> Prop)
variable {r: α -> α -> Prop} {s: β -> β -> Prop} {t: α₁ -> α₁ -> Prop}

def InitialSeg.leSum (r: α -> α -> Prop) (s: β -> β -> Prop) : InitialSeg r (Sum.Lex r s) where
  embed := Sum.inl
  embed_inj := Sum.inl.inj
  resp := Iff.intro Sum.Lex.inl (fun (.inl h) => h)
  init := by
    intro x b rel
    cases rel
    rename_i x _
    exists x

def IsWellOrder.ext_eq [rwo: IsWellOrder r] : (∀z, r z x ↔ r z y) -> x = y := by
  intro eqv
  induction x using rwo.wf.induction generalizing y with | h x ih =>
  replace ih := fun x₀ => ih x₀
  rcases rwo.tri x y with x_lt_y | x_eq_y | y_lt_x
  have := irrefl ((eqv _).mpr x_lt_y)
  contradiction
  assumption
  have := irrefl ((eqv _).mp y_lt_x)
  contradiction

def IsWellFounded.find_min
  [rwo: IsWellFounded r]
  (P: α -> Prop)
  (h: ∃x, P x)
  : ∃x, P x ∧ ∀y, r y x -> ¬P y := by
  obtain ⟨x, Px⟩ := h
  induction x using rwo.wf.induction with | h x ih =>
  apply ClassicLogic.byCases (∃y, r y x ∧ P y)
  intro ⟨y, y_lt_x, Py⟩
  apply ih y <;> assumption
  intro h
  have := fun y => not_and.mp (not_exists.mp h y)
  exists x

def InitialSeg.Injective_aux
  [IsWellOrder r] [IsWellOrder s] (f: InitialSeg r s) :
  (∀x y, f.embed x = f.embed y -> ∀z, r z x -> r z y) := by
  intro x y eq
  intro z h
  have := f.resp.mp h
  rw [eq] at this
  apply f.resp.mpr
  assumption

def InitialSeg.Injective
  [rwo: IsWellOrder r] [swo: IsWellOrder s] (f: InitialSeg r s) :
  Function.Injective f := by
  intro x y eq
  induction x using rwo.wf.induction generalizing y with | h x ih =>
  apply IsWellOrder.ext_eq (r := r)
  intro z
  apply Iff.intro
  apply f.Injective_aux
  assumption
  apply f.Injective_aux
  symm; assumption

def InitialSeg.surj_or_principal_aux
  [IsWellOrder r] [swo: IsWellOrder s] (f: InitialSeg r s):
  ¬Function.Surjective f -> ∃ b, ∀ x, (∃ y, f y = x) -> s x b := by
  intro h
  have ⟨b, b_not_in_range_of_f⟩  := ClassicLogic.not_forall.mp h
  exists b
  intro x ⟨y, prf⟩
  subst x
  rcases swo.tri (f y) b with syb | y_eq_b | sby
  assumption
  have := b_not_in_range_of_f ⟨_, y_eq_b⟩
  contradiction
  have := f.init b y sby
  contradiction

def InitialSeg.surj_or_principal
  [rwo: IsWellOrder r] [swo: IsWellOrder s] (f: InitialSeg r s):
  Function.Surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x := by
  apply Or.symm
  apply ClassicLogic.or_iff_not_imp_right.mpr
  intro h
  have ⟨b, prf⟩ := InitialSeg.surj_or_principal_aux f h
  replace prf : ∀x, s (f x) b := by
    intro x
    exact prf (f x) ⟨_, rfl⟩
  induction b using swo.wf.induction with | h b ih =>
  apply ClassicLogic.byCases (∃b', s b' b ∧ ∀x, s (f x) b')
  · intro ⟨b', b'_lt_b, b_max⟩
    apply ih b' <;> assumption
  · intro b_is_max
    exists b
    intro b'
    apply Iff.intro
    · intro b'_lt_b
      have ⟨x, b'_lt_x⟩ := ClassicLogic.not_forall.mp <| not_and.mp (not_exists.mp b_is_max b') b'_lt_b
      clear ih b_is_max h
      have ⟨x', b'_lt_x', x'_min⟩ := IsWellFounded.find_min (r := r) (fun x => ¬s (f x) b') ⟨x, b'_lt_x⟩
      replace x'_min := fun y h => ClassicLogic.not_not.mp (x'_min y h)
      exists x'
      apply IsWellOrder.ext_eq (r := s)
      intro z
      apply Iff.intro
      intro szx
      have ⟨z, h⟩  := f.init _ _ szx
      subst h
      apply x'_min
      apply f.resp.mpr
      assumption
      intro szb'
      rcases swo.tri z (f x') with z_lt | z_eq | lt_z
      assumption
      subst z
      contradiction
      have := swo.trans lt_z szb'
      contradiction
    intro ⟨y, eq⟩
    subst eq
    apply prf

def InitialSeg.princ_or_eq
  [rwo: IsWellOrder r] [swo: IsWellOrder s] (f: Nonempty (InitialSeg r s)):
  Nonempty (EmbedIso r s) ∨ Nonempty (PrincipalSeg r s) := by
  obtain ⟨f⟩ := f
  rcases f.surj_or_principal with surj | has_max
  · have ⟨iso, iso_fwd_eq_f⟩ := Ty.EmbedIso.ofBij (Function.Bijective.mk f.Injective surj)
    left; constructor
    apply EmbedIso.mk iso
    intro x y xy
    rw [iso_fwd_eq_f]
    dsimp
    apply f.resp.mp
    assumption
    intro x y sxy
    apply f.resp.mpr
    have iso_fwd_eq_f : ∀x, iso.fwd x = f x := by
      intro
      rw [iso_fwd_eq_f]
    rw [←iso_fwd_eq_f, ←iso_fwd_eq_f, iso.rev_fwd, iso.rev_fwd]
    assumption
  · obtain ⟨max, max_prf⟩ := has_max
    right; constructor
    apply PrincipalSeg.mk f.toEmbed_1 max
    apply max_prf

def InitialSeg.trans (h: InitialSeg r t) (g: InitialSeg t s) : InitialSeg r s where
  embed := g.embed ∘ h.embed
  embed_inj := Function.Injective.comp _ _ h.embed_inj g.embed_inj
  resp := by
    intro x y
    apply Iff.trans _ g.resp
    apply Iff.trans _ h.resp
    rfl
  init := by
    intro b a
    dsimp
    intro r₀
    have ⟨x, prf⟩  := g.init _ _ r₀
    subst prf
    replace r₀ := g.resp.mpr r₀
    have ⟨x, prf⟩  := h.init _ _ r₀
    subst prf
    exact ⟨_, rfl⟩

def PrincipalSeg.transInit (h: PrincipalSeg r t) (g: InitialSeg t s) : PrincipalSeg r s where
  embed := g.embed ∘ h.embed
  embed_inj := Function.Injective.comp _ _ h.embed_inj g.embed_inj
  resp := by
    intro x y
    apply Iff.trans _ g.resp
    apply Iff.trans _ h.resp
    rfl
  top := g.embed h.top
  lt_top := by
    intro x
    apply Iff.intro
    intro s₀
    have ⟨a, prf⟩  := g.init _ _ s₀
    subst prf
    replace s₀ := g.resp.mpr s₀
    obtain ⟨a', prf⟩ := h.lt_top.mp s₀
    subst prf
    exists a'
    dsimp
    intro ⟨x, prf⟩
    subst prf
    apply g.resp.mp
    apply h.lt_top.mpr
    refine ⟨_, rfl⟩

def PrincipalSeg.trans [strans: IsTrans s] (h: PrincipalSeg r t) (g: PrincipalSeg t s) : PrincipalSeg r s := transInit h g.toInitialSeg

def InitialSeg.inv [IsWellOrder s] (h: InitialSeg r s) (g: InitialSeg s r) : ∀x, h.embed (g.embed x) = x := by
  intro b
  erw [InitialSeg.eq (g.trans h) (.refl _)]
  rfl

def InitialSeg.antiymm [swo: IsWellOrder s] (h: InitialSeg r s) (g: InitialSeg s r) : EmbedIso r s where
  fwd := h.embed
  rev := g.embed
  fwd_resp := h.resp.mp
  rev_resp := g.resp.mp
  rev_fwd := InitialSeg.inv _ _
  fwd_rev := by
    intro x
    apply h.embed_inj
    apply InitialSeg.inv _ _

end Relation
