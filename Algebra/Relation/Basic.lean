import Algebra.WellFounded
import Algebra.Ty.Basic
import Algebra.Function.Basic
import Algebra.ClassicLogic

namespace Relation

variable (rel: α -> α -> Prop)
variable {r: α -> α -> Prop} {s: β -> β -> Prop}

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
def EmbedIso.symm (e: EmbedIso r s) : EmbedIso s r := by
  apply EmbedIso.mk e.toEmbedIso.symm
  exact e.rev_resp
  exact e.fwd_resp

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
variable {r: α -> α -> Prop} {s: β -> β -> Prop}

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

end Relation
