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

inductive Lex (alt: α -> α -> Prop) (blt: β -> β -> Prop) : α ⊕ β -> α ⊕ β -> Prop where
| inl : alt x y -> Lex alt blt (inl x) (inl y)
| inl_inr: Lex alt blt (inl x) (inr y)
| inr : blt x y -> Lex alt blt (inr x) (inr y)

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
        apply this
        exact ih _ r

instance
  LexIsTrans
  [Relation.IsTrans alt]
  [Relation.IsTrans blt] : Relation.IsTrans (Lex alt blt) where
  trans := by
    intro a b c ab bc
    cases ab <;> cases bc
    any_goals apply Lex.inl
    any_goals apply Lex.inr
    any_goals apply Lex.inl_inr
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
    any_goals apply Or.inl Lex.inl_inr
    any_goals apply Or.inr (Or.inr Lex.inl_inr)
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

def InitialSeg.surj_or_principal
  [rwo: IsWellOrder r] [swo: IsWellOrder s] (f: InitialSeg r s):
  Function.Surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x := by
  apply ClassicLogic.or_iff_not_imp_right.mpr
  intro h
  replace h := not_exists.mp h
  replace h :
    ∀ (x : β), ∃(z : β), ¬(s z x ↔ ∃ y, f.embed y = z)
    := by
    intro x
    replace h := h x
    rw [ClassicLogic.not_forall] at h
    exact h
  intro x
  have ⟨z, prf⟩ := h x
  rw [ClassicLogic.not_iff] at prf

  -- apply PSum.inr
  sorry

end Relation
