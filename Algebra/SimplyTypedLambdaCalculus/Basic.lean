import Algebra.Vector.Basic
import Algebra.Fin.Basic
import Algebra.Nat.Mul
import Algebra.Nat.WellFounded
import Algebra.AxiomBlame

-- a type in simply typed lambda calculus
inductive LamTy where
-- the most primitive type
| Unit
-- no term should have the type void
| Void
-- the function type
| Func (arg: LamTy) (ret: LamTy)

def TypeCtx (n: nat) := Vector LamTy n

inductive Term : TypeCtx n -> LamTy -> Type where
-- The only primitive, unit
| Unit : Term ctx .Unit
| Var : { ctx: TypeCtx n } -> (id: fin n) -> ∀ty, ty = ctx.get id -> Term ctx ty
-- The principle of explosion, if you can "prove" void, then you
-- can write a term for any type
| Abort : Term ctx .Void -> ∀ty, Term ctx ty
-- Create a new function that takes an argument and produces a value of type ret_ty
| Lam : ∀(arg_ty ret_ty: LamTy), (body: Term (Vector.cons arg_ty ctx) ret_ty) -> Term ctx (.Func arg_ty ret_ty)
-- Function application
| App: ∀(arg_ty ret_ty: LamTy), Term ctx (.Func arg_ty ret_ty) -> Term ctx arg_ty -> Term ctx ret_ty

def Term.recursion
  { motive: ∀{n} (ctx: TypeCtx n) {ty}, Term ctx ty -> Sort _ }
  (Unit: ∀{n} {ctx: TypeCtx n}, motive ctx .Unit)
  (Var: ∀{n} {ctx: TypeCtx n}, ∀id ty h, motive ctx (.Var id ty h))
  (Abort: ∀{n} {ctx: TypeCtx n}, ∀body ty, motive ctx body -> motive ctx (.Abort body ty))
  (Lam: ∀{n} {ctx: TypeCtx n}, ∀arg_ty ret_ty body, motive (.cons arg_ty ctx) body -> motive ctx (.Lam arg_ty ret_ty body))
  (App: ∀{n} {ctx: TypeCtx n}, ∀arg_ty ret_ty arg func, motive ctx arg -> motive ctx func -> motive ctx (.App arg_ty ret_ty arg func))
  {ctx: TypeCtx n} {ty}
  : ∀(t: Term ctx ty), motive ctx t
| .Unit => Unit
| .Var _ _ _ => Var _ _ _
| .Abort _ ty => Abort _ _ (recursion Unit Var Abort Lam App _)
| .Lam _ _ _ => Lam _ _ _ (recursion Unit Var Abort Lam App _)
| .App _ ret_ty _ _ => App _ _ _ _ (recursion Unit Var Abort Lam App _) (recursion Unit Var Abort Lam App _)

def Term.size (term: Term ctx ty) : nat :=
  match term with
  | .Unit => 0
  | .Var _ _ _ => 0
  | .App _ _ func arg => (func.size + arg.size).succ
  | .Lam _ _ body => body.size.succ
  | .Abort body _ => body.size.succ

def Term.is_terminal (term: Term ctx ty) : Prop :=
  match term with
  | .Unit => True
  | .Var _ _ _ => True
  -- | .Abort t _ => False
  | .Abort t _ => t.is_terminal
  | .Lam _ _ body => body.is_terminal
  | .App _ _ func arg =>
    match func with
    | .Lam _ _ _ => False
    | _ => func.is_terminal ∧ arg.is_terminal

instance : Decidable (Term.is_terminal term) := by
  apply term.recursion
  intros; exact inferInstanceAs (Decidable True)
  intros; exact inferInstanceAs (Decidable True)
  intros _ _ _ _ h; exact h
  intros _ _ _ _ _ h; exact h
  intro _ _ _ _ _ _ arg_dec func_dec
  unfold Term.is_terminal
  split
  exact inferInstance
  exact inferInstance

def Term.weaken
  { n:nat }
  { ctx: TypeCtx n }
  (term: Term ctx ty)
  (idx: fin n.succ)
  (newty: LamTy) :
  Term (ctx.insert_at idx newty) ty := by
  match term with
  | Unit => exact .Unit
  | Abort t ty =>
    apply Term.Abort _ ty
    apply t.weaken
  | Lam arg_ty ret_ty body =>
    apply Term.Lam arg_ty ret_ty
    exact body.weaken idx.succ newty
  | App arg_ty _ func arg =>
    apply Term.App arg_ty
    apply func.weaken
    apply arg.weaken
  | Var v _ _ =>
    subst ty
    if h:v.val < idx.val then
      apply Term.Var (fin.mk v.val _) _ _
      apply lt_trans v.isLt
      apply nat.lt_succ_self
      rw [Vector.insert_at_get_lt]
      exact h
    else
      apply Term.Var (fin.mk v.succ.val _) _ _
      exact v.isLt
      unfold fin.val fin.mk
      dsimp
      rw [Vector.insert_at_get_ge]
      rw [fin.val_mk]
      rw [fin.val_mk]
      apply le_of_not_lt
      assumption
termination_by term.size
decreasing_by
  any_goals apply nat.lt_succ_self
  rw [size, ←nat.add_succ]
  apply nat.add.lt_right_nz
  trivial
  rw [size, ←nat.succ_add]
  apply nat.add.lt_left_nz
  trivial

def Term.weaken_ctx
  { n:nat }
  { ctx: TypeCtx n }
  (term: Term ctx ty)
  (newty: LamTy) :
  Term (.cons newty ctx) ty := term.weaken .zero newty

def Term.extend_ctx
  { n m:nat }
  { ctx: Vector LamTy n }
  (term: Term ctx ty) (ctx': Vector LamTy m) :
  Term (ctx' ++ ctx) ty :=
  ctx'.recursion ( motive := fun ctx' => Term (ctx' ++ ctx) ty )
    term (fun ty _ ih => ih.weaken_ctx ty)

def Term.set_ctx
  { m: nat }
  (term: Term .nil ty) (ctx': Vector LamTy m) :
  Term ctx' ty :=
  ctx'.recursion ( motive := fun ctx' => Term ctx' ty )
    term (fun ty _ ih => ih.weaken_ctx ty)

def Term.subst_at
  { n: nat }
  { ctx: TypeCtx n }
  (term: Term ctx ty)
  (pos: fin n)
  (subst: Term (ctx.remove pos) (ctx.get pos)) : Term (ctx.remove pos) ty :=
  match n with
  | .succ n =>
  match term with
  | .Unit => .Unit
  | .Abort t ty => .Abort (t.subst_at pos subst) ty
  | .App arg_ty ret_ty func arg => .App arg_ty ret_ty (func.subst_at pos subst) (arg.subst_at pos subst)
  | .Lam arg_ty ret_ty body =>
    .Lam arg_ty ret_ty <| body.subst_at pos.succ <| subst.weaken_ctx arg_ty
  | .Var idx ty' ty_correct => by
    match h:compare idx pos with
    | .eq =>
      have := eq_of_compare_eq h
      subst idx
      clear h
      subst ty'
      exact subst
    | .lt =>
      have : idx.val < n := by
        apply lt_of_lt_of_le
        apply (lt_of_compare (h: compare idx.val pos.val = .lt))
        apply nat.le_of_lt_succ
        exact pos.isLt
      apply Term.Var (fin.mk idx.val this)
      rw [Vector.remove_get_lt]
      assumption
      assumption
    | .gt =>
      have := gt_of_compare h
      cases idx with
      | zero =>
        have := nat.not_lt_zero this
        contradiction
      | succ idx =>
      apply Term.Var (fin.mk idx.val _)
      rw [Vector.remove_get_ge, fin.val_mk]
      assumption
      rw [fin.mk_val]
      apply nat.le_of_lt_succ
      assumption
termination_by term.size
decreasing_by
  apply nat.lt_succ_self
  apply nat.lt_succ_of_le
  apply nat.add.le_left
  apply nat.lt_succ_of_le
  apply nat.add.le_right
  apply nat.lt_succ_self

#print axioms Term.subst_at

def Term.subst
  { n: nat }
  { ctx: TypeCtx n }
  (term: Term (Vector.cons arg_ty ctx) ty)
  (subst: Term ctx arg_ty) : Term ctx ty := Term.subst_at term .zero subst

#print axioms Term.subst

inductive Reduction : Term ctx ty -> Term ctx ty -> Type where
| Abort : ∀(body body': Term ctx .Void) ty, Reduction body body' -> Reduction (.Abort body ty) (.Abort body' ty)
| LamBody :
  ∀arg_ty ret_ty (body body': Term (Vector.cons arg_ty ctx) ret_ty), Reduction body body' -> Reduction (.Lam arg_ty ret_ty body) (.Lam arg_ty ret_ty body')
| AppFunc :
  ∀arg_ty ret_ty (func func': Term ctx (.Func arg_ty ret_ty)) (arg: Term ctx arg_ty), Reduction func func'
    -> Reduction (.App arg_ty ret_ty func arg) (.App arg_ty ret_ty func' arg)
| AppArg :
  ∀arg_ty ret_ty (func: Term ctx (.Func arg_ty ret_ty)) (arg arg': Term ctx arg_ty),
    func.is_terminal ->
    Reduction arg arg'
    -> Reduction (.App arg_ty ret_ty func arg) (.App arg_ty ret_ty func arg')
| Apply :
  ∀arg_ty ret_ty (body: Term (Vector.cons arg_ty ctx) ret_ty) (arg: Term ctx arg_ty) (output: Term ctx ret_ty),
    arg.is_terminal ->
    body.is_terminal ->
    output = body.subst arg ->
    Reduction (.App arg_ty ret_ty (.Lam arg_ty ret_ty body) arg) output

infix:60 " ⤳ " => Reduction

inductive ReductionChain : Term ctx ty -> Term ctx ty -> Type where
| Refl : ReductionChain a a
| Cons : ∀{a b c}, a ⤳ b -> ReductionChain b c ->  ReductionChain a c

infix:60 " ⤳* " => ReductionChain

@[refl]
def ReductionChain.refl:
  a ⤳* a := Refl

def ReductionChain.length (red: ReductionChain a b)  : nat :=
  match red with
  | .Refl => 0
  | .Cons _ list => list.length.succ

instance Reduction.never_terminal:
  a ⤳ b -> ¬a.is_terminal := by
  intro red
  induction red with
  | Abort body body' ty red ih => exact ih
  -- | Abort body body' ty red ih => exact False.elim
  | LamBody arg_ty ret_ty body body'  red ih => exact ih
  | AppFunc arg_ty ret_ty func func' arg red ih =>
    intro t
    apply ih
    unfold Term.is_terminal at t
    cases func
    any_goals (have ⟨ _, _ ⟩ := t; assumption; done)
    contradiction
  | AppArg arg_ty ret_ty func arg arg' func_term red ih =>
    intro t
    apply ih
    unfold Term.is_terminal at t
    cases func
    any_goals (have ⟨ _, _ ⟩ := t; assumption; done)
    contradiction
  | Apply arg_ty ret_ty body arg output arg_term body_term output_correct =>
    unfold Term.is_terminal
    dsimp
    exact id

instance Reduction.of_not_terminal:
  ¬a.is_terminal -> (b: Term ctx ty) × (a ⤳ b) := by
  apply a.recursion
  case Unit =>
    intro n ctx not_term
    unfold Term.is_terminal at not_term
    contradiction
  case Var =>
    intro n ctx id ty h not_term
    unfold Term.is_terminal at not_term
    contradiction
  case Lam =>
    intro n ctx arg_ty ret_ty body ih not_term
    have ⟨body',red⟩  := ih not_term
    exists body'.Lam _ _
    apply Reduction.LamBody
    assumption
  case Abort =>
    intro n ctx body ty ih not_term
    have ⟨body',red⟩  := ih not_term
    exists body'.Abort _
    apply Reduction.Abort
    assumption
  case App =>
    intro n ctx arg_ty ret_ty func arg func_ih arg_ih not_term
    unfold Term.is_terminal at not_term
    if func_term:func.is_terminal then
    if arg_term:arg.is_terminal then
    split at not_term
    clear not_term func_ih arg_ih
    rename_i func body
    exists body.subst arg
    apply Reduction.Apply
    assumption
    assumption
    rfl
    have := not_term ⟨func_term,arg_term⟩
    contradiction
    else
    have ⟨arg',red⟩ := arg_ih arg_term
    exists .App _ _ func arg'
    apply Reduction.AppArg
    repeat assumption
    else
    have ⟨func',red⟩ := func_ih func_term
    exists .App _ _ func' arg
    apply Reduction.AppFunc
    repeat assumption

def Reduction.determanistic : a ⤳ b -> a ⤳ c -> b = c := by
  intro a_to_b a_to_c
  induction a_to_b with
  | Abort body body' ty red ih =>
    cases a_to_c
    congr
    apply ih
    assumption
  | LamBody arg_ty ret_ty body body' red ih =>
    cases a_to_c
    congr
    apply ih
    assumption
  | AppFunc arg_ty ret_ty func func' arg red ih =>
    cases a_to_c
    congr
    apply ih
    assumption
    rename_i h
    have := red.never_terminal
    contradiction
    have := red.never_terminal
    contradiction
  | AppArg arg_ty ret_ty func arg arg' func_term red ih =>
    cases a_to_c
    rename_i h
    have := h.never_terminal
    contradiction
    congr
    apply ih
    assumption
    have := red.never_terminal
    contradiction
  | Apply arg_ty ret_ty body arg output arg_term body_term out_def =>
    cases a_to_c
    rename_i h
    have := h.never_terminal
    contradiction
    rename_i h
    have := h.never_terminal
    contradiction
    subst c
    subst output
    rfl

#print axioms Reduction.determanistic

instance Reduction.subsingleton: Subsingleton (a ⤳ b) where
  allEq := by
    intro x y
    induction x with
    | Abort xbody xbody' xty xred xih =>
      cases y
      congr
      apply xih
    | LamBody arg_ty ret_ty body body' red ih =>
      cases y
      congr
      apply ih
    | AppFunc arg_ty ret_ty func func' arg red ih =>
      cases y
      congr
      apply ih
      have := red.never_terminal
      contradiction
      have := red.never_terminal
      contradiction
    | AppArg arg_ty ret_ty func arg arg' func_term red ih =>
      cases y
      rename_i red'
      have := red'.never_terminal
      contradiction
      congr
      apply ih
      have := red.never_terminal
      contradiction
    | Apply arg_ty ret_ty body arg output arg_term body_term output_correct =>
      cases y
      rename_i body_red
      have := body_red.never_terminal
      contradiction
      rename_i arg_red
      have := arg_red.never_terminal
      contradiction
      congr

#print axioms Reduction.subsingleton

def ReductionChain.determanistic (b c: Term ctx ty) :
  b.is_terminal -> c.is_terminal ->
  a ⤳* b -> a ⤳* c -> b = c := by
  intro b_term c_term x y
  induction x with
  | Refl =>
    cases y
    rfl
    rename_i h _
    have := h.never_terminal
    contradiction
  | Cons x _ ih =>
    cases y
    {
      have := x.never_terminal
      contradiction
    }
    {
      rename_i y ys
      have := Reduction.determanistic x y
      rename_i b
      subst b
      apply ih
      repeat assumption
    }

instance ReductionChain.subsingleton (b: Term ctx ty) (b_term: b.is_terminal) : Subsingleton (a ⤳* b) where
  allEq := by
    intro x y
    induction x with
    | Refl =>
      cases y
      rfl
      rename_i h _
      have := h.never_terminal
      contradiction
    | Cons x xs ih =>
      cases y
      have := x.never_terminal
      contradiction
      rename_i x₀ x₁ x₂ y₀ x₀_to_y₀ y₀_to_x₂
      have := x.determanistic x₀_to_y₀
      subst y₀
      congr
      apply Subsingleton.allEq
      apply ih
      assumption

#print axioms ReductionChain.subsingleton

def Reduction.allHEq
  (x: a ⤳ b) (y: a ⤳ c):
  HEq x y := by
  have := x.determanistic y
  subst c
  congr
  apply Subsingleton.allEq

#print axioms Reduction.allHEq

structure CommonReduction { ctx: TypeCtx n } { a b c: Term ctx ty } (ab: a ⤳* b) (ac: a ⤳* c) where
  term: Term ctx ty
  red: a ⤳* term
  to_b: term ⤳* b
  to_c: term ⤳* c

  is_sub_ab: red.length ≤ ab.length
  is_sub_ac: red.length ≤ ac.length

def CommonReduction.push
  { a b c d: Term ctx ty }:
  (x: d ⤳ a) ->
  (ab: a ⤳* b) ->
  (ac: a ⤳* c) ->
  (red: CommonReduction ab ac) ->
  CommonReduction (ReductionChain.Cons x ab) (ReductionChain.Cons x ac) := by
  intro da ab ac comm
  apply CommonReduction.mk comm.term (ReductionChain.Cons da comm.red)
  exact comm.to_b
  exact comm.to_c
  exact comm.is_sub_ab
  exact comm.is_sub_ac

def ReductionChain.commonSubseq
  { a b c: Term ctx ty }
  (x: a ⤳* b) (y: a ⤳* c):
  CommonReduction x y := by
  match x with
  | .Refl =>
    apply CommonReduction.mk a .Refl
    rfl
    assumption
    apply nat.zero_le
    apply nat.zero_le
  | .Cons x xs =>
    match y with
    | .Refl =>
      apply CommonReduction.mk a .Refl
      apply ReductionChain.Cons x xs
      rfl
      apply nat.zero_le
      apply nat.zero_le
    | .Cons y ys =>
      rename_i b₀ b₁
      have := Reduction.determanistic x y
      subst b₁
      have := Subsingleton.allEq x y
      subst y
      apply (commonSubseq xs ys).push

#print axioms ReductionChain.commonSubseq

-- We want to prove that all terms halt
def Term.halts (t: Term ctx ty) : Prop :=
  ∃(t': Term ctx ty) (_red: t ⤳* t'), t'.is_terminal

#print axioms Term.halts

def Reduction.extend_left {t u: Term ctx ty} :
  t ⤳ u -> u.halts -> t.halts := by
  intro tu uhalts
  have ⟨ x, r, u_term ⟩ := uhalts
  exists x
  exists (.Cons tu r)

#print axioms Reduction.extend_left

def Reduction.extend_right {t u: Term ctx ty} :
  t ⤳ u -> t.halts -> u.halts := by
  intro tu uhalts
  have ⟨ x, r, u_term ⟩ := uhalts
  cases r with
  | Refl =>
    have := tu.never_terminal
    contradiction
  | Cons tb bx =>
    rename_i b
    exists x
    have := Reduction.determanistic tu tb
    subst b
    exists bx

#print axioms Reduction.extend_right

def Term.hered_halts (t: Term ctx ty) : Prop :=
  match ty with
  | .Void => False
  | .Unit => t.halts
  | .Func arg_ty ret_ty =>
    t.halts ∧ (∀(arg: Term ctx arg_ty), arg.hered_halts -> (Term.App arg_ty ret_ty t arg).hered_halts)

#print axioms Term.hered_halts

def Term.hered_halts.halts (t: Term ctx ty) : t.hered_halts -> t.halts := by
  intro h
  match ty with
  | .Void => contradiction
  | .Unit => exact h
  | .Func arg_ty ret_ty => exact h.left

def Term.hered_halt_iff_red
  (e e': Term ctx ty) :
  e ⤳ e' ->
  (e.hered_halts ↔ e'.hered_halts) := by
  intro red
  induction ty with
  | Void =>
    apply Iff.intro
    case mp => exact id
    case mpr => exact id
  | Unit =>
    apply Iff.intro
    case mp =>
      intro e_halts
      apply red.extend_right e_halts
    case mpr =>
      intro e'_halts
      apply red.extend_left e'_halts
  | Func arg_ty ret_ty _arg_ih ret_ih =>
    apply Iff.intro
    case mp =>
      intro e_hered_halts
      have ⟨ e_halts, preserve_halt ⟩ := e_hered_halts
      apply And.intro
      apply red.extend_right e_halts
      intro arg arg_hered_halt
      apply (ret_ih _ _ _).mp
      apply preserve_halt
      assumption
      apply Reduction.AppFunc
      assumption
    case mpr =>
      intro e'_hered_halts
      have ⟨ e'_halts, preserve_halt ⟩ := e'_hered_halts
      apply And.intro
      apply red.extend_left e'_halts
      intro arg arg_hered_halt
      apply (ret_ih (.App arg_ty ret_ty e arg) (.App arg_ty ret_ty e' arg) _).mpr
      apply preserve_halt
      assumption
      apply Reduction.AppFunc
      assumption

def Term.hered_halt_iff_red_chain
  (e e': Term ctx ty) :
  e ⤳* e' ->
  (e.hered_halts ↔ e'.hered_halts) := by
  intro h
  induction h with
  | Refl => rfl
  | Cons red _ ih =>
    apply Iff.trans _ ih
    apply Term.hered_halt_iff_red
    exact red

inductive BindingList : { n: nat } -> (ctx: TypeCtx n) -> Type where
| nil : BindingList .nil
| cons : (t: Term .nil ty) -> t.is_terminal -> t.hered_halts -> BindingList ctx -> BindingList (.cons ty ctx)

def BindingList.get { ctx: TypeCtx n }  (bindings: BindingList ctx) (x: fin n) : Term .nil (ctx.get x) :=
  match bindings, x with
  | .cons t _ _ _, .zero => t
  | .cons _ _ _ bindings, .succ x => bindings.get x

def BindingList.get_is_terminal { ctx: TypeCtx n } (bindings: BindingList ctx) (x: fin n) :
  (bindings.get x).is_terminal :=
  match bindings, x with
  | .cons _ t _ _, .zero => t
  | .cons _ _ _ bindings, .succ x => bindings.get_is_terminal x

def BindingList.get_halts { ctx: TypeCtx n } (bindings: BindingList ctx) (x: fin n) :
  (bindings.get x).hered_halts :=
  match bindings, x with
  | .cons _ _ t _, .zero => t
  | .cons _ _ _ bindings, .succ x => bindings.get_halts x

def Term.void_not_hered_halt:
  (t: Term ctx ty) -> ty = .Void -> ¬t.hered_halts := by
  intro t _
  subst ty
  intro
  contradiction

def Term.subst_all { n: nat } { ctx: TypeCtx n } (e: Term ctx ty)
  (bindings: BindingList ctx) : Term .nil ty :=
  match bindings with
  | .nil => e
  | .cons t _ _ bindings' => by
    apply (Term.subst e _).subst_all bindings'
    apply t.set_ctx

def Term.weaken_hered_halts_iff (e: Term ctx ty) :
  ((e.weaken idx ty').hered_halts ↔ e.hered_halts) := by
  induction e with
  | Unit =>
    unfold weaken
    apply Iff.intro
    · intro h
      exists Unit
      exists .Refl
    · intro h
      exists Unit
      exists .Refl
  | Abort body ty ih =>
    apply Iff.intro
    · intro h
      unfold weaken at h
      cases ty
      have ⟨e',chain,e'_term⟩ := h

      sorry
    · intro h
      sorry
  | Lam => sorry
  | App => sorry
  | Var => sorry

def Term.weaken_ctx_hered_halts_iff (e: Term ctx ty) :
  ((e.weaken_ctx ty').hered_halts ↔ e.hered_halts) := by
  apply Term.weaken_hered_halts_iff

def Term.set_ctx_hered_halts_iff (e: Term .nil ty) :
  ((e.set_ctx ctx').hered_halts ↔ e.hered_halts) := by
  induction ctx' using Vector.ind generalizing e
  rfl
  rename_i ih
  apply Iff.intro
  · intro h
    unfold set_ctx at h
    have := (weaken_ctx_hered_halts_iff _).mp h
    exact (ih _).mp this
  · intro h
    apply (weaken_ctx_hered_halts_iff _).mpr
    apply (ih _).mpr
    assumption

def Term.abort_chain' (body: Term ctx .Void)  (ty: LamTy) (e: Term ctx ty):
  (n: nat) ->
  (h: (body.Abort ty) ⤳* e) ->
  h.length = n ->
  ∃body': Term ctx .Void, e = body'.Abort ty := by
  intro n chain h
  match n with
  | .zero =>
    cases chain
    exists body
    contradiction
  | .succ n =>
    cases chain
    contradiction
    rename_i red chain
    cases red
    have ⟨body',eq⟩ := abort_chain' _ _ _ n chain (nat.succ.inj h)
    exists body'

def Term.abort_chain (body: Term ctx .Void)  (ty: LamTy) (e: Term ctx ty):
  (body.Abort ty) ⤳* e -> ∃body': Term ctx .Void, e = body'.Abort ty := by
  intro chain
  apply body.abort_chain' ty e _ chain
  rfl

def Term.subst_hered_halts_iff { n: nat } { ctx: TypeCtx n } (e: Term ctx ty)
  (pos: fin n)
  (arg: Term (ctx.remove pos) (ctx.get pos)) :
  arg.hered_halts ->
  ((e.subst_at pos arg).hered_halts ↔ e.hered_halts) := by
  intro arg_hered_halts
  induction e with
  | Unit =>
    rename_i n _
    match n with
    | .succ n =>
    unfold subst_at
    dsimp
    apply Iff.intro
    · intro h
      exists Unit
      exists .Refl
    · intro h
      exists Unit
      exists .Refl
  | Abort body ty ih =>
    rename_i n _
    match n with
    | .succ n =>
    unfold subst_at
    dsimp
    apply Iff.intro
    · intro h
      cases ty
      any_goals contradiction
      have ⟨e',chain,e'_term⟩ := h
      have ⟨body',_⟩ := abort_chain _ _ _ chain
      subst e'
      contradiction
      have ⟨⟨e',chain,e'_term⟩,_⟩  := h
      have ⟨body',_⟩ := abort_chain _ _ _ chain
      subst e'
      contradiction
    · intro h
      cases ty
      any_goals contradiction
      have ⟨e',chain,e'_term⟩ := h
      have ⟨body',_⟩ := abort_chain _ _ _ chain
      subst e'
      contradiction
      have ⟨⟨e',chain,e'_term⟩,_⟩  := h
      have ⟨body',_⟩ := abort_chain _ _ _ chain
      subst e'
      contradiction
  | Lam => sorry
  | App => sorry
  | Var => sorry
  -- apply Iff.intro
  -- · intro h
  --   sorry
  -- · intro h
  --   sorry

def Term.subst_all_hered_halts_iff { n: nat } { ctx: TypeCtx n } (e: Term ctx ty)
  (bindings: BindingList ctx) :
    (e.subst_all bindings).hered_halts ↔ e.hered_halts := by
  induction bindings with
  | nil => rfl
  | cons arg arg_term arg_hered_halts bindings ih =>
    apply Iff.intro
    · intro h
      unfold subst_all at h
      apply (subst_hered_halts_iff _ _ _ _).mp ((ih _).mp h)
      apply (set_ctx_hered_halts_iff _).mpr
      assumption
    · intro h
      unfold subst_all
      apply (ih _).mpr
      apply (subst_hered_halts_iff _ _ _ _).mpr
      assumption
      apply (set_ctx_hered_halts_iff _).mpr
      assumption

def Term.subst_all_red_hered_halts { n: nat } { ctx: TypeCtx n } (e e': Term ctx ty)
  (bindings: BindingList ctx) :
    e ⤳ e' ->
    ((e.subst_all bindings).hered_halts ↔
    (e'.subst_all bindings).hered_halts) := by
  intro red
  sorry
def Term.subst_all_chain_hered_halts { n: nat } { ctx: TypeCtx n } (e e': Term ctx ty)
  (bindings: BindingList ctx) :
    e ⤳* e' ->
    ((e.subst_all bindings).hered_halts ↔
    (e'.subst_all bindings).hered_halts) := by
  intro chain
  induction chain with
  | Refl => rfl
  | Cons red _ ih =>
    apply Iff.trans _ ih
    apply subst_all_red_hered_halts
    assumption

def Term.subst_all_unit { n: nat } { ctx: TypeCtx n }
  (bindings: BindingList ctx)
  : Term.Unit.subst_all bindings = Term.Unit := by
  induction bindings with
  | nil => rfl
  | cons b b_is_term b_hered_halts bindings ih =>
    unfold subst_all subst subst_at
    rw [ih]

#print axioms Term.subst_all_unit

-- def Term.subst_all_lam { n: nat } { ctx: TypeCtx n }
--   (bindings: BindingList ctx)
--   (body: Term (.cons arg_ty ctx) ret_ty)
--   : ((Term.Lam arg_ty ret_ty body): Term ctx (.Func arg_ty ret_ty)).subst_all bindings = (Term.Lam arg_ty ret_ty (body.subst_all bindings)) := by
--   induction bindings with
--   | nil => rfl
--   | cons b b_is_term b_hered_halts bindings ih =>
--     unfold subst_all subst subst_at
--     rw [ih]

-- #print axioms Term.subst_all_unit

def Term.hered_halt
  (e: Term ctx ty) (bindings: BindingList ctx) :
  (e.subst_all bindings).hered_halts := by
  induction e with
  | Unit =>
    rw [subst_all_unit]
    unfold hered_halts halts
    exists Unit
    exists .Refl
  | Abort term ty₀ ih =>
    have : False := @ih bindings
    contradiction
  | Lam arg_ty ret_ty body ih =>
    apply And.intro
    dsimp
    sorry
    · intro arg arg_hered_halts
      have ⟨arg',arg_chain,arg'_term⟩ := arg_hered_halts.halts
      have := ih (.cons arg' arg'_term ((hered_halt_iff_red_chain _ _ arg_chain).mp arg_hered_halts) bindings)

      apply (hered_halt_iff_red_chain _ _ _).mpr _
      apply body.subst_all (.cons _ _ _ bindings)
      exact arg'
      exact arg'_term
      apply (hered_halt_iff_red_chain _ _ _).mp
      exact arg_hered_halts
      assumption
      · induction bindings with
        | nil =>
          unfold subst_all
          apply ReductionChain.Cons
          apply Reduction.AppArg


          sorry
        | cons =>
          sorry
      · apply ih
  | App => sorry
  | Var idx ty ty_correct =>
    sorry
    -- rename_i ctx
    -- have := bindings.get_halts idx
    -- cases ty with
    -- | Void =>
    --   have := Term.void_not_hered_halt _ ty_correct.symm this
    --   contradiction
    -- | Unit =>
    --   exists .Var idx .Unit ty_correct
    --   exists .Refl
    -- | Func arg_ty ret_ty =>
    --   unfold hered_halts
    --   apply And.intro
    --   admit
    --   admit
