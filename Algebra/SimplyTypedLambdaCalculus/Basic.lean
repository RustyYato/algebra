import Algebra.Vector.Lemmas
import Algebra.Fin.Basic
import Algebra.Nat.Mul
import Algebra.Nat.WellFounded

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

def Term.is_terminal (term: Term ctx ty) : Prop :=
  match term with
  | .Unit => True
  | .Var _ _ _ => True
  | .Abort t _ => t.is_terminal
  | .Lam _ _ body => body.is_terminal
  | .App _ _ func arg =>
    match func with
    | .Lam _ _ _ => False
    | _ => func.is_terminal ∧ arg.is_terminal

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
      apply nat.lt_trans v.valLt
      apply nat.lt_succ_self
      rw [Vector.insert_at_get_lt]
      exact h
    else
      apply Term.Var (fin.mk v.succ.val _) _ _
      exact v.valLt
      unfold fin.val fin.mk
      dsimp
      rw [Vector.insert_at_get_ge]
      rw [fin.val_mk]
      rw [fin.val_mk]
      exact TotalOrder.le_of_not_gt h

#print axioms Term.weaken

def Term.weaken_ctx
  { n:nat }
  { ctx: TypeCtx n }
  (term: Term ctx ty)
  (newty: LamTy) :
  Term (.cons newty ctx) ty := by
  have := term.weaken .zero newty
  unfold Vector.insert_at at this
  exact this

#print axioms Term.weaken_ctx

def Term.extend_ctx
  { n m:nat }
  { ctx: Vector LamTy n }
  (term: Term ctx ty) (ctx': Vector LamTy m) :
  Term (ctx' ++ ctx) ty :=
  match ctx' with
  | .nil => term
  | .cons ty ctx' => (term.extend_ctx ctx').weaken_ctx ty

#print axioms Term.weaken_ctx

def Term.size (term: Term ctx ty) : nat :=
  match term with
  | .Unit => 0
  | .Var _ _ _ => 0
  | .App _ _ func arg => (func.size + arg.size).succ
  | .Lam _ _ body => body.size.succ
  | .Abort body _ => body.size.succ

def Term.subst_at
  { n: nat }
  { ctx: TypeCtx n.succ }
  (term: Term ctx ty)
  (pos: fin n.succ)
  (subst: Term (ctx.remove pos) (ctx.get pos)) : Term (ctx.remove pos) ty :=
  match term with
  | .Unit => .Unit
  | .Abort t ty => .Abort (t.subst_at pos subst) ty
  | .App arg_ty ret_ty func arg => .App arg_ty ret_ty (func.subst_at pos subst) (arg.subst_at pos subst)
  | .Lam arg_ty ret_ty body =>
    .Lam arg_ty ret_ty <| body.subst_at pos.succ <| by
      unfold Vector.get Vector.remove
      dsimp
      exact subst.weaken_ctx arg_ty
  | .Var idx ty' ty_correct => by
    match h:compare idx pos with
    | .eq =>
      have := TotalOrder.eq_of_compare_eq h
      subst idx
      clear h
      subst ty'
      exact subst
    | .lt =>
      have : idx.val < n := by
        apply nat.lt_of_lt_of_le (TotalOrder.lt_of_compare (h: compare idx.val pos.val = .lt))
        apply nat.le_of_lt_succ
        exact pos.valLt
      apply Term.Var (fin.mk idx.val this)
      rw [Vector.remove_get_lt]
      conv => {
        rhs
        rhs
        lhs
        rw [fin.mk_val idx.val this]
      }
      subst ty'
      congr
      rw [fin.val_mk]
      rw [fin.mk_val]
      exact h
    | .gt =>
      have := TotalOrder.gt_of_compare h
      cases idx with
      | zero =>
        have := nat.not_lt_zero this
        contradiction
      | succ idx =>
      apply Term.Var (fin.mk idx.succ.val.pred _)
      rw [Vector.remove_get_ge]
      {
        unfold fin.val nat.pred
        conv in fin.mk idx.val _ => {
          rw [fin.val_mk idx]
        }
        exact ty_correct
      }
      cases n with
      | zero => contradiction
      | succ n =>
      rw [fin.mk_val]
      conv => {
        lhs
        unfold fin.val nat.pred
      }
      dsimp
      apply nat.le_of_lt_succ
      exact this
      intros
      rename_i idx _ _ _
      exact idx.valLt
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
  (subst: Term ctx arg_ty) : Term ctx ty := by
    have := Term.subst_at term .zero (by
      unfold Vector.remove Vector.get
      dsimp
      exact subst)
    unfold Vector.remove at this
    dsimp at this
    exact this

inductive ReductionStep : Term ctx ty -> Term ctx ty -> Type where
| Abort : ∀(body body': Term ctx .Void) ty, ReductionStep body body' -> ReductionStep (.Abort body ty) (.Abort body' ty)
| LamBody :
  ∀arg_ty ret_ty (body body': Term (Vector.cons arg_ty ctx) ret_ty), ReductionStep body body' -> ReductionStep (.Lam arg_ty ret_ty body) (.Lam arg_ty ret_ty body')
| AppFunc :
  ∀arg_ty ret_ty (func func': Term ctx (.Func arg_ty ret_ty)) (arg: Term ctx arg_ty), ReductionStep func func'
    -> ReductionStep (.App arg_ty ret_ty func arg) (.App arg_ty ret_ty func' arg)
| AppArg :
  ∀arg_ty ret_ty (func: Term ctx (.Func arg_ty ret_ty)) (arg arg': Term ctx arg_ty),
    func.is_terminal ->
    ReductionStep arg arg'
    -> ReductionStep (.App arg_ty ret_ty func arg) (.App arg_ty ret_ty func arg')
| Apply :
  ∀arg_ty ret_ty (body: Term (Vector.cons arg_ty ctx) ret_ty) (arg: Term ctx arg_ty) (output: Term ctx ret_ty),
    arg.is_terminal ->
    body.is_terminal ->
    output = body.subst arg ->
    ReductionStep (.App arg_ty ret_ty (.Lam arg_ty ret_ty body) arg) output

infix:60 " ⤳ " => ReductionStep

inductive ReductionStepList : Term ctx ty -> Term ctx ty -> Type where
| Refl : ReductionStepList a a
| Cons : ∀{a b c}, a ⤳ b -> ReductionStepList b c ->  ReductionStepList a c

infix:60 " ⤳* " => ReductionStepList

@[refl]
def ReductionStepList.refl:
  a ⤳* a := Refl

def ReductionStepList.length (red: ReductionStepList a b)  : nat :=
  match red with
  | .Refl => 0
  | .Cons _ list => list.length

instance ReductionStep.never_terminal:
  a ⤳ b -> ¬a.is_terminal := by
  intro red
  induction red with
  | Abort body body' ty red ih => exact ih
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

def ReductionStep.determanistic : a ⤳ b -> a ⤳ c -> b = c := by
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

#print axioms ReductionStep.determanistic

instance ReductionStep.subsingleton: Subsingleton (a ⤳ b) where
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

#print axioms ReductionStep.subsingleton

def ReductionStepList.determanistic (b c: Term ctx ty) :
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
      have := ReductionStep.determanistic x y
      rename_i b
      subst b
      apply ih
      repeat assumption
    }

instance ReductionStepList.subsingleton (b: Term ctx ty) (b_term: b.is_terminal) : Subsingleton (a ⤳* b) where
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

#print axioms ReductionStepList.subsingleton

def ReductionStep.allHEq
  (x: a ⤳ b) (y: a ⤳ c):
  HEq x y := by
  have := x.determanistic y
  subst c
  congr
  apply Subsingleton.allEq

#print axioms ReductionStep.allHEq

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
  CommonReduction (ReductionStepList.Cons x ab) (ReductionStepList.Cons x ac) := by
  intro da ab ac comm
  apply CommonReduction.mk comm.term (ReductionStepList.Cons da comm.red)
  exact comm.to_b
  exact comm.to_c
  exact comm.is_sub_ab
  exact comm.is_sub_ac

def ReductionStepList.commonSubseq
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
      apply ReductionStepList.Cons x xs
      rfl
      apply nat.zero_le
      apply nat.zero_le
    | .Cons y ys =>
      rename_i b₀ b₁
      have := ReductionStep.determanistic x y
      subst b₁
      have := Subsingleton.allEq x y
      subst y
      apply (commonSubseq xs ys).push

#print axioms ReductionStepList.commonSubseq

-- We want to prove that all terms halt
def Term.halts (t: Term ctx ty) : Prop :=
  ∃(t': Term ctx ty) (_red: t ⤳* t'), t'.is_terminal

#print axioms Term.halts

def ReductionStep.extend_left {t u: Term ctx ty} :
  t ⤳ u -> u.halts -> t.halts := by
  intro tu uhalts
  have ⟨ x, r, u_term ⟩ := uhalts
  exists x
  exists (.Cons tu r)

#print axioms ReductionStep.extend_left

def ReductionStep.extend_right {t u: Term ctx ty} :
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
    have := ReductionStep.determanistic tu tb
    subst b
    exists bx

#print axioms ReductionStep.extend_right

def Term.hered_halts (t: Term ctx ty) : Prop :=
  match ty with
  | .Void => False
  | .Unit => t.halts
  | .Func arg_ty ret_ty =>
    t.halts ∧ (∀(arg: Term ctx arg_ty), arg.hered_halts -> (Term.App arg_ty ret_ty t arg).hered_halts)

#print axioms Term.hered_halts

def Term.hered_halt_iff
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
      apply ReductionStep.AppFunc
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
      apply ReductionStep.AppFunc
      assumption

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

def Term.cast_ctx
  (ctx: Vector LamTy n)
  (ctx': Vector LamTy m)
  (h: ctx =v ctx')
  (t: Term ctx ty):
  Term ctx' ty := by
  cases h
  exact t

def Term.subst_all { n: nat } { ctx: TypeCtx n } (e: Term ctx ty)
  (bindings: BindingList ctx)
  : Term .nil ty :=
  match ctx with
  | .nil => e
  | .cons ty' ctx =>
  match bindings with
  | .cons t _ _ bindings' => by
    apply (Term.subst e _).subst_all bindings'
    apply Term.cast_ctx
    exact Vector.append_nil ctx
    exact t.extend_ctx ctx

def Term.hered_halt
  (e: Term ctx ty) :
  (e.subst_all bindings).hered_halts := by
  induction e with
  | Unit =>
    unfold subst_all
    rename_i ctx
    cases ctx
    exists .Unit
    exists .Refl
    cases bindings
    dsimp
  | Var idx ty ty_correct =>
    rename_i ctx
    have := bindings.get_halts idx
    cases ty with
    | Void =>
      have := Term.void_not_hered_halt _ ty_correct.symm this
      contradiction
    | Unit =>
      exists .Var idx .Unit ty_correct
      exists .Refl
    | Func arg_ty ret_ty =>
      unfold hered_halts
      apply And.intro
      admit
      admit
