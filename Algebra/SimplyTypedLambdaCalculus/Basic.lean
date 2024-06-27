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
        apply nat.lt_of_lt_and_le (TotalOrder.lt_of_compare (h: compare idx.val pos.val = .lt))
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
  { ctx: TypeCtx n.succ }
  (term: Term (Vector.cons arg_ty ctx) ty)
  (subst: Term ctx arg_ty) : Term ctx ty :=
  Term.subst_at term .zero subst

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
| Refl : ∀(a: Term ctx ty), a.is_terminal -> ReductionStepList a a
| Cons : ∀{a b c}, a ⤳ b -> ReductionStepList b c ->  ReductionStepList a c

infix:60 " ~~> " => ReductionStepList

def ReductionStepList.length (red: ReductionStepList a b)  : nat :=
  match red with
  | .Refl _ _ => 0
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

def ReductionStepList.subsingleton : Subsingleton (a ~~> b) where
  allEq := by
    intro x y
    induction x with
    | Refl x x_term =>
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

#print axioms ReductionStepList.subsingleton

def ReductionStep.allHEq
  (x: a ⤳ b) (y: a ⤳ c):
  HEq x y := by
  have := x.determanistic y
  subst c
  congr
  apply Subsingleton.allEq

#print axioms ReductionStep.allHEq
