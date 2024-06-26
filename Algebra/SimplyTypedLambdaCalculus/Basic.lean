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
  | .Var _ _ (.refl _) => True
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

-- inductive Subst :
--   ∀{ n: nat } { ctx: TypeCtx n.succ } (pos: fin n.succ) (subst_ty ty: LamTy),
--   -- the substituted value should have type `subst_ty` in the context where
--   -- the substituted variable at pos is removed
--   (subst: Term (ctx.remove pos) subst_ty) ->
--   -- the term before the substitution
--   (before: Term ctx ty) ->
--   -- the term after the substitution
--   -- note that it must have the same type
--   -- as before the substitution and in the
--   -- context where the variable at pos is removed
--   (after: Term (ctx.remove pos) ty) -> Type where
--   | Unit : Subst pos subst_ty .Unit subst .Unit .Unit
--   | VarEq : Subst pos subst_ty subst_ty subst (.Var pos _ refl) subst
--   | VarLt :
--     ∀{n: nat} { ctx: TypeCtx n.succ } { pos idx: fin n.succ} {subst_ty: LamTy}
--       {subst: Term (ctx.remove pos) subst_ty},
--       (idx_lt_pos: idx < pos) ->
--     Subst pos subst_ty (ctx.get idx) subst (.Var idx (ctx.get idx) rfl) (by
--       apply Term.Var (fin.mk idx.val _)
--       rw [Vector.remove_get_lt]
--       conv => {
--         rhs
--         rhs
--         conv => {
--           lhs
--           rw [fin.mk_val _ (by
--             apply nat.lt_of_lt_and_le idx_lt_pos
--             apply nat.le_of_lt_succ
--             exact pos.valLt)]
--         }
--       }
--       rw [fin.val_mk]
--       rw [fin.mk_val]
--       assumption)
--   | VarGt :
--     ∀{n: nat} { ctx: TypeCtx n.succ } { pos idx: fin n.succ} {subst_ty: LamTy}
--       {subst: Term (ctx.remove pos) subst_ty},
--       (idx_gt_pos: idx > pos) ->
--     Subst pos subst_ty (ctx.get idx) subst (.Var idx (ctx.get idx) rfl) (by
--       apply Term.Var (fin.mk idx.val.pred _) _ _
--       {
--         cases idx
--         have := nat.not_lt_zero idx_gt_pos
--         contradiction
--         unfold fin.val nat.pred
--         dsimp
--         rename_i a; exact a.valLt
--       }
--       {
--         cases idx with
--         | zero =>
--           cases pos <;> contradiction
--         | succ idx =>
--         unfold fin.val nat.pred
--         dsimp
--         conv in fin.mk idx.val _ => {
--           rw [fin.val_mk]
--         }
--         rw [Vector.remove_get_ge]
--         apply nat.le_of_lt_succ
--         exact idx_gt_pos
--     })
--   | Abort :
--       Subst pos subst_ty .Void subst body new_body ->
--       Subst pos subst_ty ty susbt (.Abort body ty) (.Abort new_body ty)
--   | Func :
--       ∀{ arg_ty ret_ty subst_ty: LamTy }
--       { body: Term (.cons arg_ty ctx) ret_ty }
--       { new_body: Term (.cons arg_ty ctx) ret_ty }
--       { subst: Term (ctx.remove pos) subst_ty },
--       Subst pos.succ subst_ty ret_ty (by
--         unfold Vector.remove
--         simp
--         exact subst
--         admit) body new_body ->
--       Subst pos subst_ty (.Func arg_ty ret_ty) subst (.Lam arg_ty ret_ty body) (.Lam arg_ty ret_ty new_body)


-- #print axioms Subst

inductive ReductionStep : Term ctx ty -> Term ctx ty -> Type where
| Abort : ∀(body body': Term ctx .Void) ty, ReductionStep body body' -> ReductionStep (.Abort body ty) (.Abort body' ty)
--| Abort : ∀(body body': Term ctx .Void) ty, ReductionStep body body' -> ReductionStep (.Abort body ty) (.Abort body' ty)
