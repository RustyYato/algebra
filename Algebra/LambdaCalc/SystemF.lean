inductive LamType where
| Void
| Var (ty_binders: Nat)
| Fn (arg ret: LamType)
| Forall (body: LamType)
deriving Repr

inductive Term where
| Var (term_binders: Nat)
| TermLam (arg_ty: LamType) (body: Term)
| TypeLam (body: Term)
| TermApp (f arg: Term)
| TypeApp (f: Term) (arg: LamType)
| Panic (body: Term) (ty: LamType)
deriving Repr

abbrev TypeCtx := Nat
abbrev TermCtx := List LamType

inductive LamType.IsWellFormed : TypeCtx -> LamType -> Prop where
| Void : IsWellFormed n .Void
| Var n m : m < n -> IsWellFormed n (.Var m)
| Fn n arg ret : IsWellFormed n arg -> IsWellFormed n ret -> IsWellFormed n (.Fn arg ret)
| Forall n body : IsWellFormed n.succ body -> IsWellFormed n (.Forall body)

inductive TermCtx.IsWellFormed : TypeCtx -> TermCtx -> Prop where
| nil tyctx : IsWellFormed tyctx .nil
| cons tyctx ty ctx : ty.IsWellFormed tyctx -> IsWellFormed tyctx ctx -> IsWellFormed tyctx (ty::ctx)

def LamType.weakenAtBy (ty: LamType) (n m: Nat) : LamType :=
  match ty with
  | .Void => .Void
  | .Var x =>
    .Var <|
    if x < n then
      x
    else
      x + n + m
  | .Fn arg ret => .Fn (arg.weakenAtBy n m) (ret.weakenAtBy n m)
  | .Forall body => .Forall (body.weakenAtBy n.succ m)

def LamType.weakenBy (ty: LamType) (n: Nat) : LamType :=
  ty.weakenAtBy 0 n

def LamType.substAt (ty subst: LamType) (n: Nat) : LamType :=
  match ty with
  | .Void => .Void
  | .Var x =>
    if x < n then
      .Var x
    else if x = n then
      subst.weakenBy n
    else
      .Var x.pred
  | .Fn arg ret => .Fn (arg.substAt subst n) (ret.substAt subst n)
  | .Forall body => .Forall (body.substAt subst n.succ)

def Term.weakenAtBy (term: Term) (type_n type_m term_n term_m: Nat) : Term :=
  match term with
  | .Var x =>
    if x < term_n then
      .Var x
    else
      .Var (x + term_n + term_m)
  | .TermApp arg ret => .TermApp (arg.weakenAtBy type_n type_m term_n term_m) (ret.weakenAtBy type_n type_m term_n term_m)
  | .TypeApp f arg => .TypeApp (f.weakenAtBy type_n type_m term_n term_m) (arg.weakenAtBy type_n type_m)
  | .TermLam arg_ty body => .TermLam (arg_ty.weakenAtBy type_n type_m) (body.weakenAtBy type_n type_m term_n.succ term_m)
  | .TypeLam body => .TypeLam (body.weakenAtBy type_n.succ type_m term_n term_m)
  | .Panic body ty => .Panic (body.weakenAtBy type_n type_m term_n term_m) (ty.weakenAtBy type_n type_m)

def Term.weakenBy (term: Term) (type_n term_n: Nat) : Term :=
  term.weakenAtBy 0 type_n 0 term_n

def Term.substAt (term subst: Term) (type_n term_n: Nat) : Term :=
    match term with
  | .Var x =>
    if x < term_n then
      .Var x
    else if x = term_n then
      subst.weakenBy type_n term_n
    else
      .Var x.pred
  | .TermApp arg ret => .TermApp (arg.substAt subst type_n term_n) (ret.substAt subst type_n term_n)
  | .TypeApp f arg => .TypeApp (f.substAt subst type_n term_n) arg
  | .TermLam arg_ty body => .TermLam arg_ty (body.substAt subst type_n term_n.succ)
  | .TypeLam body => .TypeLam (body.substAt subst type_n.succ term_n)
  | .Panic body ty => .Panic (body.substAt subst type_n term_n) ty

def LamType.subst (term subst: LamType) := term.substAt subst 0
def Term.subst (term subst: Term) := term.substAt subst 0 0

def TermCtx.weakenBy (ctx: TermCtx) (n: Nat) : TermCtx := ctx.map (·.weakenBy n)

inductive Term.IsWellTyped : TypeCtx -> TermCtx -> Term -> LamType -> Prop where
| Var tyctx ctx term_binders (h: term_binders < ctx.length) ty :
  ty = ctx[term_binders] ->
  IsWellTyped tyctx ctx (.Var term_binders) ty
| TermLam tyctx ctx arg_ty ret_ty body :
  arg_ty.IsWellFormed tyctx ->
  IsWellTyped tyctx (arg_ty::ctx) body ret_ty ->
  IsWellTyped tyctx ctx (.TermLam arg_ty body) (.Fn arg_ty ret_ty)
| TypeLam tyctx ctx ret_ty body :
  IsWellTyped tyctx.succ (ctx.weakenBy 1) body ret_ty ->
  IsWellTyped tyctx ctx (.TypeLam body) (.Forall ret_ty)
| TermApp tyctx ctx f arg :
  IsWellTyped tyctx ctx f (.Fn arg_ty ret_ty) ->
  IsWellTyped tyctx ctx arg arg_ty ->
  IsWellTyped tyctx ctx (.TermApp f arg) ret_ty
| TypeApp tyctx ctx f arg :
  IsWellTyped tyctx ctx f (.Forall ret_ty) ->
  arg.IsWellFormed tyctx ->
  ret_ty' = ret_ty.subst arg ->
  IsWellTyped tyctx ctx (.TypeApp f arg) ret_ty'
| Panic body ty :
  IsWellTyped tyctx ctx body .Void ->
  ty.IsWellFormed tyctx ->
  IsWellTyped tyctx ctx (.Panic body ty) ty

def TermCtx.IsWellFormed.get (ctx: TermCtx) :
  ctx.IsWellFormed tyctx ->
  ∀x (h: x < ctx.length),
  ctx[x].IsWellFormed tyctx := by
  intro ctxwf x h
  induction ctxwf generalizing x with
  | nil => contradiction
  | cons ty ctx tywf ctxwf ih =>
    cases x with
    | zero => assumption
    | succ x => apply ih

def LamType.IsWellFormed.weakenAtBy.add (ty: LamType) :
  (ty.weakenAtBy pos x).IsWellFormed tyctx ->
  (ty.weakenAtBy (pos + pos') (x + x')).IsWellFormed (tyctx + pos' + x') := by
  intro tywf
  induction ty generalizing tyctx pos x pos' x' with
  | Void => apply IsWellFormed.Void
  | Fn arg ret argih retih =>
    cases tywf
    apply IsWellFormed.Fn
    apply argih <;> assumption
    apply retih <;> assumption
  | Forall body ih =>
    cases tywf with | Forall _ _ h =>
    apply IsWellFormed.Forall
    repeat rw [←Nat.succ_add]
    apply ih
    assumption
  | Var n =>
    cases tywf with | Var _ _ h =>
    apply IsWellFormed.Var
    split at h
    rename_i n_lt_pos
    rw [if_pos, Nat.add_assoc]
    apply Nat.lt_add_right
    assumption
    apply Nat.lt_add_right
    assumption
    rename_i pos_le_n
    replace pos_le_n := Nat.le_of_not_lt pos_le_n
    split
    rw [Nat.add_assoc]
    apply Nat.lt_add_right
    rw [Nat.add_assoc] at h
    apply Nat.lt_of_add_right_lt
    assumption
    repeat rw [Nat.add_assoc]
    rw [Nat.add_left_comm pos']
    rw [←Nat.add_assoc n, ←Nat.add_assoc (n + _)]
    apply Nat.add_lt_add_right
    assumption

def LamType.IsWellFormed.weakenBy.succ (ty: LamType) :
  (ty.weakenBy x).IsWellFormed tyctx ->
  (ty.weakenBy x.succ).IsWellFormed tyctx.succ :=
    LamType.IsWellFormed.weakenAtBy.add (pos' := 0) (x' := 1) ty

def LamType.IsWellFormed.weakenAtBy.add' (ty: LamType) :
  ty.IsWellFormed tyctx ->
  (ty.weakenAtBy n m).IsWellFormed (tyctx + n + m) := by
  intro wf
  induction ty generalizing n m tyctx with
  | Void => apply IsWellFormed.Void
  | Fn arg ret argih retih =>
    cases wf
    apply IsWellFormed.Fn
    apply argih; assumption
    apply retih; assumption
  | Forall body ih =>
    apply IsWellFormed.Forall
    cases wf
    rw [←Nat.succ_add]

    apply ih
    assumption
  | Var x =>
    apply IsWellFormed.Var
    cases wf with | Var _ _ x_lt_tyctx =>
    split
    apply Nat.lt_add_right
    apply Nat.lt_add_right
    assumption
    rename_i n_le_x
    replace n_le_x := Nat.le_of_not_lt n_le_x
    apply Nat.add_lt_add_right
    apply Nat.add_lt_add_right
    assumption

def LamType.IsWellFormed.weakenBy.add (ty: LamType) :
  ty.IsWellFormed tyctx ->
  (ty.weakenBy n).IsWellFormed (tyctx + n) := by
  intro wf
  exact weakenAtBy.add' (n := 0) (m := n) _ wf

def LamType.IsWellFormed.subst {ty subst: LamType} :
  x ≤ tyctx ->
  ty.IsWellFormed tyctx.succ ->
  (subst.weakenBy x).IsWellFormed tyctx ->
  (ty.substAt subst x).IsWellFormed tyctx := by
  intro x_in_bounds tywf substwf
  induction ty generalizing tyctx x with
  | Void => apply IsWellFormed.Void
  | Var n =>
    cases tywf with | Var _ _ n_le_tyctx =>
    unfold substAt
    split <;> rename_i h
    apply IsWellFormed.Var
    apply Nat.lt_of_lt_of_le <;> assumption
    replace h := Nat.le_of_not_lt h
    rcases Nat.lt_or_eq_of_le h with x_lt_n | x_eq_n
    rw [if_neg (Nat.ne_of_gt x_lt_n)]
    apply IsWellFormed.Var
    cases n
    contradiction
    apply Nat.lt_of_succ_lt_succ
    assumption
    rw [if_pos x_eq_n.symm]
    assumption
  | Fn arg ret argih retih =>
    cases tywf with | Fn _ _ _ argwf retwf =>
    apply IsWellFormed.Fn
    apply argih <;> assumption
    apply retih <;> assumption
  | Forall body ih =>
    cases tywf with | Forall _ _ bodywf =>
    apply IsWellFormed.Forall
    apply ih
    apply Nat.succ_le_succ
    assumption
    assumption
    apply LamType.IsWellFormed.weakenBy.succ
    assumption

def TermCtx.IsWellFormed.weakenBy (ctx: TermCtx) :
  ctx.IsWellFormed tyctx ->
  (ctx.weakenBy n).IsWellFormed (tyctx + n) := by
  intro ctxwf
  induction ctxwf with
  | nil => apply IsWellFormed.nil
  | cons ty ctx tywf ctxwf ih =>
    apply IsWellFormed.cons
    dsimp
    apply LamType.IsWellFormed.weakenBy.add
    assumption
    assumption

def Term.IsWellTyped.TypeIsWellFormed (term: Term) :
  ctx.IsWellFormed tyctx ->
  term.IsWellTyped tyctx ctx ty ->
  ty.IsWellFormed tyctx := by
  intro ctxwf termwt
  induction termwt with
  | Var tyctx ctx x x_in_bounds ty =>
    subst ty
    apply ctxwf.get
  | TermLam tyctx ctx arg_ty ret_ty body arg_tywf bodywt ih =>
    apply LamType.IsWellFormed.Fn
    assumption
    apply ih
    apply ctxwf.cons
    assumption
  | TypeLam tyctx ctx ret_ty body body_wt ih  =>
    apply LamType.IsWellFormed.Forall
    apply ih
    apply ctxwf.weaken
  | TermApp => sorry
  | TypeApp => sorry
  | Panic => sorry
