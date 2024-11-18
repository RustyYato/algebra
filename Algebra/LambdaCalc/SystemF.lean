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
    if x < n then
      .Var x
    else
      .Var (x + n + m)
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

inductive Term.IsWellTyped : TypeCtx -> TermCtx -> Term -> LamType -> Prop where
| Var tyctx ctx term_binders (h: term_binders < ctx.length) ty :
  ty = ctx[term_binders] ->
  IsWellTyped tyctx ctx (.Var term_binders) ty
| TermLam tyctx ctx arg_ty ret_ty body :
  IsWellTyped tyctx (arg_ty::ctx) body ret_ty ->
  IsWellTyped tyctx ctx (.TermLam arg_ty body) (.Fn arg_ty ret_ty)
| TypeLam tyctx ctx ret_ty body :
  IsWellTyped tyctx.succ ctx body ret_ty ->
  IsWellTyped tyctx ctx (.TermLam arg_ty body) (.Forall ret_ty)
| TermApp tyctx ctx f arg :
  IsWellTyped tyctx ctx f (.Fn arg_ty ret_ty) ->
  IsWellTyped tyctx ctx arg arg_ty ->
  IsWellTyped tyctx ctx (.TermApp f arg) ret_ty
| TypeApp tyctx ctx f arg :
  IsWellTyped tyctx ctx f (.Forall ret_ty) ->
  arg.IsWellFormed tyctx ->
  ret_ty' = ret_ty.substAt arg 0 ->
  IsWellTyped tyctx ctx (.TypeApp f arg) ret_ty'
| Panic body ty :
  IsWellTyped tyctx ctx body .Void ->
  ty.IsWellFormed tyctx ->
  IsWellTyped tyctx ctx (.Panic body ty) ty
