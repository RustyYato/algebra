
structure TypeVar where
  get: Nat
structure TermVar where
  get: Nat

instance : DecidableEq TypeVar
| .mk a, .mk b =>
  if h:a = b then
    .isTrue (by rw [h])
  else
    .isFalse (by intro g; apply h; rw [TypeVar.mk.inj g])
instance : DecidableEq TermVar
| .mk a, .mk b =>
  if h:a = b then
    .isTrue (by rw [h])
  else
    .isFalse (by intro g; apply h; rw [TermVar.mk.inj g])

inductive LamType where
| Void
| Var (name: TypeVar)
| Fn (arg ret: LamType)
| Forall (name: TypeVar) (body: LamType)

inductive Term where
| Var (id: TermVar)
| TermLam (arg_name: TermVar) (arg_ty: LamType) (body: Term)
| TypeLam (arg_name: TypeVar) (body: Term)
| TermApp (f arg: Term)
| TypeApp (f: Term) (arg: LamType)
| Panic (body: Term) (ty: LamType)

-- which type variables are in scope
structure TypeCtx where
  type_vars: List TypeVar
  type_vars_unique: type_vars.Nodup

-- which term variables are in scope, and
-- which what types they have
structure TermCtx where
  items: List (TermVar × LamType)
  term_vars_unique: items.Pairwise (fun a b => a.1 ≠ b.1)

-- does there exist a forall with the given type variable
inductive LamType.MemTypeVar : TypeVar -> LamType -> Prop where
| Forall body : MemTypeVar var (.Forall var body)
| ForallBody v' body : MemTypeVar var body -> MemTypeVar var (.Forall v' body)
| FnArg arg ret : MemTypeVar var arg -> MemTypeVar var (.Fn arg ret)
| FnRet arg ret : MemTypeVar var ret -> MemTypeVar var (.Fn arg ret)

instance : Membership TypeVar LamType := ⟨flip LamType.MemTypeVar⟩

-- does there exist a term lambda with the given term variable
inductive Term.MemTermVar : TermVar -> Term -> Prop where
| TermLam arg_ty body : MemTermVar var (.TermLam var arg_ty body)
| TermLamBody v' arg_ty body : MemTermVar var body -> MemTermVar var (.TermLam v' arg_ty body)
| TypeLamBody v' body : MemTermVar var body -> MemTermVar var (.TypeLam v' body)
| TermAppFun f arg : MemTermVar var f -> MemTermVar var (TermApp f arg)
| TermAppArg f arg : MemTermVar var arg -> MemTermVar var (TermApp f arg)
| TypeAppFun f arg : MemTermVar var f -> MemTermVar var (TypeApp f arg)
| Panic body ty : MemTermVar var body -> MemTermVar var (.Panic body ty)

instance : Membership TermVar Term := ⟨flip Term.MemTermVar⟩

-- does there exist a type lambda with the given type variable
inductive Term.MemTypeVar : TypeVar -> Term -> Prop where
| TypeLam body : MemTypeVar var (.TypeLam var body)
| TermLamBody v' arg_ty body : MemTypeVar var body -> MemTypeVar var (.TermLam v' arg_ty body)
| TypeLamBody v' body : MemTypeVar var body -> MemTypeVar var (.TypeLam v' body)
| TermAppFun f arg : MemTypeVar var f -> MemTypeVar var (TermApp f arg)
| TermAppArg f arg : MemTypeVar var arg -> MemTypeVar var (TermApp f arg)
| TypeAppFun f arg : MemTypeVar var f -> MemTypeVar var (TypeApp f arg)
| TypeAppArg f arg : var ∈ arg -> MemTypeVar var (TypeApp f arg)
| Panic body ty : MemTypeVar var body -> MemTypeVar var (.Panic body ty)

instance : Membership TypeVar Term := ⟨flip Term.MemTypeVar⟩

instance : Membership TypeVar TypeCtx where
  mem ctx x := x ∈ ctx.type_vars
instance : Membership TermVar TermCtx where
  mem ctx x := ∃v, ⟨x, v⟩ ∈ ctx.items

instance decMemTypeVarLamType (v: TypeVar) : ∀(ctx: LamType), Decidable (v ∈ ctx)
| .Void => .isFalse (nomatch ·)
| .Var _ => .isFalse (nomatch ·)
| .Fn a b =>
  match decMemTypeVarLamType v a with
  | .isTrue h => .isTrue (.FnArg _ _ h)
  | .isFalse h =>
  match decMemTypeVarLamType v b with
  | .isTrue h => .isTrue (.FnRet _ _ h)
  | .isFalse h => .isFalse (by intro g; cases g <;> trivial)
| .Forall name body =>
  if h:name = v then
    .isTrue (by rw [h]; exact .Forall _)
  else
    match decMemTypeVarLamType v body with
    | .isTrue h => .isTrue (.ForallBody _ _ h)
    | .isFalse h => .isFalse (by intro h; cases h <;> trivial)

instance (v: TypeVar) (ctx: TypeCtx) : Decidable (v ∈ ctx) := inferInstanceAs (Decidable (v ∈ ctx.type_vars)
)
instance (x: TermVar) (ctx: TermCtx) : Decidable (x ∈ ctx) := by
  unfold Membership.mem instMembershipTermVarTermCtx
  match ctx with
  | .mk ctx h =>
  match h:ctx.find? (fun x' => x'.1 = x) with
  | .some pair =>
    apply Decidable.isTrue
    exists pair.2
    have ⟨pairfst_eq, as, bs, append_eq,_⟩ := List.find?_eq_some_iff_append.mp h
    rw [←decide_eq_true_iff.mp pairfst_eq]
    show pair ∈ _
    dsimp
    rw [append_eq]
    apply List.mem_append.mpr
    right; apply List.Mem.head
  | .none =>
    apply Decidable.isFalse
    dsimp
    intro ⟨v, in_ctx⟩
    exact List.find?_eq_none.mp h ⟨x, v⟩  in_ctx (decide_eq_true_iff.mpr rfl)

inductive OptionProof {α: Type _} : Option α -> Type _ where
| some (a: α) : opt = .some a -> OptionProof opt
| none : opt = .none -> OptionProof opt

def Option.attachProof : ∀(o: Option α), OptionProof o
| .some x => .some x rfl
| .none => .none rfl

def Option.attachProof.ofEq (o o': Option a) : OptionProof o -> o = o' -> OptionProof o'
| x, .refl _ => x

def Option.attachProof_some (o: Option a) : (o': OptionProof o) -> (h: o = .some x) -> o' = .some x h := by
  intro o' h
  cases h
  cases o'
  rename_i h
  cases h
  rfl
  contradiction

def Option.attachProof_none (o: Option a) : (o': OptionProof o) -> (h: o = .none) -> o' = .none h := by
  intro o' h
  cases h
  cases o'
  rename_i h
  contradiction
  rfl

def TermCtx.get {x: TermVar} (ctx: TermCtx) (h: x ∈ ctx) : LamType :=
  match (ctx.items.find? (fun t => t.1 = x)).attachProof with
  | .some h _ => h.2
  | .none g => by
    exfalso
    have ⟨ty,mem⟩ := h
    have := List.find?_eq_none.mp g _ mem
    apply this
    apply decide_eq_true
    rfl

def TermCtx.get_head (h: List.Pairwise (fun a b => a.fst ≠ b.fst) (p :: ctx)
) : (TermCtx.mk (p::ctx) h).get (⟨_, List.Mem.head _⟩  : p.1 ∈ (_: TermCtx)) = p.2 := by
  unfold get
  dsimp
  cases g:(List.find? (fun t => decide (t.fst = p.fst)) (p :: ctx)).attachProof
  dsimp
  rename_i h
  unfold List.find? at h
  rw [decide_eq_true_iff.mpr rfl] at h
  rw [Option.some.inj h]
  dsimp
  contradiction

def TermCtx.get_tail (nomem: List.Pairwise (fun a b => a.fst ≠ b.fst) (p :: ctx)
) : (TermCtx.mk (p::ctx) nomem).get (⟨_, List.Mem.tail _ mem⟩ : x ∈ (_: TermCtx)) = (TermCtx.mk ctx (by
  cases nomem
  rename_i nomem
  assumption)).get ⟨_, mem⟩ := by
  unfold get
  dsimp
  cases g:(List.find? (fun t => decide (t.fst = x)) (p :: ctx)).attachProof
  dsimp
  rename_i a h
  unfold List.find? at h
  rw [decide_eq_false_iff_not.mpr] at h
  dsimp at h
  rw [Option.attachProof_some _ (List.find? (fun t => decide (t.fst = x)) ctx).attachProof h]
  intro h'
  · subst h'
    cases nomem
    rename_i nomem
    have := nomem _ mem
    contradiction
  dsimp
  contradiction

def TypeCtx.push (ctx: TypeCtx) (var: TypeVar) (nomem: var ∉ ctx) : TypeCtx where
  type_vars := var::ctx.type_vars
  type_vars_unique := by
    apply List.Pairwise.cons
    intro y x h
    subst h
    contradiction
    exact ctx.type_vars_unique

def TypeCtx.mem_push {ctx: TypeCtx} {var: TypeVar} {nomem: var ∉ ctx} :
  x ∈ ctx.push var nomem ↔ x = var ∨ x ∈ ctx := List.mem_cons

def TypeCtx.map (ctx: TypeCtx) (f: TypeVar -> TypeVar) (finj: ∀{x y}, f x = f y -> x = y) : TypeCtx where
  type_vars := ctx.type_vars.map f
  type_vars_unique := by
    cases ctx with | mk vars vars_unique =>
    induction vars with
    | nil => apply List.Pairwise.nil
    | cons head tail ih =>
      cases vars_unique <;> rename_i t h
      apply List.Pairwise.cons
      intro a mem
      have ⟨v,vmem,fv_eq_a⟩ := List.mem_map.mp mem
      subst fv_eq_a
      clear mem
      intro feq
      cases finj feq
      have := h _ vmem
      contradiction
      apply ih
      assumption

def TypeCtx.mem_map {ctx: TypeCtx} {f: TypeVar -> TypeVar} {finj} :
  ∀{x}, x ∈ ctx.map f finj ↔ ∃v ∈ ctx, x = f v := by
  intro x
  cases ctx with | mk vars vars_unique =>
  induction vars with
  | nil =>
    apply Iff.intro
    intro h
    contradiction
    intro ⟨h,_,_⟩
    contradiction
  | cons v vs ih =>
    cases vars_unique with | cons h vars_unique =>
    apply Iff.intro
    intro h
    cases h
    exists v
    apply And.intro
    apply List.Mem.head
    rfl
    rename_i h
    have ⟨v',v'_mem,xeq⟩  := (ih vars_unique).mp h
    exists v'
    apply And.intro
    apply List.Mem.tail
    assumption
    assumption
    intro ⟨v,mem,p⟩
    subst p
    cases mem
    apply List.Mem.head
    apply List.Mem.tail
    apply (ih vars_unique).mpr
    exists v

def TypeCtx.map_push (ctx: TypeCtx) (f: TypeVar -> TypeVar) (finj: ∀{x y}, f x = f y -> x = y) (var: TypeVar) {hv} :
  (ctx.map f finj).push (f var) hv = (ctx.push var (by
    intro h
    apply hv
    apply mem_map.mpr
    exists var)).map f finj := by
    rfl

def TermCtx.push (ctx: TermCtx) (var: TermVar) (ty: LamType) (nomem: var ∉ ctx) : TermCtx where
  items := ⟨var, ty⟩::ctx.items
  term_vars_unique := by
    apply List.Pairwise.cons
    intro x h var_eq_x
    dsimp at var_eq_x
    subst var_eq_x
    apply nomem
    exists x.snd
    exact ctx.term_vars_unique

def TermCtx.mem_push {ctx: TermCtx} {var: TermVar} {ty:LamType} {nomem: var ∉ ctx} :
  x ∈ ctx.push var ty nomem ↔ x = var ∨ x ∈ ctx := by
  apply Iff.intro
  intro ⟨ty',mem⟩
  cases mem
  left; rfl
  right; exists ty'
  intro h
  cases h
  subst var; exists ty; apply List.Mem.head
  rename_i h
  obtain ⟨ty',mem⟩ := h
  exists ty'
  apply List.Mem.tail
  assumption

attribute [irreducible] TypeCtx.push TermCtx.push

-- are all type variables well scoped
inductive LamType.IsWellFormed : TypeCtx -> LamType -> Prop where
| Void : IsWellFormed ctx .Void
| Var var : var ∈ ctx -> IsWellFormed ctx (.Var var)
| Func arg ret : IsWellFormed ctx arg -> IsWellFormed ctx ret -> IsWellFormed ctx (.Fn arg ret)
| Forall var body (fresh_var: var ∉ ctx) :
  IsWellFormed (ctx.push var fresh_var) body -> IsWellFormed ctx (.Forall var body)

-- are all types in the term ctx well formed
inductive TermCtx.IsWellFormed (tyctx: TypeCtx) : TermCtx -> Prop where
| nil : IsWellFormed tyctx ⟨[], List.Pairwise.nil⟩
| cons termvar ty ctx hx hctx :
  ty.IsWellFormed tyctx ->
  IsWellFormed tyctx ⟨ctx,hctx⟩ ->
  IsWellFormed tyctx ⟨⟨termvar,ty⟩::ctx,List.Pairwise.cons hx hctx⟩

-- are all term and type vars are well scoped
inductive Term.IsWellFormed : TypeCtx -> TermCtx -> Term -> Prop where
| Var id : id ∈ ctx -> IsWellFormed tyctx ctx (.Var id)
| TermLam arg_name arg_ty body (nomem: arg_name ∉ ctx) :
  arg_ty.IsWellFormed tyctx ->
  IsWellFormed tyctx ((ctx: TermCtx).push arg_name arg_ty nomem) body ->
  IsWellFormed tyctx ctx (.TermLam arg_name arg_ty body)
| TypeLam arg_name body (nomem: arg_name ∉ tyctx) :
  IsWellFormed (tyctx.push arg_name nomem) ctx body ->
  IsWellFormed tyctx ctx (.TypeLam arg_name body)
| TermApp f arg :
  IsWellFormed tyctx ctx f ->
  IsWellFormed tyctx ctx arg ->
  IsWellFormed tyctx ctx (TermApp f arg)
| TypeApp f arg :
  IsWellFormed tyctx ctx f ->
  arg.IsWellFormed tyctx ->
  IsWellFormed tyctx ctx (TypeApp f arg)
| Panic body ty :
  ty.IsWellFormed tyctx ->
  IsWellFormed tyctx ctx body ->
  IsWellFormed tyctx ctx (.Panic body ty)

inductive Term.IsValue : Term -> Prop where
| TermLam (arg_name: TermVar) (arg_ty: LamType) (body: Term) : IsValue (.TermLam arg_name arg_ty body)
| TypeLam (arg_name: TypeVar) (body: Term) : IsValue (.TypeLam arg_name body)

def LamType.subst (var: TypeVar) (ty subst: LamType) : LamType :=
  match ty with
  | .Void => .Void
  | .Var name => if name = var then subst else .Var name
  | .Fn arg ret => .Fn (arg.subst var subst) (ret.subst var subst)
  | .Forall name body => .Forall name (body.subst var subst)

def Term.substTerm (var: TermVar) (term subst: Term) : Term :=
  match term with
  | .Var name => if name = var then subst else .Var name
  | .TermLam arg_name arg_ty body =>
    .TermLam arg_name arg_ty (body.substTerm var subst)
  | .TypeLam arg_name body =>
    .TypeLam arg_name (body.substTerm var subst)
  | .TermApp f arg =>
    .TermApp (f.substTerm var subst) (arg.substTerm var subst)
  | .TypeApp f arg =>
    .TypeApp (f.substTerm var subst) arg
  | .Panic body ty =>
    .Panic (body.substTerm var subst) ty

def Term.substType (var: TypeVar) (term: Term) (subst: LamType) : Term :=
  match term with
  | .Var name => .Var name
  | .TermLam arg_name arg_ty body =>
    .TermLam arg_name (arg_ty.subst var subst) (body.substType var subst)
  | .TypeLam arg_name body =>
    .TypeLam arg_name (body.substType var subst)
  | .TermApp f arg =>
    .TermApp (f.substType var subst) (arg.substType var subst)
  | .TypeApp f arg =>
    .TypeApp (f.substType var subst) (arg.subst var subst)
  | .Panic body ty =>
    .Panic (body.substType var subst) (ty.subst var subst)

inductive Term.IsWellTyped : TypeCtx -> TermCtx -> Term -> LamType -> Prop where
| Var id (mem: id ∈ ctx) :
  -- if the type is the same as the context
  ty = ctx.get mem ->
  IsWellTyped tyctx ctx (.Var id) ty
| TermLam arg_name arg_ty body (nomem: arg_name ∉ ctx) :
  arg_ty.IsWellFormed tyctx ->
  IsWellTyped tyctx ((ctx: TermCtx).push arg_name arg_ty nomem) body ret_ty ->
  IsWellTyped tyctx ctx (.TermLam arg_name arg_ty body) (.Fn arg_ty ret_ty)
| TypeLam arg_name body (nomem: arg_name ∉ tyctx) :
  IsWellTyped (tyctx.push arg_name nomem) ctx body ret_ty ->
  IsWellTyped tyctx ctx (.TypeLam arg_name body) (.Forall arg_name ret_ty)
| TermApp f arg :
  IsWellTyped tyctx ctx f (.Fn arg_ty ret_ty)  ->
  IsWellTyped tyctx ctx arg arg_ty ->
  IsWellTyped tyctx ctx (.TermApp f arg) ret_ty
| TypeApp f arg (nomem: arg_name ∉ tyctx) :
  ret_ty.IsWellFormed (tyctx.push arg_name nomem) ->
  arg.IsWellFormed tyctx ->
  IsWellTyped tyctx ctx f (.Forall arg_name ret_ty)  ->
  -- there are no common type variables introduced in arg and ret_ty
  (∀ (x : TypeVar), ¬(x ∈ arg ∧ x ∈ ret_ty)) ->
  ret_ty' = (ret_ty.subst arg_name arg) ->
  IsWellTyped tyctx ctx (.TypeApp f arg) ret_ty'
| Panic body ty :
  ty.IsWellFormed tyctx ->
  IsWellTyped tyctx ctx body .Void ->
  IsWellTyped tyctx ctx (.Panic body ty) ty

def LamType.IsWellFormed.ext {ctx₀ ctx₁: TypeCtx} :
  (∀x, x ∈ ctx₀ ↔ x ∈ ctx₁) ->
  IsWellFormed ctx₀ ty ->
  IsWellFormed ctx₁ ty := by
  intro h wf
  induction ty generalizing ctx₀ ctx₁ with
  | Void => exact IsWellFormed.Void
  | Var name =>
    apply IsWellFormed.Var
    apply (h _).mp
    cases wf
    assumption
  | Fn arg ret argih retih =>
    cases wf
    apply IsWellFormed.Func
    apply argih; assumption; assumption
    apply retih; assumption; assumption
  | Forall v body ih =>
    apply IsWellFormed.Forall
    cases wf; rename_i fresh wf
    apply ih _ wf
    intro wf mem
    cases wf
    have := (h _).mpr mem
    contradiction
    intro v
    apply Iff.intro
    intro mem
    cases TypeCtx.mem_push.mp mem <;> rename_i mem
    apply TypeCtx.mem_push.mpr
    left; assumption
    apply TypeCtx.mem_push.mpr
    right
    apply (h _).mp
    assumption
    intro mem
    cases TypeCtx.mem_push.mp mem <;> rename_i mem
    apply TypeCtx.mem_push.mpr
    left; assumption
    apply TypeCtx.mem_push.mpr
    right
    apply (h _).mpr
    assumption

def LamType.IsWellFormed.exchange {ctx: TypeCtx} {hty₀ hty₁} :
  IsWellFormed ((ctx.push ty₀ hty₀).push ty₁ hty₁) ty ->
  IsWellFormed ((ctx.push ty₁ (by
    intro h
    apply hty₁
    apply TypeCtx.mem_push.mpr
    right; assumption)).push ty₀ (by
    intro h
    cases TypeCtx.mem_push.mp h
    apply hty₁
    apply TypeCtx.mem_push.mpr
    left; symm; assumption
    apply hty₀
    assumption)) ty := by
  intro wf
  apply wf.ext
  intro x
  apply Iff.intro
  intro mem
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  left; assumption
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  left; assumption
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  right; assumption
  intro mem
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  left; assumption
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  left; assumption
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  right; assumption

def LamType.IsWellFormed.weaken :
  tyvar ∉ ty ->
  IsWellFormed ctx ty ->
  IsWellFormed (ctx.push tyvar hty') ty := by
  intro nomem h
  induction h generalizing tyvar with
  | Void => exact IsWellFormed.Void
  | Var =>
    apply IsWellFormed.Var
    apply TypeCtx.mem_push.mpr
    right; assumption
  | Func arg ret argwf retwf argih retih =>
    apply IsWellFormed.Func
    apply argih
    intro h
    apply nomem
    apply LamType.MemTypeVar.FnArg
    assumption
    apply retih
    intro h
    apply nomem
    apply LamType.MemTypeVar.FnRet
    assumption
  | Forall v body vfresh bodywf ih =>
    apply IsWellFormed.Forall
    apply exchange
    apply ih
    intro h
    apply nomem
    apply LamType.MemTypeVar.ForallBody
    assumption
    intro g
    replace g := TypeCtx.mem_push.mp g
    cases g <;> rename_i g
    subst v
    apply nomem
    apply LamType.MemTypeVar.Forall
    contradiction

def TermCtx.IsWellFormed.ext (ctx: TermCtx) {ctx₀ ctx₁: TypeCtx} :
  (∀x, x ∈ ctx₀ ↔ x ∈ ctx₁) ->
  ctx.IsWellFormed ctx₀ ->
  ctx.IsWellFormed ctx₁ := by
  intro h wf
  cases ctx with | mk items term_vars_unique =>
  induction items with
  | nil => apply IsWellFormed.nil
  | cons head tail ih =>
    cases term_vars_unique with | cons h t =>
    cases wf with | cons h₀ t₀ =>
    apply IsWellFormed.cons
    intro ⟨x,ty⟩ mem eq
    exact h _ mem eq
    apply LamType.IsWellFormed.ext
    assumption
    assumption
    apply ih
    assumption

def TermCtx.IsWellFormed.exchange {ctx: TermCtx} {tyctx: TypeCtx} {hty₀ hty₁} :
  ctx.IsWellFormed ((tyctx.push ty₀ hty₀).push ty₁ hty₁) ->
  ctx.IsWellFormed ((tyctx.push ty₁ (by
    intro h
    apply hty₁
    apply TypeCtx.mem_push.mpr
    right; assumption)).push ty₀ (by
    intro h
    cases TypeCtx.mem_push.mp h
    apply hty₁
    apply TypeCtx.mem_push.mpr
    left; symm; assumption
    apply hty₀
    assumption)) := by
  intro wf
  apply wf.ext
  intro x
  apply Iff.intro
  intro mem
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  left; assumption
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  left; assumption
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  right; assumption
  intro mem
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  left; assumption
  replace mem := TypeCtx.mem_push.mp mem
  cases mem <;> rename_i mem
  apply TypeCtx.mem_push.mpr
  left; assumption
  apply TypeCtx.mem_push.mpr
  right; apply TypeCtx.mem_push.mpr
  right; assumption

def TermCtx.containsTypeVar (ctx: TermCtx) (x: TypeVar) :=
  ∃v, ∃h: v ∈ ctx, x ∈ ctx.get h

def TermCtx.IsWellFormed.weaken {tyvar: TypeVar} {hty'} :
  ¬ctx.containsTypeVar tyvar ->
  IsWellFormed tyctx ctx ->
  IsWellFormed (tyctx.push tyvar hty') ctx := by
  intro nomem wf
  cases ctx with | mk items term_vars_unique =>
  induction items generalizing tyctx tyvar with
  | nil => apply IsWellFormed.nil
  | cons p ctx ih =>
    cases term_vars_unique with | cons h t =>
    cases wf with | cons h₀ t₀ =>
    apply IsWellFormed.cons
    intro ⟨x,ty⟩ mem eq
    exact h _ mem eq
    apply LamType.IsWellFormed.weaken
    intro mem
    apply nomem
    unfold containsTypeVar
    exists h₀
    refine ⟨?_,?_⟩
    exists t₀
    apply List.Mem.head
    rw [TermCtx.get_head]
    assumption
    assumption
    apply ih
    intro nomem'
    cases nomem' <;> rename_i v nomem'
    cases nomem' <;> rename_i hv nomem'
    apply nomem
    exists v
    refine ⟨?_,?_⟩
    cases hv <;> rename_i v₀ _
    exists v₀
    apply List.Mem.tail
    assumption
    obtain ⟨v₀,hv₀⟩ := hv
    rw [TermCtx.get_tail]
    assumption
    exact v₀
    assumption
    assumption

def LamType.subst.IsWellFormed
  (var: TypeVar) (ty subst: LamType) (nomem: var ∉ tyctx) :
  IsWellFormed (tyctx.push var nomem) ty ->
  IsWellFormed tyctx subst ->
  (no_common_vars: ∀x, ¬(x ∈ subst ∧ x ∈ ty)) ->
  IsWellFormed tyctx (ty.subst var subst) := by
  intro h g no_common_vars
  induction ty generalizing tyctx with
  | Void => apply LamType.IsWellFormed.Void
  | Var name =>
    unfold LamType.subst
    cases h
    rename_i mem
    replace mem := TypeCtx.mem_push.mp mem
    cases mem <;> rename_i mem
    rw [if_pos mem]
    assumption
    rw [if_neg]
    apply IsWellFormed.Var
    assumption
    intro h
    subst h
    contradiction
  | Fn arg ret argih retih =>
    cases h
    apply IsWellFormed.Func
    apply argih
    assumption
    assumption
    intro x h
    apply no_common_vars
    apply And.intro h.left
    apply LamType.MemTypeVar.FnArg
    exact h.right
    apply retih
    assumption
    assumption
    intro x h
    apply no_common_vars
    apply And.intro h.left
    apply LamType.MemTypeVar.FnRet
    exact h.right
  | Forall name body ih =>
    cases h
    rename_i fresh_var _
    apply IsWellFormed.Forall
    apply ih
    apply IsWellFormed.exchange
    assumption
    apply IsWellFormed.weaken
    intro h
    exact no_common_vars name ⟨h,LamType.MemTypeVar.Forall _⟩
    assumption
    intro x h
    apply no_common_vars
    apply And.intro h.left
    apply LamType.MemTypeVar.ForallBody
    exact h.right

def TermCtx.IsWellFormed.get {ctx: TermCtx} (mem: x ∈ ctx) :
  ctx.IsWellFormed tyctx ->
  (ctx.get mem).IsWellFormed tyctx := by
  intro wf
  cases mem with | intro v₀ mem =>
  cases ctx with | mk items term_vars_unique =>
  dsimp at mem
  induction mem with
  | head =>
    cases wf
    rw [TermCtx.get_head]
    assumption
  | tail _ _ ih =>
    cases wf
    rw [TermCtx.get_tail]
    apply ih
    assumption
    exact v₀
    assumption

def TermCtx.IsWellFormed.push {ctx: TermCtx} (h: x ∉ ctx) :
  ctx.IsWellFormed tyctx ->
  ty.IsWellFormed tyctx ->
  (ctx.push x ty h).IsWellFormed tyctx := by
  intro wfctx wfty
  unfold TermCtx.push
  apply IsWellFormed.cons
  any_goals assumption
  intro y mem g
  dsimp at g
  subst g
  cases ctx with | mk items term_vars_unique =>
  apply h <;> clear h
  dsimp at *
  cases mem
  exists y.snd
  apply List.Mem.head
  exists y.snd
  apply List.Mem.tail
  assumption

def Term.IsWellTyped.TypeIsWellFormed :
  ctx.IsWellFormed tyctx ->
  Term.IsWellTyped tyctx ctx term ty ->
  ty.IsWellFormed tyctx := by
  intro ctxwf h
  induction h with
  | Var name name_in_ctx tydef =>
    subst tydef
    apply ctxwf.get
  | TermLam _ _ _ _ _ _ ih =>
    apply LamType.IsWellFormed.Func
    assumption
    apply ih
    apply TermCtx.IsWellFormed.push
    repeat assumption
  | TypeLam _ _ _ _ ih =>
    apply LamType.IsWellFormed.Forall
    apply ih
    repeat assumption
    apply TermCtx.IsWellFormed.weaken
    ·
      sorry
    assumption
  | TermApp _ _ _ _ iharg ihret =>
    cases iharg ctxwf
    assumption
  | TypeApp _ _ _ _ _ _ _ retdef ih =>
    cases ih ctxwf
    subst retdef
    apply LamType.subst.IsWellFormed
    assumption
    assumption
    assumption
  | Panic _ _ _ _ _ => assumption
