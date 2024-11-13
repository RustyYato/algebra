import Algebra.AxiomBlame

inductive LamType where
| Unit
| Void
| Fn (arg ret: LamType)

inductive Term where
| ConstUnit
| Var (id: Nat)
| Lam (arg_ty: LamType) (body: Term)
| App (f arg: Term)
| Panic (body: Term) (ty: LamType)

-- under a given context `ctx`, does term `t` have type `ty`
inductive Term.IsWellTyped : (ctx: List LamType) -> (t: Term) -> (ty: LamType) -> Prop where
| ConstUnit : IsWellTyped ctx .ConstUnit .Unit
| Var (id: Nat) (ty: LamType) (h: id < ctx.length) : ty = ctx[id] -> IsWellTyped ctx (.Var id) ty
| Lam (body: Term) : IsWellTyped (arg_ty::ctx) body ret_ty -> IsWellTyped ctx (.Lam arg_ty body) (.Fn arg_ty ret_ty)
| App (f arg: Term) : IsWellTyped ctx f (.Fn arg_ty ret_ty) -> IsWellTyped ctx arg arg_ty -> IsWellTyped ctx (.App f arg) ret_ty
| Panic (body: Term) (ty: LamType) : IsWellTyped ctx body .Void -> IsWellTyped ctx (.Panic body ty) ty

-- every type can be uniquely specified in a given context
def Term.IsWellTyped.decide {ctx: List LamType} {t: Term} {a b: LamType} :
  IsWellTyped ctx t a ->
  IsWellTyped ctx t b ->
  a = b := by
  intro wta wtb
  induction wta generalizing b with
  | ConstUnit => cases wtb; rfl
  | Var => cases wtb; subst b; assumption
  | Lam body _ ih =>
    cases wtb
    congr
    rw [ih]
    assumption
  | App _ _ _ _ fih _ =>
    rename_i arg_ty _ _ _ _
    cases wtb
    rename_i wtf'
    have ⟨_,_⟩ := LamType.Fn.inj (fih wtf')
    trivial
  | Panic body ty _ _ =>
    cases wtb
    rfl

def Term.weakenAt (varid: Nat) : Term -> Term
| .ConstUnit => .ConstUnit
| .Lam arg_ty body => .Lam arg_ty (body.weakenAt varid.succ)
| .Panic body ty => .Panic (body.weakenAt varid) ty
| .App f arg => .App (f.weakenAt varid) (arg.weakenAt varid)
| .Var id => .Var <| if id < varid then id else id.succ

def Term.weaken : Term -> Term := weakenAt 0

def Term.weakenN (term: Term) : Nat -> Term
| 0 => term
| n + 1 => Term.weaken (Term.weakenN term n)

def Term.substAt (repl: Term) (varid: Nat) : Term -> Term
| .ConstUnit => .ConstUnit
| .Panic body ty => .Panic (Term.substAt repl varid body) ty
| .App f arg => .App (Term.substAt repl varid f) (Term.substAt repl varid arg)
| .Lam arg_ty body => .Lam arg_ty (Term.substAt repl.weaken varid.succ body)
| .Var id =>
  if id = varid then repl
  else if id < varid then .Var id
  else .Var id.pred

def Term.subst (term repl: Term) := Term.substAt repl 0 term

def List.insertAt (val: α) : Nat -> List α -> List α
| 0, xs => val::xs
| n + 1, xs =>
match xs with
| [] => [val]
| x::xs => x::xs.insertAt val n

def List.length_insertAt (val: α) (n: Nat) (xs: List α) : (xs.insertAt val n).length = xs.length.succ := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    unfold insertAt
    cases xs
    rfl
    dsimp
    rw [ih]

macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|rw [List.length_insertAt]; get_elem_tactic_trivial)

def List.getElem_insertAt_lt (val: α) (n m: Nat) (xs: List α) (h: m < xs.length) :
  m < n -> (xs.insertAt val n)[m] = xs[m] := by
  intro m_lt_n
  induction n generalizing xs m with
  | zero => contradiction
  | succ n ih =>
    unfold insertAt
    cases xs
    contradiction
    dsimp
    cases m
    rfl
    rw [List.getElem_cons_succ, ih]
    rfl
    apply Nat.lt_of_succ_lt_succ
    assumption

def List.getElem_insertAt_eq (val: α) (n: Nat) (xs: List α) (h: n ≤ xs.length) : (xs.insertAt val n)[n] = val := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    unfold insertAt
    cases xs
    contradiction
    dsimp
    rw [ih]
    apply Nat.le_of_succ_le_succ
    assumption

def List.getElem_insertAt_gt (val: α) (n m: Nat) (xs: List α) (h: m < xs.length) :
  m ≥ n -> (xs.insertAt val n)[m.succ] = xs[m] := by
  intro m_lt_n
  induction n generalizing xs m with
  | zero => rfl
  | succ n ih =>
    unfold insertAt
    cases xs
    contradiction
    dsimp
    cases m
    contradiction
    rw [List.getElem_cons_succ, ih]
    apply Nat.le_of_succ_le_succ
    assumption

def Term.weakenAt.spec (term: Term) (varid: Nat) (varid_bounds: varid ≤ ctx.length) :
  IsWellTyped ctx term ty ->
  IsWellTyped (ctx.insertAt ty' varid) (term.weakenAt varid) ty := by
  intro term_prf
  induction term_prf generalizing varid with
  | ConstUnit => exact IsWellTyped.ConstUnit
  | Lam body _ ih =>
    clear ctx
    rename_i ctx _ _
    apply IsWellTyped.Lam
    apply ih varid.succ
    apply Nat.succ_le_succ
    assumption
  | App _ _ _ _ fih argih =>
    apply IsWellTyped.App
    apply fih; assumption
    apply argih; assumption
  | Panic _ _ _ ih =>
    apply IsWellTyped.Panic
    apply ih; assumption
  | Var id h =>
    unfold weakenAt
    split
    apply IsWellTyped.Var
    rw [List.getElem_insertAt_lt]
    assumption
    assumption
    apply IsWellTyped.Var
    rw [List.getElem_insertAt_gt]
    assumption
    apply Nat.le_of_not_lt
    assumption

def Term.weaken.spec {ty'} (term: Term) : IsWellTyped ctx term ty -> IsWellTyped (ty'::ctx) term.weaken ty := weakenAt.spec term 0 (Nat.zero_le _)

def Term.weakenN.spec (term: Term) (n: Nat) :
  IsWellTyped (ctx.drop n) term ty ->
  n ≤ ctx.length ->
  IsWellTyped ctx (term.weakenN n) ty := by
  intro wt h
  induction n generalizing ctx term with
  | zero => assumption
  | succ n ih =>
    match ctx with
    | ty'::ctx =>
    apply weaken.spec
    apply ih
    assumption
    apply Nat.le_of_succ_le_succ
    assumption

def Term.substAt.spec (term repl: Term) (varid: Nat) (h: varid < ctx.length) : IsWellTyped ctx term ty -> IsWellTyped (ctx.eraseIdx varid) repl ctx[varid] -> IsWellTyped (ctx.eraseIdx varid) (Term.substAt repl varid term) ty := by
  intro term_prf repl_prf
  induction term_prf generalizing repl varid with
  | ConstUnit => apply IsWellTyped.ConstUnit
  | Lam body _ ih =>
    rename_i arg_ty ctx _
    apply IsWellTyped.Lam
    apply ih _ varid.succ
    apply weaken.spec
    assumption
    apply Nat.succ_lt_succ
    assumption
  | App _ _ _ _ fih argih  =>
    apply IsWellTyped.App
    apply fih; assumption
    apply argih; assumption
  | Panic _ _ _ ih =>
    apply IsWellTyped.Panic
    apply ih; assumption
  | Var id _ _ h₀ =>
    unfold substAt
    split
    subst varid
    subst h₀
    assumption
    rename_i id_ne_varid
    split <;> rename_i h₀
    apply IsWellTyped.Var
    conv => { rhs; arg 1; rw [List.eraseIdx_eq_take_drop_succ] }
    rw [List.getElem_append_left]
    rw [←List.getElem_take]
    any_goals assumption
    apply Nat.lt_of_lt_of_le h₀
    apply Nat.le_of_lt_succ
    rw [List.length_eraseIdx, Nat.sub_one, Nat.succ_pred]
    assumption
    apply Nat.not_eq_zero_of_lt
    any_goals assumption
    rename_i h₁
    subst h₁
    rename_i ctx' _
    have : varid + 1 + (id.pred - (List.take varid ctx').length) = id := by
      rw [List.length_take, Nat.min_eq_left (by
        apply Nat.le_of_lt
        assumption), ←Nat.add_sub_assoc (by
          apply  Nat.le_pred_of_lt
          apply Nat.lt_of_le_of_ne
          apply Nat.le_of_not_lt; assumption
          apply Ne.symm
          assumption), Nat.add_assoc, Nat.one_add, Nat.succ_pred (by
            intro h
            subst h
            cases Nat.le_zero.mp (Nat.le_of_not_lt h₀)
            contradiction), Nat.add_comm, Nat.add_sub_cancel]
    apply IsWellTyped.Var
    conv => { rhs; arg 1; rw [List.eraseIdx_eq_take_drop_succ] }
    rw [List.getElem_append_right', ←List.getElem_drop]
    conv => {
      rhs; arg 2
      rw [this]
    }
    rw[ this]
    assumption
    rw [List.length_take]
    apply Nat.le_pred_of_lt
    apply Nat.lt_of_le_of_lt
    apply Nat.min_le_left
    apply Nat.lt_of_le_of_ne
    apply Nat.le_of_not_lt; assumption
    apply Ne.symm
    assumption
    rw [List.length_eraseIdx, Nat.sub_one]
    apply Nat.pred_lt_pred
    intro h
    subst h
    cases Nat.le_zero.mp (Nat.le_of_not_lt h₀)
    contradiction
    assumption
    assumption

def Term.subst.spec (term repl: Term) : IsWellTyped (ty'::ctx) term ty -> IsWellTyped ctx repl ty' -> IsWellTyped ctx (Term.subst term repl) ty :=  Term.substAt.spec (ctx := ty'::ctx) term repl 0 (Nat.zero_lt_succ _)

-- inductive Term.IsIrreducible : Term -> Prop where
-- | ConstUnit : IsIrreducible .ConstUnit
-- | Var id : IsIrreducible (.Var id)
-- | Lam arg_ty body : IsIrreducible body -> IsIrreducible (.Lam arg_ty body)
-- | App f arg : IsIrreducible f -> IsIrreducible arg -> ¬f.IsLam -> IsIrreducible (.App f arg)
-- | Panic body : IsIrreducible body -> IsIrreducible (.Panic body ty)

inductive Term.IsNormalForm : Term -> Prop where
| ConstUnit : IsNormalForm .ConstUnit
| Lam arg_ty body : IsNormalForm (.Lam arg_ty body)

inductive Term.Reduce : List LamType -> LamType -> Term -> Term -> Prop where
| Apply next :
  IsWellTyped ctx (.App (.Lam arg_ty body) arg) ty ->
  arg.IsNormalForm ->
  next = body.subst arg ->
  Reduce ctx ty (.App (.Lam arg_ty body) arg) next
| AppFunc :
  Reduce ctx (.Fn arg_ty ret_ty) f f' ->
  IsWellTyped ctx arg arg_ty ->
  Reduce ctx ret_ty (.App f arg) (.App f' arg)
| AppArg :
  f.IsNormalForm ->
  IsWellTyped ctx f (.Fn arg_ty ret_ty) ->
  Reduce ctx arg_ty arg arg' ->
  Reduce ctx ret_ty (.App f arg) (.App f arg')
| Panic (ty: LamType) :
  Reduce ctx .Void body body' ->
  Reduce ctx ty (.Panic body ty) (.Panic body' ty)

inductive Term.Chain : List LamType -> LamType -> Term -> Term -> Prop where
| nil : IsWellTyped ctx a ty -> Chain ctx ty a a
| cons : Reduce ctx ty a b -> Chain ctx ty b c -> Chain ctx ty a c

instance Term.decIsNormalForm : ∀a, Decidable (IsNormalForm a)
| .Lam arg_ty body =>.isTrue (.Lam arg_ty body)
| .ConstUnit => .isTrue .ConstUnit
| .Panic _ _ | .App _ _ | .Var _ => .isFalse (nomatch ·)

def Term.progress {ty: LamType} (wt: a.IsWellTyped [] ty) : ¬a.IsNormalForm ↔ ∃b, Reduce [] ty a b := by
  induction a generalizing ty with
  | ConstUnit =>
    apply Iff.intro
    intro h
    have := h .ConstUnit
    contradiction
    intro ⟨_,red⟩
    nomatch red
  | Var n =>
    cases wt
    contradiction
  | Lam _ =>
    apply Iff.intro
    intro h
    have := h (.Lam _ _)
    contradiction
    intro ⟨_,red⟩
    nomatch red
  | Panic body ty ih =>
    cases wt; rename_i wt
    replace ih := ih wt
    have body_not_norm : ¬body.IsNormalForm := by
      intro norm
      cases norm <;> nomatch wt
    have ⟨body',body_red⟩ := ih.mp body_not_norm
    apply Iff.intro
    intro
    refine ⟨body'.Panic ?_,?_⟩
    assumption
    apply Reduce.Panic
    assumption
    intro ⟨_,_⟩
    intro h
    nomatch h
  | App f arg fih argih =>
    apply flip Iff.intro
    intro _ norm
    nomatch norm
    intro h
    clear h
    cases wt
    rename_i arg_ty argwt fwt
    if h₀:f.IsNormalForm then
      if h₁:arg.IsNormalForm then
        cases h₀
        nomatch fwt
        cases fwt
        rename_i body bodywt
        apply Exists.intro _ (Reduce.Apply _ _ _ _)
        any_goals rfl
        apply IsWellTyped.App
        apply IsWellTyped.Lam
        repeat assumption
      else
      have ⟨arg',red⟩ := (argih argwt).mp h₁
      exists f.App arg'
      apply Reduce.AppArg
      repeat assumption
    else
      have ⟨f',red⟩ := (fih fwt).mp h₀
      exists f'.App arg
      apply Reduce.AppFunc
      repeat assumption

def Term.Reduce.well_typed_left : Reduce ctx ty a b -> IsWellTyped ctx a ty := by
  intro red
  induction red with
  | Apply => assumption
  | AppFunc =>
    apply IsWellTyped.App
    assumption
    assumption
  | AppArg =>
    apply IsWellTyped.App
    assumption
    assumption
  | Panic =>
    apply IsWellTyped.Panic
    assumption

def Term.Reduce.well_typed_right : Reduce ctx ty a b -> IsWellTyped ctx b ty := by
  intro red
  induction red with
  | Apply next wt =>
    subst next
    cases wt
    rename_i wt
    cases wt
    apply subst.spec
    assumption
    assumption
  | AppFunc =>
    apply IsWellTyped.App
    assumption
    assumption
  | AppArg =>
    apply IsWellTyped.App
    assumption
    assumption
  | Panic =>
    apply IsWellTyped.Panic
    assumption

def Term.Chain.well_typed_left : Chain ctx ty a b -> IsWellTyped ctx a ty := by
  intro red
  cases red with
  | nil => assumption
  | cons a => exact a.well_typed_left

def Term.Chain.well_typed_right : Chain ctx ty a b -> IsWellTyped ctx b ty := by
  intro red
  induction red <;> assumption

def Term.Reduce.isNotNormal : Reduce ctx ty a b -> ¬a.IsNormalForm := by
  intro red norm
  cases norm <;> nomatch red

def Term.Reduce.decide : Reduce ctx ty a b -> Reduce ctx ty a c -> b = c := by
  intro ab ac
  induction ab generalizing c with
  | Apply _ _ body_val arg_val=>
    cases ac with
    | Apply => subst c; assumption
    | AppFunc red =>
      have := red.isNotNormal
      contradiction
    | AppArg _ _ red =>
      have := red.isNotNormal
      contradiction
  | AppFunc fred _ ih =>
    cases ac with
    | Apply _ _ body_val =>
      have := fred.isNotNormal
      contradiction
    | AppFunc red =>
      rw [ih]
      rename_i arg₀ _ _ arg₁
      cases arg₀.decide arg₁
      assumption
    | AppArg f_val =>
      have := fred.isNotNormal f_val
      contradiction
  | AppArg f_val _ arg_red ih =>
    cases ac with
    | Apply _ _ _ arg_val =>
      have := arg_red.isNotNormal
      contradiction
    | AppFunc red =>
      have := red.isNotNormal f_val
      contradiction
    | AppArg f_val =>
      rw [ih]
      rename_i h₀ _ _ h₁ _
      cases h₀.decide h₁
      assumption
  | Panic _ _ ih =>
    cases ac
    rw [ih]
    assumption

def Term.Reduce.allHEq (r₀: Term.Reduce ctx ty a b) (r₁: Term.Reduce ctx ty' a c): HEq r₀ r₁ := by
  cases r₀.well_typed_left.decide r₁.well_typed_left
  cases r₀.decide r₁
  rfl

inductive Term.Halts (ctx: List LamType) (t: Term) (ty: LamType) : Prop where
| intro (val: Term) (h: val.IsNormalForm) :
  -- reduce to a value
  Chain ctx ty t val -> Halts ctx t ty

def Term.Halts.IsWellTyped : Term.Halts ctx t ty -> t.IsWellTyped ctx ty := by
  intro ⟨val,_,chain⟩
  exact chain.well_typed_left

def Term.Halts.push : Reduce ctx ty t t' -> Term.Halts ctx t' ty -> Term.Halts ctx t ty := by
  intro red ⟨val,val_spec,chain⟩
  refine ⟨val,val_spec,?_⟩
  apply Chain.cons
  assumption
  assumption

def Term.Halts.pop : Reduce ctx ty t t' -> Term.Halts ctx t ty -> Term.Halts ctx t' ty := by
  intro red ⟨val,val_spec,chain⟩
  refine ⟨val,val_spec,?_⟩
  cases chain with
  | nil =>
    have := red.isNotNormal
    contradiction
  | cons r c =>
    cases r.decide red
    assumption

def Term.HeredHalts (ctx: List LamType) (t: Term) (ty: LamType) : Prop :=
  match ty with
  | .Void => False
  | .Unit => t.Halts ctx ty
  | .Fn arg_ty ret_ty =>
    t.Halts ctx ty ∧
    ∀(arg: Term), arg.HeredHalts ctx arg_ty -> (t.App arg).HeredHalts ctx ret_ty

def Term.HeredHalts.Halts : Term.HeredHalts ctx t ty -> t.Halts ctx ty := by
  intro halts
  cases ty with
  | Void => contradiction
  | Unit => exact halts
  | Fn arg_ty ret_ty => exact halts.left

def Term.HeredHalts.IsWellTyped : Term.HeredHalts ctx t ty -> t.IsWellTyped ctx ty := fun h => h.Halts.IsWellTyped

def Term.HeredHalts.iff_red (e e': Term) : Reduce ctx ty e e' -> (e.HeredHalts ctx ty ↔ e'.HeredHalts ctx ty) := by
  intro red
  induction ty generalizing e e' with
  | Void => apply Iff.intro <;> (intro h; contradiction)
  | Unit =>
    apply Iff.intro
    intro h
    apply Term.Halts.pop <;> assumption
    intro h
    apply Term.Halts.push <;> assumption
  | Fn arg_ty ret_ty _ ret_ih =>
    apply Iff.intro
    case mp =>
      intro ⟨h,pres⟩
      apply And.intro
      exact h.pop red
      intro arg arg_halts
      apply (ret_ih _ _ _).mp
      apply pres
      assumption
      apply Reduce.AppFunc
      assumption
      exact arg_halts.IsWellTyped
    case mpr =>
      intro ⟨h,pres⟩
      apply And.intro
      exact h.push red
      intro arg arg_halts
      apply (ret_ih _ _ _).mpr
      apply pres
      assumption
      apply Reduce.AppFunc
      assumption
      exact arg_halts.IsWellTyped

def Term.HeredHalts.iff_chain (e e': Term) : Chain ctx ty e e' -> (e.HeredHalts ctx ty ↔ e'.HeredHalts ctx ty) := by
  intro chain
  induction chain with
  | nil => exact Iff.refl _
  | cons red _ ih =>
    apply Iff.trans _ ih
    apply iff_red
    assumption

inductive IsValidBindingList : List LamType -> List Term -> Prop where
| nil : IsValidBindingList ctx []
| cons :
  t.IsNormalForm ->
  t.HeredHalts [] ty ->
  IsValidBindingList ctx ts ->
  IsValidBindingList (ty::ctx) (t::ts)

def Term.substAllAt (term: Term) (n: Nat) (ctx_len: Nat) : List Term -> Term
| [] => term
| t::ts =>
  match ctx_len with
  | 0 => term
  | ctx_len + 1 => (Term.substAt (t.weakenN ctx_len) n term).substAllAt n ctx_len ts

def Term.substAll (term: Term) (ctx_len: Nat) : List Term -> Term := Term.substAllAt term 0 ctx_len

def Term.substAll.spec (ctx: List LamType) (term: Term) (ty: LamType) :
  term.IsWellTyped ctx ty ->
  ∀bindings,
  IsValidBindingList ctx bindings ->
  bindings.length ≤ ctx.length ->
  (term.substAll ctx.length bindings).IsWellTyped (ctx.drop bindings.length) ty := by
  intro term_wt bindings bind_spec bindings_le_ctx
  induction bind_spec generalizing term ty with
  | nil =>
    unfold substAll substAllAt
    assumption
  | cons _ halts _ ih =>
    unfold Term.substAll
    dsimp
    apply ih
    apply subst.spec
    assumption
    apply weakenN.spec
    rw [List.drop_length]
    exact halts.IsWellTyped
    apply Nat.le_refl
    apply Nat.le_of_succ_le_succ
    assumption

def Term.substAll.spec' (ctx: List LamType) (term: Term) (ty: LamType) :
  term.IsWellTyped ctx ty ->
  ∀bindings, ctx.length = bindings.length -> IsValidBindingList ctx bindings -> (term.substAll ctx.length bindings).IsWellTyped [] ty := by
  intro wt bindings spec h
  have := substAll.spec ctx term ty wt bindings h (Nat.le_of_eq spec.symm)
  rw [←spec, List.drop_length] at this
  assumption

def Term.substAll.ConstUnit:
  Term.ConstUnit.substAll n bindings = Term.ConstUnit := by
  induction bindings generalizing n <;> cases n <;> try trivial
  unfold substAll substAllAt
  dsimp
  rename_i ih _
  apply ih

def Term.weakenAt_substAt (t: Term) (binding: Term) (n: Nat) :
  Term.substAt binding n (t.weakenAt n) = t := by
  induction t generalizing n binding with
  | ConstUnit => rfl
  | Lam arg_ty body ih =>
    unfold weakenAt substAt
    rw [ih]
  | Panic body ty ih =>
    unfold weakenAt substAt
    rw [ih]
  | App f arg fih argih =>
    unfold substAt weakenAt
    dsimp
    rw [fih, argih]
  | Var id =>
    unfold substAt weakenAt
    dsimp
    split <;> rename_i h
    rw [if_neg]
    intro g
    exact Nat.lt_irrefl _ (g ▸ h)
    split <;> rename_i g
    subst n
    have := h (Nat.lt_succ_self _)
    contradiction
    rw [if_neg]
    rfl
    intro g
    apply h
    apply Nat.lt_trans _ g
    apply Nat.lt_succ_self

def Term.weaken_subst (t: Term) (binding: Term) :
  (t.weaken).subst binding = t := by apply weakenAt_substAt

def Term.weakenN_substAll (t: Term) (bindings: List Term) :
  (t.weakenN bindings.length).substAll bindings.length bindings = t := by
  induction bindings with
  | nil => rfl
  | cons b bindings =>
    unfold weakenN substAll substAllAt
    dsimp
    rw [←subst, weaken_subst]
    assumption

def Term.weaken_weakenN :
  weaken (weakenN term n) = weakenN (weaken term) n := by
  induction n generalizing term with
  | zero => rfl
  | succ n ih =>
    unfold weakenN
    rw [ih]

def Term.substAll.Lam (body : Term) (bindings: List Term) :
  (body.Lam arg_ty).substAll ctx_len bindings = (body.substAllAt 1 ctx_len (bindings.map Term.weaken)).Lam arg_ty := by
  induction bindings generalizing body ctx_len with
  | nil =>
    unfold substAll substAllAt
    rfl
  | cons b bindings ih =>
    cases ctx_len <;> unfold substAll substAllAt
    rfl
    rename_i ctx_len
    dsimp
    conv => {
      lhs
      unfold substAt
    }
    rw [←ih]
    congr
    rw [weaken_weakenN]

def Term.substAll.App (f arg : Term) (bindings: List Term) :
  (f.App arg).substAll ctx_len bindings = (f.substAll ctx_len bindings).App (arg.substAll ctx_len bindings) := by
  induction bindings generalizing f arg ctx_len with
  | nil =>
    unfold substAll substAllAt
    rfl
  | cons b bindings ih =>
    cases ctx_len
    rfl
    rename_i ctx_len
    unfold substAll substAllAt
    dsimp
    repeat rw [←subst]
    repeat rw [←substAll]
    rw [←ih]
    congr

def Term.Chain.append : Term.Chain ctx ty a b -> Term.Chain ctx ty b c -> Term.Chain ctx ty a c := by
  intro ab bc
  induction ab with
  | nil => assumption
  | cons a _ ih =>
    apply Chain.cons
    assumption
    apply ih
    assumption

def Term.Chain.AppArg  :
  IsWellTyped ctx f (LamType.Fn arg_ty ret_ty) ->
  f.IsNormalForm ->
  Chain ctx arg_ty arg arg' ->
  Chain ctx ret_ty (Term.App f arg) (Term.App f arg') := by
  intro wt fnorm chain
  induction chain with
  | nil =>
    apply Chain.nil
    apply IsWellTyped.App
    assumption
    assumption
  | cons c _ ih =>
    replace ih := ih wt
    apply Chain.cons
    apply Reduce.AppArg
    repeat assumption

def Term.substAt_subst' (n: Nat) (v body: Term) {arg_val: Term} :
  Term.substAt (arg_val.weakenN n) n (Term.substAt (v.weakenN n.succ) n.succ body) =
  Term.substAt (v.weakenN n) n (Term.substAt (arg_val.weakenN n.succ) n body) := by
  induction body generalizing v arg_val n with
  | ConstUnit => rfl
  | Panic body ty ih =>
    repeat rw [substAt]
    rw [ih]
  | App f arg fih argih =>
    repeat rw [substAt]
    rw [fih, argih]
  | Lam arg_ty body ih =>
    repeat rw [substAt]
    repeat rw [←weakenN]
    rw [ih]
  | Var id =>
    repeat rw [substAt]
    split <;> rename_i h
    subst id
    rw [if_neg (Nat.succ_ne_self _), if_neg (Nat.not_lt_of_le (Nat.le_succ _))]
    dsimp
    sorry
    split
    split; subst id
    sorry
    rw [if_pos]
    sorry
    apply Nat.lt_of_le_of_ne
    apply Nat.le_of_lt_succ
    assumption
    assumption
    rw [if_neg, if_neg]
    sorry
    intro h
    have := Nat.lt_trans h (Nat.lt_succ_self _)
    contradiction
    intro h
    subst h
    have := Nat.lt_succ_self id
    contradiction

def Term.substAt_subst (v body: Term) :
  Term.substAt arg_val 0 (Term.substAt v.weaken 1 body) =
  Term.substAt v 0 (Term.substAt arg_val.weaken 0 body) := substAt_subst' 0 v body

def Term.substAllAt_subst {ctx: List LamType} (body: Term) :
  ctx.length = bindings.length ->
  (body.substAllAt 1 ctx.length (List.map weaken bindings)).subst arg_val =
   body.substAll (ty' :: ctx).length (arg_val :: bindings) := by
  intro h
  rw [List.length_cons, h]
  clear ty'
  clear h ctx
  induction bindings generalizing body arg_val with
  | nil =>
  unfold substAll substAllAt
  dsimp
  rfl
  | cons b bindings ih =>
  unfold substAll substAllAt
  dsimp
  rw [←weaken_weakenN, ←weakenN, ←substAll]
  rw [←subst, ih]
  unfold substAll substAllAt
  dsimp
  rw [weakenN, substAt_subst]
  rfl

def Term.allHeredHalts
  (ctx: List LamType)
  (term: Term)
  (ty: LamType)
  (bindings: List Term):
  term.IsWellTyped ctx ty ->
  IsValidBindingList ctx bindings ->
  ctx.length = bindings.length ->
  (term.substAll ctx.length bindings).HeredHalts [] ty := by
  intro wt valid_bindings complete_bindings

  induction wt generalizing bindings with
  | Panic _ _ _ ih  =>
    have : False := ih bindings valid_bindings complete_bindings
    contradiction
  | ConstUnit =>
    apply Halts.intro
    exact .ConstUnit
    rw [Term.substAll.ConstUnit]
    apply Chain.nil
    exact .ConstUnit
  | App f arg _ _ fih argih =>
    rw [substAll.App]
    apply (fih _ valid_bindings complete_bindings).right
    apply argih
    repeat assumption
  | Var id ty id_in_bounds ty_spec =>
    subst ty_spec
    clear ctx
    rename_i ctx
    clear term ty
    induction id generalizing ctx bindings with
    | zero =>
      match ctx with
      | ty'::ctx =>
      match bindings with
      | v::bindings =>
      cases valid_bindings with
      | cons v_val v_halts bindings =>
      unfold substAll substAllAt substAt
      dsimp
      rw [Nat.succ.inj complete_bindings, ←substAll, weakenN_substAll]
      assumption
    | succ id ih =>
      match ctx with
      | ty'::ctx =>
      match bindings with
      | v::bindings =>
      unfold substAll
      apply ih
      cases valid_bindings
      assumption
      apply Nat.succ.inj
      assumption
  | Lam body body_wt ih =>
    apply And.intro
    · rename_i arg_ty _ _
      apply Halts.intro (Term.Lam _ _)
      rename_i ctx _
      apply IsNormalForm.Lam arg_ty (body.substAllAt 1 ctx.length (bindings.map .weaken))
      rw [substAll.Lam]
      apply Chain.nil
      rw [←substAll.Lam]
      apply substAll.spec'
      apply IsWellTyped.Lam
      assumption
      assumption
      assumption
    · intro arg arg_halts
      have ⟨arg_val, arg_val_is_norm,arg_red⟩  := arg_halts.Halts
      apply (HeredHalts.iff_chain _ _ _).mpr
      apply ih
      apply IsValidBindingList.cons
      exact arg_val_is_norm
      apply (HeredHalts.iff_chain _ _ _).mp
      exact arg_halts
      assumption
      assumption
      unfold List.length
      congr
      apply Chain.append
      apply Chain.AppArg
      apply substAll.spec'
      apply IsWellTyped.Lam
      repeat assumption
      rw [substAll.Lam]
      apply IsNormalForm.Lam
      assumption
      apply Chain.cons
      rw [substAll.Lam]
      apply Reduce.Apply
      rw [←substAll.Lam]
      apply IsWellTyped.App
      apply substAll.spec'
      apply IsWellTyped.Lam
      repeat assumption
      exact arg_red.well_typed_right
      assumption
      rfl
      rw [substAllAt_subst]
      apply Chain.nil
      apply substAll.spec'
      assumption
      unfold List.length
      congr
      apply IsValidBindingList.cons
      assumption
      apply (HeredHalts.iff_chain _ _ _).mp
      assumption
      assumption
      assumption
      assumption

#axiom_blame Term.allHeredHalts
