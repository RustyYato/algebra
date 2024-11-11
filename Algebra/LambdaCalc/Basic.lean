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

def Term.weaken.spec (term: Term) : IsWellTyped ctx term ty -> IsWellTyped (ty'::ctx) term.weaken ty := weakenAt.spec term 0 (Nat.zero_le _)

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

inductive Term.IsLam : Term -> Prop where
| Lam arg_ty body : IsLam (.Lam arg_ty body)

inductive Term.IsValue : Term -> Prop where
| ConstUnit : IsValue .ConstUnit
| Var id : IsValue (.Var id)
| Lam arg_ty body : IsValue body -> IsValue (.Lam arg_ty body)
| App f arg : IsValue f -> IsValue arg -> ¬f.IsLam -> IsValue (.App f arg)
| Panic body : IsValue body -> IsValue (.Panic body ty)

inductive Term.Reduce : List LamType -> LamType -> Term -> Term -> Prop where
| Apply next :
  IsWellTyped ctx (.App (.Lam arg_ty body) arg) ty ->
  body.IsValue -> arg.IsValue ->
  next = body.subst arg ->
  Reduce ctx ty (.App (.Lam arg_ty body) arg) next
| LamBody :
  Reduce (arg_ty::ctx) ret_ty body body' ->
  Reduce ctx (.Fn arg_ty ret_ty) (.Lam arg_ty body) (.Lam arg_ty body')
| AppFunc :
  Reduce ctx (.Fn arg_ty ret_ty) f f' ->
  IsWellTyped ctx arg arg_ty ->
  Reduce ctx ret_ty (.App f arg) (.App f' arg)
| AppArg :
  f.IsValue ->
  IsWellTyped ctx f (.Fn arg_ty ret_ty) ->
  Reduce ctx arg_ty arg arg' ->
  Reduce ctx ret_ty (.App f arg) (.App f arg')
| Panic (ty: LamType) :
  Reduce ctx .Void body body' ->
  Reduce ctx ty (.Panic body ty) (.Panic body' ty)

inductive Term.Chain : List LamType -> LamType -> Term -> Term -> Prop where
| nil : IsWellTyped ctx a ty -> Chain ctx ty a a
| cons : Reduce ctx ty a b -> Chain ctx ty b c -> Chain ctx ty a c

variable {ctx: List LamType} {ty: LamType}

def Term.Reduce.IsNotValue : Reduce ctx ty a b -> ¬a.IsValue := by
  intro h v
  induction h <;> cases v
  rename_i h _
  exact h (.Lam _ _)
  any_goals contradiction

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
  | LamBody =>
    apply IsWellTyped.Lam
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
  | LamBody =>
    apply IsWellTyped.Lam
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

def Term.Reduce.decide : Reduce ctx ty a b -> Reduce ctx ty a c -> b = c := by
  intro ab ac
  induction ab generalizing c with
  | Apply _ _ body_val arg_val=>
    cases ac with
    | Apply => subst c; assumption
    | AppFunc red =>
      have := red.IsNotValue (.Lam _ _ body_val)
      contradiction
    | AppArg _ _ red =>
      have := red.IsNotValue arg_val
      contradiction
  | AppFunc fred _ ih =>
    cases ac with
    | Apply _ _ body_val =>
      have := fred.IsNotValue (.Lam _ _ body_val)
      contradiction
    | AppFunc red =>
      rw [ih]
      rename_i arg₀ _ _ arg₁
      cases arg₀.decide arg₁
      assumption
    | AppArg f_val =>
      have := fred.IsNotValue f_val
      contradiction
  | AppArg f_val _ arg_red ih =>
    cases ac with
    | Apply _ _ _ arg_val =>
      have := arg_red.IsNotValue arg_val
      contradiction
    | AppFunc red =>
      have := red.IsNotValue f_val
      contradiction
    | AppArg f_val =>
      rw [ih]
      rename_i h₀ _ _ h₁ _
      cases h₀.decide h₁
      assumption
  | LamBody _ ih =>
    cases ac
    rw [ih]
    assumption
  | Panic _ _ ih =>
    cases ac
    rw [ih]
    assumption

def Term.Reduce.allHEq (r₀: Term.Reduce ctx ty a b) (r₁: Term.Reduce ctx ty' a c): HEq r₀ r₁ := by
  cases r₀.well_typed_left.decide r₁.well_typed_left
  cases r₀.decide r₁
  rfl

instance Term.decIsLam : ∀a, Decidable (Term.IsLam a)
| .Lam _ _ => .isTrue (.Lam _ _)
| .ConstUnit | .Var _ | .App _ _ | .Panic _ _ => .isFalse (nomatch ·)

instance Term.decIsValue : ∀a, Decidable (Term.IsValue a)
| .ConstUnit => .isTrue .ConstUnit
| .Var _ => .isTrue (.Var _)
| .Lam _ body =>
  match decIsValue body with
  | .isTrue h => .isTrue (.Lam _ _ h)
  | .isFalse h => .isFalse fun h => by cases h <;> contradiction
| .Panic body _ =>
  match decIsValue body with
  | .isTrue h => .isTrue (.Panic _ h)
  | .isFalse h => .isFalse fun h => by cases h <;> contradiction
| .App a b =>
  have := decIsValue a
  have := decIsValue b
  match inferInstanceAs (Decidable (¬a.IsLam ∧ a.IsValue ∧ b.IsValue)) with
  | .isTrue h => .isTrue (.App _ _ h.2.1 h.2.2 h.1)
  | .isFalse h => .isFalse (by intro h₀; apply h; cases h₀ <;> trivial)

def Term.Reduce.ofNotValue {ctx: List LamType} {ty: LamType} : ∀a: Term,
  a.IsWellTyped ctx ty -> ¬a.IsValue -> ∃b, Reduce ctx ty a b := by
  intro a wt not_val
  induction wt with
  | ConstUnit => contradiction
  | Var => exact (not_val (.Var _)).elim
  | Lam body _wt ih =>
    rename_i arg_ty ret_ty ctx
    have ⟨body',red⟩  := ih (fun g => not_val (g.Lam _))
    exists body'.Lam arg_ty
    apply Reduce.LamBody
    assumption
  | Panic body ty _wt ih =>
    rename_i ctx
    have ⟨body',red⟩  := ih (fun g => not_val (g.Panic _))
    exists body'.Panic ty
    apply Reduce.Panic
    assumption
  | App f arg fwt argwt fih argih =>
    if h₁:f.IsValue then
      if h₂:arg.IsValue then
        match f.decIsLam with
        | .isTrue _ =>
          match f with
          | .Lam _ body =>
            refine ⟨_,Term.Reduce.Apply _ ?_ (by cases h₁; assumption) h₂ rfl⟩
            apply IsWellTyped.App
            assumption
            assumption
        | .isFalse h₀ => exact (not_val (.App _ _ h₁ h₂ h₀)).elim
      else
        have ⟨arg',red⟩ := argih h₂
        refine ⟨_,red.AppArg h₁ ?_⟩
        assumption
    else
      have ⟨arg',red⟩ := fih h₁
      refine ⟨_,red.AppFunc ?_⟩
      assumption

inductive Term.Halts (ctx: List LamType) (t: Term) (ty: LamType) : Prop where
| intro (val: Term) (h: val.IsValue) :
  -- reduce to a value
  Chain ctx ty t val -> Halts ctx t ty

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
    have := red.IsNotValue
    contradiction
  | cons r c =>
    cases r.decide red
    assumption
