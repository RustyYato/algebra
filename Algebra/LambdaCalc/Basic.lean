inductive LamType where
| Unit
| Void
| Fn (arg ret: LamType)

inductive Term where
| ConstUnit
| Var (id: Nat)
| Lam (body: Term)
| App (f arg: Term)
| Panic (body: Term)

-- under a given context `ctx`, does term `t` have type `ty`
inductive Term.IsWellTyped : (ctx: List LamType) -> (t: Term) -> (ty: LamType) -> Prop where
| ConstUnit : IsWellTyped ctx .ConstUnit .Unit
| Var (id: Nat) (ty: LamType) (h: id < ctx.length) : ty = ctx[id] -> IsWellTyped ctx (.Var id) ty
| Lam (body: Term) : IsWellTyped (arg_ty::ctx) body ret_ty -> IsWellTyped ctx (.Lam body) (.Fn arg_ty ret_ty)
| App (f arg: Term) : IsWellTyped ctx f (.Fn arg_ty ret_ty) -> IsWellTyped ctx f ret_ty -> IsWellTyped ctx (.App f arg) ret_ty
| Panic (body: Term) (ty: LamType) : IsWellTyped ctx body .Void -> IsWellTyped ctx (.Panic body) ty

def Term.weakenAt (varid: Nat) : Term -> Term
| .ConstUnit => .ConstUnit
| .Lam body => .Lam (body.weakenAt varid.succ)
| .Panic body => .Panic (body.weakenAt varid)
| .App f arg => .App (f.weakenAt varid) (arg.weakenAt varid)
| .Var id => .Var <| if id < varid then id else id.succ

def Term.weaken : Term -> Term := weakenAt 0

def Term.substAt (repl: Term) (varid: Nat) : Term -> Term
| .ConstUnit => .ConstUnit
| .Panic body => .Panic (Term.substAt repl varid body)
| .App f arg => .App (Term.substAt repl varid f) (Term.substAt repl varid arg)
| .Lam body => .Lam (Term.substAt repl.weaken varid.succ body)
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
