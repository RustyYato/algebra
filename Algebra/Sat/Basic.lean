import Algebra.WellFounded

inductive Ast (α: Type _) where
| Const (b: Bool)
| Var (a: α)
| And (a b: Ast α)
| Or (a b: Ast α)
| Imp (a b: Ast α)
| Not (a: Ast α)
deriving DecidableEq

def Ast.eval (f: α -> Bool) : Ast α -> Bool
| Const b => b
| Var a => f a
| And a b => a.eval f && b.eval f
| Or a b => a.eval f || b.eval f
| Not a => !a.eval f
| Imp a b => !a.eval f || b.eval f

inductive Ast.isLiteral : Ast α -> Prop where
| Pos (a: α) : isLiteral (.Var a)
| Neg (a: α) : isLiteral (.Not (.Var a))
inductive Ast.isCnfClause : Ast α -> Prop where
| Lit (l: Ast α) : Ast.isLiteral l -> isCnfClause l
| Or (l r: Ast α) : Ast.isCnfClause l -> isCnfClause r -> isCnfClause (.Or l r)
inductive Ast.isCnf : Ast α -> Prop where
| Clause (c: Ast α) : isCnfClause c -> isCnf c
| And (l r: Ast α) : isCnf l -> isCnf r -> isCnf (.And l r)
inductive Ast.isDnfClause : Ast α -> Prop where
| Lit (l: Ast α) : Ast.isLiteral l -> isDnfClause l
| And (l r: Ast α) : Ast.isLiteral l -> isDnfClause r -> isDnfClause (.And l r)
inductive Ast.isDnf : Ast α -> Prop where
| Clause (c: Ast α) : isDnfClause c -> isDnf c
| Or (l r: Ast α) : isDnfClause l -> isDnf r -> isDnf (.Or l r)
-- 3-SAT
inductive Ast.isCnf3 : Ast α -> Prop where
| left (a b c: Ast α) : isCnfClause a -> isCnfClause b -> isCnfClause c -> isCnf3 (.Or (.Or a b)  c)
| right (a b c: Ast α) : isCnfClause a -> isCnfClause b -> isCnfClause c -> isCnf3 (.Or a (.Or b c))

inductive Ast.noImp : Ast α -> Prop where
| Const (b: Bool) : noImp (.Const b)
| Var (a: α) : noImp (.Var a)
| And (a b: Ast α) : noImp a -> noImp b -> noImp (.And a b)
| Or (a b: Ast α) : noImp a -> noImp b -> noImp (.Or a b)
| Not (a: Ast α) : noImp a -> noImp (.Not a)

inductive Ast.noLargeNeg : Ast α -> Prop where
| Const (x: Bool) : noLargeNeg (.Const x)
| Literal (a: Ast α) : isLiteral a -> noLargeNeg a
| And (a b: Ast α) : noLargeNeg a -> noLargeNeg b -> noLargeNeg (.And a b)
| Or (a b: Ast α) : noLargeNeg a -> noLargeNeg b -> noLargeNeg (.Or a b)

inductive Ast.noConsts : Ast α -> Prop where
| Literal (a: Ast α) : isLiteral a -> noConsts a
| And (a b: Ast α) : noConsts a -> noConsts b -> noConsts (.And a b)
| Or (a b: Ast α) : noConsts a -> noConsts b -> noConsts (.Or a b)

inductive Ast.minConst : Ast α -> Prop where
| Const (x: Bool) : minConst (.Const x)
| noConsts (a: Ast α) : noConsts a -> minConst a

inductive Ast.isAnd : Ast α -> Prop where
| intro a b : isAnd (.And a b)
inductive Ast.isOr : Ast α -> Prop where
| intro a b : isOr (.Or a b)
inductive Ast.isConst : Ast α -> Prop where
| intro x : isConst (.Const x)

def Ast.isConst.spec : isConst a -> ∃b, a = .Const b
| intro x => ⟨ x, rfl ⟩

def Ast.minConst.iff (a: Ast α) :
  a.minConst ↔ a.isConst ∨ a.noConsts := by
  apply Iff.intro
  intro h
  cases h
  apply Or.inl; apply isConst.intro
  apply Or.inr; assumption
  intro h
  cases h <;> rename_i h
  cases h
  apply minConst.Const
  apply minConst.noConsts
  assumption

instance Ast.decIsOr (a: Ast α) : Decidable a.isOr := by
  cases a
  any_goals apply Decidable.isFalse; intro h; contradiction
  exact Decidable.isTrue (.intro _ _)

instance Ast.decIsAnd (a: Ast α) : Decidable a.isAnd := by
  cases a
  any_goals apply Decidable.isFalse; intro h; contradiction
  exact Decidable.isTrue (.intro _ _)

instance Ast.decIsConst (a: Ast α) : Decidable a.isConst := by
  cases a
  any_goals apply Decidable.isFalse; intro h; contradiction
  exact Decidable.isTrue (.intro _)

instance Ast.decIsLiteral (a: Ast α) : Decidable a.isLiteral := by
  cases a
  any_goals apply Decidable.isFalse; intro h; contradiction
  apply Decidable.isTrue
  apply Ast.isLiteral.Pos
  rename_i a
  cases a
  any_goals apply Decidable.isFalse; intro h; contradiction
  apply Decidable.isTrue
  apply Ast.isLiteral.Neg

instance Ast.decIsCnfClause (a: Ast α) : Decidable a.isCnfClause := by
  cases decIsOr a
  cases decIsLiteral a
  apply Decidable.isFalse
  intro h
  cases h
  contradiction
  rename_i h _
  have := h (.intro _ _)
  contradiction
  apply Decidable.isTrue
  apply isCnfClause.Lit
  assumption
  rename_i h
  cases a
  any_goals contradiction
  rename_i a b
  cases decIsCnfClause a
  apply Decidable.isFalse; intro g
  cases g <;> contradiction
  cases decIsCnfClause b
  apply Decidable.isFalse; intro g
  cases g <;> contradiction
  apply Decidable.isTrue
  apply isCnfClause.Or <;> assumption

instance Ast.decIsCnf (a: Ast α) : Decidable a.isCnf := by
  cases decIsAnd a
  cases decIsCnfClause a
  apply Decidable.isFalse
  intro h
  cases h
  contradiction
  rename_i h _
  have := h (.intro _ _)
  contradiction
  apply Decidable.isTrue
  apply isCnf.Clause
  assumption
  rename_i h
  cases a
  any_goals contradiction
  rename_i a b
  cases decIsCnf a
  apply Decidable.isFalse; intro g
  cases g <;> contradiction
  cases decIsCnf b
  apply Decidable.isFalse; intro g
  cases g <;> contradiction
  apply Decidable.isTrue
  apply isCnf.And <;> assumption

def Ast.simplify_imp : Ast α -> Ast α
| .Imp a b => .Or (.Not a.simplify_imp) b.simplify_imp
| .Const x => .Const x
| .Var x => .Var x
| .Not a => .Not a.simplify_imp
| .Or a b => .Or a.simplify_imp b.simplify_imp
| .And a b => .And a.simplify_imp b.simplify_imp

def Ast.simplify_imp.spec (a: Ast α) : a.simplify_imp.noImp := by
  induction a with
  | Const x => apply noImp.Const
  | Var x => apply noImp.Var
  | And a b aih bih => apply noImp.And _ _ aih bih
  | Or a b aih bih => apply noImp.Or _ _ aih bih
  | Not a aih => apply noImp.Not _ aih
  | Imp a b aih bih =>
    apply noImp.Or
    apply noImp.Not _ aih
    exact bih

def Ast.simplify_imp.sound (a: Ast α) (f: α -> Bool) : a.eval f = a.simplify_imp.eval f := by
  induction a with
  | Const _ => rfl
  | Var _ => rfl
  | And a b aih bih =>
    unfold simplify_imp eval
    rw [←aih, ←bih]
  | Or a b aih bih =>
    unfold simplify_imp eval
    rw [←aih, ←bih]
  | Imp a b aih bih =>
    unfold simplify_imp eval
    rw [eval]
    rw [←aih, ←bih]
  | Not a aih =>
    unfold simplify_imp eval
    rw [←aih]

def Ast.push_neg_with : Bool -> Ast α -> Ast α
| is_negated, .Const x => .Const (x.xor is_negated)
| false, .Var x => .Var x
| true, .Var x => .Not (.Var x)
| is_negated, .Not a => a.push_neg_with !is_negated
| false, .Imp a b => .Imp (a.push_neg_with false) (b.push_neg_with false)
| true, .Imp a b => .And (a.push_neg_with false) (b.push_neg_with true)
| false, .Or a b => .Or (a.push_neg_with false) (b.push_neg_with false)
| false, .And a b => .And (a.push_neg_with false) (b.push_neg_with false)
| true, .Or a b => .And (a.push_neg_with true) (b.push_neg_with true)
| true, .And a b => .Or (a.push_neg_with true) (b.push_neg_with true)

def Ast.push_neg (a: Ast α) : Ast α := a.push_neg_with false

def Ast.push_neg_with.spec (a: Ast α) (x: Bool) : a.noImp -> (a.push_neg_with x).noLargeNeg := by
  intro no_imp
  induction no_imp generalizing x with
  | Const _ => cases x <;> apply noLargeNeg.Const
  | Var _ =>
    cases x <;> apply noLargeNeg.Literal
    apply isLiteral.Pos
    apply isLiteral.Neg
  | Or a b _ _ aih bih =>
    cases x
    apply noLargeNeg.Or
    apply aih
    apply bih
    apply noLargeNeg.And
    apply aih
    apply bih
  | And a b _ _ aih bih =>
    cases x
    apply noLargeNeg.And
    apply aih
    apply bih
    apply noLargeNeg.Or
    apply aih
    apply bih
  | Not a _ aih =>
    cases x <;> apply aih

def Ast.push_neg.spec (a: Ast α) : a.noImp -> a.push_neg.noLargeNeg := by apply Ast.push_neg_with.spec

def Ast.push_neg_with.sound (a: Ast α) (x: Bool) (f: α -> Bool) : a.eval f = xor x ((a.push_neg_with x).eval f) := by
  induction a generalizing x with
  | Const b =>
    unfold push_neg_with eval
    cases x <;> cases b <;> rfl
  | Var a =>
    unfold push_neg_with eval
    cases x <;> dsimp
    rw [Bool.false_xor]
    rw [Bool.true_xor, Bool.not_not]
    rfl
  | And a b aih bih =>
    unfold push_neg_with eval
    cases x <;> dsimp
    rw [aih false, bih false]
    repeat rw [Bool.false_xor]
    rw [Bool.true_xor, Bool.not_or, ←Bool.true_xor, ←Bool.true_xor, ←aih, ←bih]
  | Or a b aih bih =>
    unfold push_neg_with eval
    cases x <;> dsimp
    rw [aih false, bih false]
    repeat rw [Bool.false_xor]
    rw [Bool.true_xor, Bool.not_and, ←Bool.true_xor, ←Bool.true_xor, ←aih, ←bih]
  | Imp a b aih bih =>
    unfold push_neg_with
    cases x <;> dsimp [eval]
    rw [Bool.false_xor]
    rw [←Bool.false_xor (eval f (push_neg_with false _)), ←aih]
    rw [←Bool.false_xor (eval f (push_neg_with false _)), ←bih]
    rw [Bool.true_xor]
    rw [←Bool.false_xor (eval f (push_neg_with false _)), ←aih]
    rw [
      ←Bool.not_not (eval f (push_neg_with true _)),
      ←Bool.true_xor (eval f (push_neg_with true _)), ←bih]
    rw [Bool.not_and, Bool.not_not]
  | Not a aih =>
    unfold push_neg_with
    rw [eval]
    cases x <;> dsimp
    rw [Bool.false_xor]
    conv => {
      rhs
      rw [←Bool.not_not (eval _ _), ←Bool.true_xor (eval _ _)]
    }
    rw [Bool.not_false, ←aih]
    rw [Bool.true_xor]
    conv => {
      rhs
      rw [←Bool.false_xor (eval _ _)]
    }
    rw [Bool.not_true, ←aih]

def Ast.push_neg.sound (a: Ast α) (f: α -> Bool) : a.eval f = (a.push_neg.eval f) := by
  rw [push_neg_with.sound _ false, Bool.false_xor]
  rfl

def Ast.elim_consts : Ast α -> Ast α
| .Const x => .Const x
| .Not x => .Not x
| .Var x => .Var x
-- unreachable
| .Imp _ _ => .Const false
| .And a b => match a.elim_consts with
  | .Const true => b.elim_consts
  | .Const false => .Const false
  | a => match b.elim_consts with
    | .Const true => a
    | .Const false => .Const false
    | b => .And a b
| .Or a b => match a.elim_consts with
  | .Const false => b.elim_consts
  | .Const true => .Const true
  | a => match b.elim_consts with
    | .Const false => a
    | .Const true => .Const true
    | b => .Or a b

def Ast.elim_consts.spec (a: Ast α) : a.noLargeNeg -> a.elim_consts.minConst := by
  intro h
  induction h with
  | Const x => apply minConst.Const
  | Literal x h =>
    cases h <;> (apply minConst.noConsts; apply noConsts.Literal)
    apply isLiteral.Pos
    apply isLiteral.Neg
  | And a b _ _ aih bih =>
    unfold elim_consts
    split
    assumption
    apply minConst.Const
    split
    assumption
    apply minConst.Const
    apply minConst.noConsts
    generalize ha:a.elim_consts=a'
    generalize hb:b.elim_consts=b'
    rename_i ha₀ ha₁ _ hb₀ hb₁
    rw [ha] at aih ha₀ ha₁
    rw [hb] at bih hb₀ hb₁
    clear ha hb
    apply noConsts.And
    cases aih
    rename_i a
    cases a <;> contradiction
    assumption
    cases bih
    rename_i b
    cases b <;> contradiction
    assumption
  | Or a b _ _ aih bih =>
    unfold elim_consts
    split
    assumption
    apply minConst.Const
    split
    assumption
    apply minConst.Const
    apply minConst.noConsts
    generalize ha:a.elim_consts=a'
    generalize hb:b.elim_consts=b'
    rename_i ha₀ ha₁ _ hb₀ hb₁
    rw [ha] at aih ha₀ ha₁
    rw [hb] at bih hb₀ hb₁
    clear ha hb
    apply noConsts.Or
    cases aih
    rename_i a
    cases a <;> contradiction
    assumption
    cases bih
    rename_i b
    cases b <;> contradiction
    assumption

def Ast.elim_consts.sound (a: Ast α) (f: α -> Bool) : a.noLargeNeg -> a.eval f = a.elim_consts.eval f := by
  intro h
  induction h with
  | Const x => rfl
  | Literal x h => cases h <;> rfl
  | And a b _ _ aih bih =>
    unfold elim_consts
    split <;> rename_i ha₀
    rw [eval, aih, bih, ha₀, eval, Bool.true_and]
    rw [eval, eval, aih, ha₀, eval, Bool.false_and]
    split <;> rename_i hb₀
    rw [eval, aih, bih, hb₀, eval, Bool.and_true]
    rw [eval, eval, bih, hb₀, eval, Bool.and_false]
    rw [eval, eval, aih, bih]
  | Or a b _ _ aih bih =>
    unfold elim_consts
    split <;> rename_i ha₀
    rw [eval, aih, bih, ha₀, eval, Bool.false_or]
    rw [eval, eval, aih, ha₀, eval, Bool.true_or]
    split <;> rename_i hb₀
    rw [eval, aih, bih, hb₀, eval, Bool.or_false]
    rw [eval, eval, bih, hb₀, eval, Bool.or_true]
    rw [eval, eval, aih, bih]

def Ast.orCnf (a b: Ast α) : Ast α :=
  match a with
  | .And a₀ a₁ => .And (a₀.orCnf b) (a₁.orCnf b)
  | a => match b with
    | .And b₀ b₁ => .And (a.orCnf b₀) (a.orCnf b₁)
    | b => .Or a b
termination_by Prod'.mk a b
decreasing_by
  apply Prod'.LexAny.left
  apply Nat.lt_of_lt_of_le
  apply Nat.lt_succ_self
  dsimp
  rw [Nat.add_comm]
  apply Nat.le_add_right
  apply Prod'.LexAny.left
  apply Nat.lt_of_lt_of_le
  apply Nat.lt_succ_self
  dsimp
  rw [Nat.add_comm, Nat.add_right_comm]
  apply Nat.le_add_right

  apply Prod'.LexAny.right
  apply Nat.lt_of_lt_of_le
  apply Nat.lt_succ_self
  dsimp
  rw [Nat.add_comm]
  apply Nat.le_add_right
  apply Prod'.LexAny.right
  apply Nat.lt_of_lt_of_le
  apply Nat.lt_succ_self
  dsimp
  rw [Nat.add_comm, Nat.add_right_comm]
  apply Nat.le_add_right

def Ast.orCnf.spec (a b: Ast α) :
  a.isCnf ->
  b.isCnf ->
  (a.orCnf b).isCnf := by
  induction a, b using Ast.orCnf.induct
  rename_i a b c aih bih
  intro abCnf cCnf
  cases abCnf
  contradiction
  unfold orCnf
  apply isCnf.And
  apply aih <;> assumption
  apply bih <;> assumption
  rename_i a h b c aih bih
  intro aCnf bcCnf
  unfold orCnf
  split
  have := h _ _ rfl
  contradiction
  cases bcCnf
  contradiction
  apply isCnf.And
  apply aih <;> assumption
  apply bih <;> assumption
  rename_i a h₀ b h₁
  intro aCnf bCnf
  unfold orCnf
  split
  have := h₀ _ _ rfl
  contradiction
  split
  have := h₁ _ _ rfl
  contradiction
  cases aCnf
  cases bCnf
  apply isCnf.Clause
  apply isCnfClause.Or <;> assumption
  have := h₁ _ _ rfl
  contradiction
  have := h₀ _ _ rfl
  contradiction

def Ast.orCnf.sound (a b: Ast α) (f: α -> Bool) :
  (a.orCnf b).eval f = (a.eval f || b.eval f) := by
  induction a, b using Ast.orCnf.induct
  rename_i a b c aih bih
  rw [eval]
  unfold orCnf
  rw [eval, Bool.or_and_distrib_right, ←aih, ←bih]
  rename_i a h b c aih bih
  rw [eval, Bool.or_and_distrib_left]
  unfold orCnf
  split
  have := h _ _ rfl
  contradiction
  rw [←aih, ←bih]
  rfl
  rename_i a h₀ b h₁
  unfold orCnf
  split
  have := h₀ _ _ rfl
  contradiction
  split
  have := h₁ _ _ rfl
  contradiction
  rfl

def Ast.toCnf' : Ast α -> Ast α
| .Const x => .Const x
-- unreachable
| .Imp _ _ => .Const false
-- always a literal
| .Not a => .Not a
| .Var a => .Var a
| .And a b => .And a.toCnf' b.toCnf'
| .Or a b => a.toCnf'.orCnf b.toCnf'

def Ast.toCnf'.spec (a: Ast α) : a.noConsts -> a.toCnf'.isCnf := by
  intro h
  induction h with
  | Literal a h =>
    cases h <;> (
      apply isCnf.Clause
      apply isCnfClause.Lit
    )
    apply isLiteral.Pos
    apply isLiteral.Neg
  | And a b _ _ aih bih => apply isCnf.And <;> assumption
  | Or a b _ _ aih bih => apply orCnf.spec <;> assumption

def Ast.toCnf (a: Ast α) :=
  a.simplify_imp.push_neg.elim_consts.toCnf'

def Ast.toCnf.spec (a: Ast α) : a.toCnf.isCnf ∨ a.toCnf.isConst := by
  cases decIsConst a.toCnf
  · apply Or.inl
    rename_i cnf_nontrivial
    unfold toCnf
    have h := Ast.simplify_imp.spec a
    replace h := Ast.push_neg.spec _ h
    replace h := Ast.elim_consts.spec _ h
    cases (Ast.minConst.iff _).mp h
    apply Ast.toCnf'.spec
    · rename_i h
      have ⟨ b, prf ⟩  := h.spec
      unfold toCnf toCnf' at cnf_nontrivial
      rw [prf] at cnf_nontrivial
      have := cnf_nontrivial (.intro b)
      contradiction
    apply Ast.toCnf'.spec
    assumption
  · apply Or.inr
    assumption
