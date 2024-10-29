import Algebra.AxiomBlame

inductive BitInt.Bits where
| pos: Bits -- non-negative
| neg: Bits -- negative
| bit: Bool -> Bits -> Bits
deriving DecidableEq

instance : Repr BitInt.Bits where
  reprPrec b _prec := by
    let rec repr : BitInt.Bits -> Lean.Format
      | .pos => "+"
      | .neg => "-"
      | .bit b bs => (repr bs) ++ reprPrec (if b then 1 else 0) 1
    exact repr b

inductive BitInt.Bits.Equiv : Bits -> Bits -> Prop
| pos : Equiv .pos .pos
| neg : Equiv .neg .neg
| pos_false : Equiv .pos xs -> Equiv .pos (.bit false xs)
| neg_true : Equiv .neg xs -> Equiv .neg (.bit true xs)
| false_pos : Equiv xs .pos -> Equiv (.bit false xs) .pos
| true_neg : Equiv xs .neg -> Equiv (.bit true xs) .neg
| bit : Equiv as bs -> Equiv (.bit x as) (.bit x bs)

instance BitInt.Bits.setoid : Setoid Bits where
  r := Bits.Equiv
  iseqv.refl := by
    intro x
    induction x with
    | pos => exact .pos
    | neg => exact .neg
    | bit b bs ih => exact ih.bit
  iseqv.symm := by
    intro x y h
    induction h with
    | pos => exact .pos
    | neg => exact .neg
    | pos_false _ ih => exact ih.false_pos
    | neg_true _ ih => exact ih.true_neg
    | false_pos _ ih => exact ih.pos_false
    | true_neg _ ih => exact ih.neg_true
    | bit _ ih => exact ih.bit
  iseqv.trans := by
    intro a b c ab bc
    induction ab generalizing c with
    | pos => exact bc
    | neg => exact bc
    | pos_false _ ih =>
      cases bc
      exact .pos
      apply Equiv.pos_false
      apply ih
      assumption
    | neg_true _ ih =>
      cases bc
      exact .neg
      apply Equiv.neg_true
      apply ih
      assumption
    | false_pos _ ih =>
      cases bc
      apply Equiv.false_pos
      apply ih
      exact .pos
      apply Equiv.bit
      apply ih
      assumption
    | true_neg _ ih =>
      cases bc
      apply Equiv.true_neg
      apply ih
      exact .neg
      apply Equiv.bit
      apply ih
      assumption
    | bit _ ih =>
      cases bc
      apply Equiv.false_pos
      apply ih
      assumption
      apply Equiv.true_neg
      apply ih
      assumption
      apply Equiv.bit
      apply ih
      assumption

@[refl]
def BitInt.Bits.refl : ∀(a: Bits), a ≈ a := BitInt.Bits.setoid.iseqv.refl
@[symm]
def BitInt.Bits.symm : ∀{a b: Bits}, a ≈ b -> b ≈ a := BitInt.Bits.setoid.iseqv.symm
def BitInt.Bits.trans : ∀{a b: Bits}, a ≈ b -> b ≈ c -> a ≈ c := BitInt.Bits.setoid.iseqv.trans

inductive BitInt.Bits.IsMinimal : Bits -> Prop
| pos : IsMinimal .pos
| neg : IsMinimal .neg
| b0 : xs ≠ .pos -> IsMinimal xs -> IsMinimal (.bit false xs)
| b1 : xs ≠ .neg -> IsMinimal xs -> IsMinimal (.bit true xs)

instance BitInt.decIsMinimal (x: Bits) : Decidable (x.IsMinimal) :=
  match x with
  | .pos => .isTrue .pos
  | .neg => .isTrue .neg
  | .bit false x =>
    match decEq x .pos with
    | .isTrue h => .isFalse (fun
        | .b0 g _ => g h)
    | .isFalse h₀ =>
    match decIsMinimal x with
    | .isFalse h => .isFalse (fun
        | .b0 _ g => h g)
    | .isTrue h₁ => .isTrue (.b0 h₀ h₁)
  | .bit true x =>
    match decEq x .neg with
    | .isTrue h => .isFalse (fun
        | .b1 g _ => g h)
    | .isFalse h₀ =>
    match decIsMinimal x with
    | .isFalse h => .isFalse (fun
        | .b1 _ g => h g)
    | .isTrue h₁ => .isTrue (.b1 h₀ h₁)

def BitInt.decEqPos : ∀(a: Bits), Decidable (Bits.pos ≈ a)
| .pos => .isTrue .pos
| .neg => .isFalse (nomatch ·)
| .bit false as =>
  match decEqPos as with
  | .isTrue h => .isTrue h.pos_false
  | .isFalse h => .isFalse (fun g => by cases g; contradiction)
| .bit true as => .isFalse (nomatch ·)

def BitInt.decEqNeg : ∀(a: Bits), Decidable (Bits.neg ≈ a)
| .neg => .isTrue .neg
| .pos => .isFalse (nomatch ·)
| .bit true as =>
  match decEqNeg as with
  | .isTrue h => .isTrue h.neg_true
  | .isFalse h => .isFalse (fun g => by cases g; contradiction)
| .bit false as => .isFalse (nomatch ·)
def BitInt.decEqSymm {a b: Bits} : Decidable (b ≈ a) -> Decidable (a ≈ b)
| .isTrue h => .isTrue (Bits.symm h)
| .isFalse h => .isFalse (fun g => h (Bits.symm g))

instance BitInt.decEquiv (a b: Bits) : Decidable (a ≈ b) :=
  match a, b with
  | .pos, _ => BitInt.decEqPos _
  | .neg, _ => BitInt.decEqNeg _
  | _, .pos => BitInt.decEqSymm (BitInt.decEqPos _)
  | _, .neg => BitInt.decEqSymm (BitInt.decEqNeg _)
  | .bit true as, .bit false bs
  | .bit false as, .bit true bs => .isFalse (nomatch ·)
  | .bit false as, .bit false bs
  | .bit true as, .bit true bs =>
    match decEquiv as bs with
    | .isTrue h => .isTrue h.bit
    | .isFalse h => .isFalse (fun g => by cases g; contradiction)

#print axioms BitInt.decEquiv

def BitInt.Bits.IsMinimal.spec (a b: Bits) : a ≈ b -> a.IsMinimal -> b.IsMinimal -> a = b := by
  intro eq amin bmin
  induction eq with
  | pos => rfl
  | neg => rfl
  | pos_false _ ih | neg_true _ ih =>
    cases bmin
    rename_i bmin
    cases ih amin bmin
    contradiction
  | false_pos _ ih | true_neg _ ih =>
    cases amin
    rename_i amin
    cases ih amin bmin
    contradiction
  | bit _ ih =>
    congr
    apply ih
    cases amin <;> assumption
    cases bmin <;> assumption

def BitInt.Bits.push_bit : Bool -> Bits -> Bits
| false, .pos => .pos
| true, .neg => .neg
| b, bs => .bit b bs

def BitInt.Bits.push_bit.spec (b: Bool) : bs.IsMinimal -> Bits.bit b bs ≈ push_bit b bs ∧ (push_bit b bs).IsMinimal := by
  intro min
  induction min with
  | pos =>
    unfold push_bit
    split
    decide
    contradiction
    rename_i x _ _ h _
    cases x
    have := h rfl rfl
    contradiction
    decide
  | neg =>
    unfold push_bit
    split
    contradiction
    decide
    rename_i x _ _ _ h
    cases x
    decide
    have := h rfl rfl
    contradiction
  | b0 next_not_pos min ih =>
    cases b
    apply And.intro
    rfl
    apply IsMinimal.b0
    exact (nomatch ·)
    apply IsMinimal.b0 <;> assumption
    apply And.intro
    rfl
    apply IsMinimal.b1
    exact (nomatch ·)
    apply IsMinimal.b0 <;> assumption
  | b1 next_not_pos min ih =>
    cases b
    apply And.intro
    rfl
    apply IsMinimal.b0
    exact (nomatch ·)
    apply IsMinimal.b1 <;> assumption
    apply And.intro
    rfl
    apply IsMinimal.b1
    exact (nomatch ·)
    apply IsMinimal.b1 <;> assumption

def BitInt.Bits.minimize : Bits -> Bits
| .pos => .pos
| .neg => .neg
| .bit b bs => bs.minimize.push_bit b

def BitInt.Bits.minimize.spec : ∀b: Bits, b ≈ b.minimize ∧ b.minimize.IsMinimal := by
  intro b
  induction b with
  | pos => exact ⟨.pos,.pos⟩
  | neg => exact ⟨.neg,.neg⟩
  | bit b bs ih =>
    have := push_bit.spec b ih.right
    apply And.intro _ this.right
    apply Bits.trans ih.left.bit this.left

-- at this point we've established that (BitInt.Bits, ≈) is a setoid
-- and every BitInt.Bits can be canonicalized via `BitInt.Bits.minimize`.
-- These are provable canonical given by `BitInt.Bits.IsMinimal.spec`.
-- We also show that all `Bits` can be embedded into the set of minimal elements
-- with `BitInt.Bits.minimize`. `BitInt.Bits.minimize.spec` proves that
-- `minimize` respects the `≈` and is a true minimal elemnt.
--
-- this means that `{ x: BitInt.Bits // x.IsMinimal }` actually forms a quotient
-- type for `BitInt.Bits` under the relation `≈`. Note: that `IsMinimal.spec`
-- is eerily similar to `Quot.sound`! That's becuase they have the same
-- signature! And without a single axiom in sight.

def x := { x: BitInt.Bits // x.IsMinimal }
structure BitInt where
  ofBits ::
  bits: BitInt.Bits
  is_minimal: bits.IsMinimal
deriving Repr

instance : Repr BitInt where
  reprPrec b prec := reprPrec b.bits prec

def BitInt.bits.inj : ∀(a b: BitInt), a.bits = b.bits -> a = b
| .ofBits _ _, .ofBits _ _, .refl _ => .refl _

def BitInt.mk (bits: Bits) : BitInt := .ofBits bits.minimize (BitInt.Bits.minimize.spec bits).right

def BitInt.sound : ∀a b: BitInt, a.bits ≈ b.bits -> a = b := by
  intro a b eq
  apply bits.inj
  apply Bits.IsMinimal.spec
  assumption
  exact a.is_minimal
  exact b.is_minimal

def BitInt.Bits.ofNat.rec_lemma : (n + 1) / 2 < n.succ := by
  rw [Nat.div_eq]
  cases (inferInstance : Decidable (0 < 2 ∧ 2 ≤ n + 1)) with
  | isFalse h =>
    rw [if_neg h]
    exact Nat.zero_lt_succ _
  | isTrue h =>
    rw [if_pos h]
    apply Nat.succ_lt_succ
    cases n with
    | zero => contradiction
    | succ n =>
      have : n + 1 + 1 = n + 2 := rfl
      rw [this, Nat.succ_sub_succ, Nat.succ_sub_succ, Nat.sub_zero]
      clear this h
      induction n using Nat.strongInductionOn with
      | ind n ih =>
      cases Nat.decLt n 2 <;> rename_i h
      · replace h := Nat.le_of_not_lt h
        have := ih (n - 2) (Nat.sub_lt_self (by trivial) h)
        rw [Nat.div_eq]
        rw [if_pos]
        apply Nat.succ_lt_succ
        apply Nat.lt_of_lt_of_le this
        · cases n with
          | zero => contradiction
          | succ n =>
          cases n with
          | zero => contradiction
          | succ n =>
          rw [Nat.succ_sub_succ, Nat.succ_sub_succ, Nat.sub_zero]
          apply Nat.le_succ
        · apply And.intro
          trivial
          assumption
      · rw [Nat.div_eq, if_neg]
        apply Nat.zero_lt_succ
        intro g
        exact Nat.not_lt_of_le g.right h

@[reducible]
def BitInt.Bits.ofNat : Nat -> Bits
| 0 => .pos
| n + 1 => .bit ((n + 1) % 2 == 1) (ofNat ((n + 1) / 2))
decreasing_by
  exact ofNat.rec_lemma

def BitInt.Bits.ofNat_eq_zero_iff (n: Nat) : n = 0 ↔ BitInt.Bits.ofNat n = .pos := by
  apply Iff.intro
  · intro h
    subst h
    rfl
  · intro h
    cases n
    rfl
    contradiction

def BitInt.Bits.ofNat_ne_neg (n: Nat) : BitInt.Bits.ofNat n ≠ .neg := by
  intro h
  cases n
  contradiction
  contradiction

def BitInt.Bits.ofNat.is_minimal (n: Nat) : (ofNat n).IsMinimal := by
  induction n using BitInt.Bits.ofNat.induct with
  | case1 => exact .pos
  | case2 n ih =>
    unfold ofNat
    cases h:(n + 1) % 2
    apply ih.b0
    intro g
    have := (ofNat_eq_zero_iff ((n + 1) / 2)).mpr g
    have : n + 1 < 2 := by
      cases n
      trivial
      rename_i n
      cases n
      trivial
      rw [Nat.div_eq, if_pos] at this
      contradiction
      apply And.intro
      trivial
      apply Nat.succ_le_succ
      apply Nat.succ_le_succ
      apply Nat.zero_le
    match n with
    | 0 => contradiction
    | 1 => contradiction
    | n + 2 =>
      have := Nat.lt_of_succ_lt_succ this
      have := Nat.lt_of_succ_lt_succ this
      exact Nat.not_lt_zero _ this
    rename_i m
    cases m
    apply ih.b1
    apply ofNat_ne_neg
    have := @Nat.mod_lt (n + 1) 2 (by trivial)
    rw [h] at this
    have := Nat.lt_of_succ_lt_succ this
    have := Nat.lt_of_succ_lt_succ this
    exact (Nat.not_lt_zero _ this).elim

instance BitInt.Bits.OfNatInst : OfNat BitInt n := ⟨⟨.ofNat n,ofNat.is_minimal n⟩⟩
