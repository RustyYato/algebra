import Algebra.Nat.Div
import Algebra.Nat.WellFounded
import Algebra.AxiomBlame

inductive BitInt.Bits where
| nil: (is_neg: Bool) -> Bits
| bit: Bool -> Bits -> Bits
deriving DecidableEq

instance : Repr BitInt.Bits where
  reprPrec b _prec := by
    let rec repr : BitInt.Bits -> Lean.Format
      | .nil false => "+"
      | .nil true => "-"
      | .bit b bs => (repr bs) ++ reprPrec (if b then 1 else 0) 1
    exact repr b

inductive BitInt.Bits.Equiv : Bits -> Bits -> Prop
| nil_nil x : Equiv (.nil x) (.nil x)
| nil_bit x xs : Equiv (.nil x) xs -> Equiv (.nil x) (.bit x xs)
| bit_nil x xs : Equiv xs (.nil x) -> Equiv (.bit x xs) (.nil x)
| bit_bit x as bs : Equiv as bs -> Equiv (.bit x as) (.bit x bs)

instance BitInt.Bits.setoid : Setoid Bits where
  r := Bits.Equiv
  iseqv.refl := by
    intro x
    induction x with
    | nil => exact Equiv.nil_nil _
    | bit b bs ih => exact ih.bit_bit _
  iseqv.symm := by
    intro x y h
    induction h with
    | nil_nil => exact Equiv.nil_nil _
    | nil_bit _ _ _ ih => exact ih.bit_nil
    | bit_nil _ _ _ ih => exact ih.nil_bit
    | bit_bit _ _ _ _ ih => exact ih.bit_bit _
  iseqv.trans := by
    intro a b c ab bc
    induction ab generalizing c with
    | nil_nil => exact bc
    | nil_bit _ _ _ ih =>
      cases bc
      exact Equiv.nil_nil _
      apply Equiv.nil_bit
      apply ih
      assumption
    | bit_nil _ _ _ ih =>
      cases bc
      apply Equiv.bit_nil
      assumption
      apply Equiv.bit_bit
      apply ih
      assumption
    | bit_bit _ _ _ _ ih =>
      cases bc
      apply Equiv.bit_nil
      apply ih
      assumption
      apply Equiv.bit_bit
      apply ih
      assumption

@[refl]
def BitInt.Bits.refl : ∀(a: Bits), a ≈ a := BitInt.Bits.setoid.iseqv.refl
@[symm]
def BitInt.Bits.symm : ∀{a b: Bits}, a ≈ b -> b ≈ a := BitInt.Bits.setoid.iseqv.symm
def BitInt.Bits.trans : ∀{a b: Bits}, a ≈ b -> b ≈ c -> a ≈ c := BitInt.Bits.setoid.iseqv.trans

def BitInt.Bits.nil_nil : (nil a) ≈ (nil a) := Equiv.nil_nil _
def BitInt.Bits.bit_nil : as ≈ (nil a) -> (bit a as) ≈ (nil a) := Equiv.bit_nil _ _
def BitInt.Bits.nil_bit : (nil a) ≈ as -> (nil a) ≈ (bit a as) := Equiv.nil_bit _ _
def BitInt.Bits.bit_bit : as ≈ bs -> (bit x as) ≈ (bit x bs) := Equiv.bit_bit _ _ _

inductive BitInt.Bits.IsMinimal : Bits -> Prop
| nil x : IsMinimal (.nil x)
| bit x xs : xs ≠ .nil x -> IsMinimal xs -> IsMinimal (.bit x xs)

instance BitInt.decIsMinimal (x: Bits) : Decidable (x.IsMinimal) :=
  match x with
  | .nil _ => .isTrue (.nil _)
  | .bit x xs =>
    match decEq xs (.nil x) with
    | .isTrue h => .isFalse (fun
        | .bit _ _ g _ => g h)
    | .isFalse h₀ =>
    match decIsMinimal xs with
    | .isFalse h => .isFalse (fun
        | .bit _ _ _ g => h g)
    | .isTrue h₁ => .isTrue (.bit _ _ h₀ h₁)

def BitInt.decEqNil : ∀(a: Bits) (b: Bool), Decidable (Bits.nil b ≈ a)
| .nil true, true | .nil false, false => .isTrue (.nil_nil _)
| .nil true, false | .nil false, true
| .bit true xs, false | .bit false xs, true => .isFalse (nomatch ·)
| .bit true xs, true | .bit false xs, false =>
  match decEqNil xs _ with
  | .isTrue h => .isTrue h.nil_bit
  | .isFalse h => .isFalse (fun g => by cases g; contradiction)

def BitInt.decEqSymm {a b: Bits} : Decidable (b ≈ a) -> Decidable (a ≈ b)
| .isTrue h => .isTrue (Bits.symm h)
| .isFalse h => .isFalse (fun g => h (Bits.symm g))

instance BitInt.decEquiv (a b: Bits) : Decidable (a ≈ b) :=
  match a, b with
  | .nil _, _ => BitInt.decEqNil _ _
  | _, .nil _ => BitInt.decEqSymm (BitInt.decEqNil _ _)
  | .bit true as, .bit false bs
  | .bit false as, .bit true bs => .isFalse (nomatch ·)
  | .bit false as, .bit false bs
  | .bit true as, .bit true bs =>
    match decEquiv as bs with
    | .isTrue h => .isTrue (h.bit_bit _)
    | .isFalse h => .isFalse (fun g => by cases g; contradiction)

def BitInt.Bits.IsMinimal.spec (a b: Bits) : a ≈ b -> a.IsMinimal -> b.IsMinimal -> a = b := by
  intro eq amin bmin
  induction eq with
  | nil_nil => rfl
  | nil_bit _ _ _ ih =>
    cases bmin
    rename_i bmin
    have := bmin.symm (ih amin (by assumption))
    contradiction
  | bit_nil _ _ _ ih =>
    cases amin
    rename_i amin
    have := amin (ih (by assumption) bmin)
    contradiction
  | bit_bit _ _ _ _ ih =>
    congr
    apply ih
    cases amin <;> assumption
    cases bmin <;> assumption

def BitInt.Bits.push_bit : Bool -> Bits -> Bits
| false, .nil false => .nil false
| true, .nil true => .nil true
| b, bs => .bit b bs

def BitInt.Bits.push_bit.spec (b: Bool) : bs.IsMinimal -> Bits.bit b bs ≈ push_bit b bs ∧ (push_bit b bs).IsMinimal := by
  intro min
  induction min generalizing b with
  | nil b' =>
    clear bs
    revert b b'
    decide
  | bit =>
    unfold push_bit
    split
    any_goals contradiction
    apply And.intro
    apply Bits.refl
    apply IsMinimal.bit
    exact Bits.noConfusion
    apply IsMinimal.bit
    assumption
    assumption

def BitInt.Bits.minimize : Bits -> Bits
| .nil x => .nil x
| .bit b bs => bs.minimize.push_bit b

def BitInt.Bits.minimize.spec : ∀b: Bits, b ≈ b.minimize ∧ b.minimize.IsMinimal := by
  intro b
  induction b with
  | nil => exact ⟨.nil_nil _,.nil _⟩
  | bit b bs ih =>
    have := push_bit.spec b ih.right
    apply And.intro _ this.right
    apply Bits.trans (ih.left.bit_bit _) this.left

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

def BitInt.sound' : ∀a b: BitInt, a.bits ≈ b.bits -> a = b := by
  intro a b eq
  apply bits.inj
  apply Bits.IsMinimal.spec
  assumption
  exact a.is_minimal
  exact b.is_minimal
def BitInt.sound : ∀{a b: Bits}, a ≈ b -> mk a = mk b := by
  intro a b eq
  apply sound'
  unfold mk
  dsimp
  apply Bits.trans
  symm
  apply (Bits.minimize.spec _).left
  apply flip Bits.trans
  apply (Bits.minimize.spec _).left
  exact eq
def BitInt.exact : ∀{a b: Bits}, mk a = mk b -> a ≈ b := by
  intro a b eq
  apply Bits.trans
  apply (Bits.minimize.spec _).left
  apply flip Bits.trans
  symm
  apply (Bits.minimize.spec _).left
  rw [BitInt.ofBits.inj eq]
def BitInt.bits.spec (a: Bits) : (mk a).bits ≈ a := by
  symm
  apply (BitInt.Bits.minimize.spec _).left
def BitInt.liftWith {r: α -> α -> Prop} (eqv: Equivalence r) : (f: Bits -> α) -> (all_eq: ∀a b, a ≈ b -> r (f a) (f b)) -> BitInt -> α := fun f _ x => f x.bits
def BitInt.lift : (f: Bits -> α) -> (all_eq: ∀a b, a ≈ b -> f a = f b) -> BitInt -> α := liftWith ⟨Eq.refl,Eq.symm,Eq.trans⟩
def BitInt.liftProp : (f: Bits -> Prop) -> (all_eq: ∀a b, a ≈ b -> (f a ↔ f b)) -> BitInt -> Prop := liftWith ⟨Iff.refl,Iff.symm,Iff.trans⟩
def BitInt.liftWith₂ {r: α -> α -> Prop} (eqv: Equivalence r) : (f: Bits -> Bits -> α) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> r (f a b) (f c d)) -> BitInt -> BitInt -> α := fun f _ x y => f x.bits y.bits
def BitInt.lift₂ : (f: Bits -> Bits -> α) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> BitInt -> BitInt -> α := liftWith₂ ⟨Eq.refl,Eq.symm,Eq.trans⟩
def BitInt.liftProp₂ : (f: Bits -> Bits -> Prop) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> (f a b ↔ f c d)) -> BitInt -> BitInt -> Prop := liftWith₂ ⟨Iff.refl,Iff.symm,Iff.trans⟩
def BitInt.lift_mk : lift f all_eq (mk a) = f a := by
  apply all_eq
  apply bits.spec
def BitInt.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := by
  apply all_eq
  apply bits.spec
  apply bits.spec
def BitInt.liftProp_mk : liftProp f all_eq (mk a) ↔ f a := by
  apply all_eq
  apply bits.spec
def BitInt.liftProp₂_mk : liftProp₂ f all_eq (mk a) (mk b) ↔ f a b := by
  apply all_eq
  apply bits.spec
  apply bits.spec
def BitInt.ind { motive: BitInt -> Prop } : (mk: ∀x, motive (mk x)) -> ∀x, motive x := by
  intro h x
  have := h x.bits
  rw [sound' (mk x.bits)] at this
  exact this
  unfold mk
  dsimp
  symm
  apply (Bits.minimize.spec _).left

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

def BitInt.Bits.of_nat.rec_lemma (n: nat) : (n + 1) / 2 < n.succ := by
  rw [nat.div.eq_if]
  any_goals trivial
  cases (inferInstance : Decidable (n + 1 < 2)) with
  | isTrue h =>
    rw [if_pos h]
    apply nat.zero_lt_succ
  | isFalse h =>
    rw [if_neg h]
    rw [nat.add_one]
    apply nat.succ_lt_succ
    cases n with
    | zero => contradiction
    | succ n =>
      have : n + 1 + 1 = n + 2 := by
        rw [nat.add.assoc]
        rfl
      rw [←nat.add_one, this, nat.add_sub_inv]
      clear this h
      induction n using nat.wf.induction with
      | h n ih =>
      by_cases h:n < 2
      · rw [nat.div.eq_if, if_pos, nat.add_one]
        apply nat.zero_lt_succ
        assumption
        trivial
      · replace h := le_of_not_lt h
        have := ih (n - 2) (nat.sub.lt_nz _ _ rfl h)
        rw [nat.div.if_ge]
        rw [nat.add_one]
        apply nat.succ_lt_succ
        apply lt_of_lt_of_le this
        · cases n with
          | zero => contradiction
          | succ n =>
          cases n with
          | zero => contradiction
          | succ n =>
          apply le_of_lt
          have : n.succ.succ - 2 = n := rfl
          rw [this, nat.add_one]
          apply nat.lt_succ_self
        · trivial
        · assumption

@[reducible]
def BitInt.Bits.ofNat : Nat -> Bits
| 0 => .nil false
| n + 1 => .bit ((n + 1) % 2 == 1) (ofNat ((n + 1) / 2))
decreasing_by
  exact ofNat.rec_lemma

@[reducible]
def BitInt.Bits.of_nat : nat -> Bits
| .zero => .nil false
| .succ n => .bit ((n + 1) % 2 == 1) (of_nat ((n + 1) / 2))
termination_by n => n
decreasing_by
  exact of_nat.rec_lemma _

def BitInt.Bits.ofNat_eq_zero_iff (n: Nat) : n = 0 ↔ BitInt.Bits.ofNat n = .nil false := by
  apply Iff.intro
  · intro h
    subst h
    rfl
  · intro h
    cases n
    rfl
    contradiction

def BitInt.Bits.ofNat_ne_neg (n: Nat) : BitInt.Bits.ofNat n ≠ .nil true := by
  intro h
  cases n
  contradiction
  contradiction

def BitInt.Bits.ofNat.is_minimal (n: Nat) : (ofNat n).IsMinimal := by
  induction n using BitInt.Bits.ofNat.induct with
  | case1 => exact (.nil _)
  | case2 n ih =>
    unfold ofNat
    cases h:(n + 1) % 2
    apply ih.bit
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
    apply ih.bit
    apply ofNat_ne_neg
    have := @Nat.mod_lt (n + 1) 2 (by trivial)
    rw [h] at this
    have := Nat.lt_of_succ_lt_succ this
    have := Nat.lt_of_succ_lt_succ this
    exact (Nat.not_lt_zero _ this).elim

instance BitInt.OfNatInst : OfNat BitInt n := ⟨⟨.ofNat n,Bits.ofNat.is_minimal n⟩⟩
instance (priority := 900) BitInt.Bits.OfNatInst : OfNat BitInt.Bits n := ⟨.ofNat n⟩
instance BitInt.Bits.One : OfNat BitInt.Bits 1 := ⟨.bit true (.nil false)⟩
instance BitInt.Bits.Zero : OfNat BitInt.Bits 0 := ⟨.nil false⟩

def BitInt.mk_zero : 0 = mk 0 := rfl
def BitInt.mk_one : 1 = mk 1 := rfl

-- bit_maps and bit_zip_with are intentionally very simply to make it easy
-- to prove theorems about them

def BitInt.Bits.test_bit : nat -> Bits -> Bool
| _, .nil x => x
| .zero, .bit x _ => x
| .succ n, .bit _ xs => xs.test_bit n

def BitInt.Bits.test_bit_nil : ∀{x}, test_bit n (.nil x) = x := by intro; cases n <;> rfl
def BitInt.Bits.test_bit_bit_succ : ∀{x}{n:nat}, test_bit n.succ (.bit x xs) = test_bit n xs := by intros; rfl

def BitInt.test_bit (n: nat) : BitInt -> Bool := by
  apply lift (Bits.test_bit n) _
  intro a b eq
  induction eq generalizing n with
  | nil_nil => rfl
  | nil_bit _ _ _ ih =>
    cases n
    rfl
    unfold Bits.test_bit
    rw [←ih, Bits.test_bit_nil]
  | bit_nil _ _ _ ih =>
    cases n
    rfl
    unfold Bits.test_bit
    rw [ih, Bits.test_bit_nil]
  | bit_bit _ _ _ _ ih =>
    cases n
    rfl
    unfold Bits.test_bit
    apply ih

def BitInt.mk_test_bit (n: nat) : test_bit n (mk bs) = bs.test_bit n := lift_mk

@[ext]
def BitInt.ext (a b: BitInt) : (∀n, a.test_bit n = b.test_bit n) -> a = b := by
  intro h
  cases a with | ofBits a amin =>
  cases b with | ofBits b bmin =>
  apply sound'
  unfold test_bit lift liftWith bits at h
  dsimp at h
  dsimp
  induction amin generalizing b with
  | nil a =>
    induction bmin with
    | nil b =>
      cases h 0
      rfl
    | bit _ _ _ _ ih =>
      cases h 0
      apply Bits.nil_bit
      apply ih
      intro n
      conv => { rhs; rw [←@Bits.test_bit_bit_succ _ a] }
      rw [←h n.succ, Bits.test_bit_nil, Bits.test_bit_nil]
  | bit a _ _ _ ih =>
    cases bmin with
    | nil =>
      cases h 0
      apply Bits.bit_nil
      apply ih
      exact (.nil _)
      intro n
      conv => { lhs; rw [←@Bits.test_bit_bit_succ _ a] }
      rw [h n.succ, Bits.test_bit_nil, Bits.test_bit_nil]
    | bit =>
      cases h 0
      apply Bits.bit_bit
      apply ih
      assumption
      intro n
      apply h n.succ

def BitInt.Bits.bit_map (f: Bool -> Bool) : Bits -> Bits
| .nil x => .nil (f x)
| .bit b bs => .bit (f b) (bs.bit_map f)

def BitInt.Bits.bit_zip_with (f: Bool -> Bool -> Bool) : Bits -> Bits -> Bits
| .nil x, b => b.bit_map (f x)
| a, .nil x => a.bit_map (f · x)
| .bit a as, .bit b bs => .bit (f a b) (as.bit_zip_with f bs)

def BitInt.Bits.nil_bit_zip_with (f: Bool -> Bool -> Bool) :
  bit_zip_with f (.nil a) bs = bit_map (f a) bs := by cases bs <;> rfl
def BitInt.Bits.bit_zip_with_nil (f: Bool -> Bool -> Bool) :
  bit_zip_with f as (.nil b) = bit_map (f · b) as := by cases as <;> rfl

def BitInt.Bits.bit_map.spec (f: Bool -> Bool) (a b: Bits) : a ≈ b -> a.bit_map f ≈ b.bit_map f := by
  intro eq
  induction eq with
  | nil_nil => rfl
  | nil_bit =>
    apply nil_bit
    assumption
  | bit_nil =>
    apply bit_nil
    assumption
  | bit_bit _ _ _ _ ih =>
    apply bit_bit
    apply ih

def BitInt.bit_map (f: Bool -> Bool) : BitInt -> BitInt := by
  apply lift (fun _ => mk _) _
  exact BitInt.Bits.bit_map f
  intro a b aeq
  dsimp
  apply sound
  apply Bits.bit_map.spec
  assumption

def BitInt.mk_bit_map (f: Bool -> Bool) : bit_map f (mk bs) = mk (bs.bit_map f) := lift_mk

def BitInt.Bits.bit_zip_with.spec (f: Bool -> Bool -> Bool) (a b c d: Bits) : a ≈ c -> b ≈ d -> a.bit_zip_with f b ≈ c.bit_zip_with f d := by
  intro ac bd
  induction ac generalizing b d with
  | nil_nil a =>
    rw [nil_bit_zip_with, nil_bit_zip_with]
    apply bit_map.spec
    assumption
  | nil_bit a cs _ ih =>
    cases bd
    apply nil_bit
    apply flip trans
    apply bit_map.spec
    assumption
    rfl
    apply nil_bit
    apply flip trans
    apply ih
    assumption
    rfl
    apply bit_bit
    apply flip trans
    apply bit_map.spec
    assumption
    apply trans
    apply bit_map.spec
    assumption
    rfl
    apply bit_bit
    apply flip trans
    apply ih
    assumption
    rw [nil_bit_zip_with]
  | bit_nil _ _ _ ih =>
    rw [nil_bit_zip_with]
    cases bd
    apply bit_nil
    apply Bits.trans
    apply bit_map.spec
    assumption
    rfl
    apply bit_bit
    apply Bits.trans
    apply bit_map.spec
    assumption
    apply flip Bits.trans
    apply bit_map.spec
    assumption
    rfl
    apply bit_nil
    apply Bits.trans
    apply ih
    assumption
    rfl
    apply bit_bit
    apply Bits.trans
    apply ih
    assumption
    rw [nil_bit_zip_with]
  | bit_bit _ _ _ _ ih =>
    cases bd
    all_goals apply bit_bit
    apply bit_map.spec
    assumption
    any_goals (apply ih; assumption)
    apply flip Bits.trans
    apply ih; assumption
    rw [bit_zip_with_nil]
    apply Bits.trans
    apply ih; assumption
    rw [bit_zip_with_nil]

def BitInt.bit_zip_with (f: Bool -> Bool -> Bool) : BitInt -> BitInt -> BitInt := by
  apply lift₂ (fun _ _ => mk _) _
  exact BitInt.Bits.bit_zip_with f
  intro a b c d aeqc beqd
  dsimp
  apply sound
  apply Bits.bit_zip_with.spec
  assumption
  assumption

def BitInt.mk_bit_zip_with (f: Bool -> Bool -> Bool) : bit_zip_with f (mk as) (mk bs) = mk (as.bit_zip_with f bs) := lift₂_mk

def BitInt.Bits.bit_map_test_bit (f: Bool -> Bool) (n: nat) (a: Bits) : (a.bit_map f).test_bit n = f (a.test_bit n) := by
  induction n generalizing a with
  | zero => cases a <;> rfl
  | succ n ih =>
    cases a
    rfl
    unfold Bits.bit_map Bits.test_bit
    apply ih

def BitInt.bit_map_test_bit (f: Bool -> Bool) (n: nat) (a: BitInt) : (a.bit_map f).test_bit n = f (a.test_bit n) := by
  induction a using ind with | mk a =>
  rw [mk_bit_map, mk_test_bit, mk_test_bit]
  apply BitInt.Bits.bit_map_test_bit

def BitInt.Bits.bit_zip_with_test_bit (f: Bool -> Bool -> Bool) (n: nat) (a b: Bits) : (a.bit_zip_with f b).test_bit n = f (a.test_bit n) (b.test_bit n) := by
  induction n generalizing a b with
  | zero => cases a <;> cases b <;> rfl
  | succ n ih =>
    cases a <;> cases b
    rfl
    erw [bit_map_test_bit]
    rfl
    erw [bit_map_test_bit]
    rfl
    unfold bit_zip_with test_bit
    apply ih

def BitInt.bit_zip_with_test_bit (f: Bool -> Bool -> Bool) (n: nat) (a b: BitInt) : (a.bit_zip_with f b).test_bit n = f (a.test_bit n) (b.test_bit n) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_bit_zip_with, mk_test_bit, mk_test_bit, mk_test_bit]
  apply BitInt.Bits.bit_zip_with_test_bit

def BitInt.Bits.not : Bits -> Bits := bit_map Bool.not
def BitInt.not : BitInt -> BitInt := bit_map Bool.not

def BitInt.not_test_bit (n: nat) (a: BitInt) : a.not.test_bit n = !(a.test_bit n) := bit_map_test_bit _ n a

def BitInt.and : BitInt -> BitInt -> BitInt := bit_zip_with (· && ·)
def BitInt.or : BitInt -> BitInt -> BitInt := bit_zip_with (· || ·)
def BitInt.nand : BitInt -> BitInt -> BitInt := bit_zip_with (fun a b => !(a && b))
def BitInt.nor : BitInt -> BitInt -> BitInt := bit_zip_with (fun a b => !(a || b))
def BitInt.xor : BitInt -> BitInt -> BitInt := bit_zip_with Bool.xor
def BitInt.nxor : BitInt -> BitInt -> BitInt := bit_zip_with (· == ·)

instance : AndOp BitInt := ⟨BitInt.and⟩
instance : OrOp BitInt := ⟨BitInt.or⟩
instance : Xor BitInt := ⟨BitInt.xor⟩

def BitInt.and_test_bit (n: nat) (a b: BitInt) : (a &&& b).test_bit n = ((a.test_bit n) && (b.test_bit n)) := bit_zip_with_test_bit _ _ _ _
def BitInt.or_test_bit (n: nat) (a b: BitInt) : (a ||| b).test_bit n = ((a.test_bit n) || (b.test_bit n)) := bit_zip_with_test_bit _ _ _ _
def BitInt.xor_test_bit (n: nat) (a b: BitInt) : (a ^^^ b).test_bit n = ((a.test_bit n).xor (b.test_bit n)) := bit_zip_with_test_bit _ _ _ _

def BitInt.Bits.succ: Bits -> Bits
| .nil false => .bit true (.nil false)
| .nil true => .nil false
| .bit false as => .bit true as
| .bit true as => .bit false as.succ

def BitInt.Bits.pred: Bits -> Bits
| .nil false => .nil true
| .nil true => .bit false (.nil true)
| .bit false as => .bit true as.pred
| .bit true as => .bit false as

-- def BitInt.Bits.neg : Bits -> Bits := BitInt.Bits.succ ∘ bit_map Bool.not
def BitInt.Bits.neg : Bits -> Bits
| .nil false => .nil false
| .nil true => .bit true (.nil false)
| .bit true (.nil false) => .nil true
| .bit false bs => .bit false bs.neg
| .bit true bs => .bit true bs.not

-- def BitInt.Bits.neg : Bits -> Bits := BitInt.Bits.succ ∘ bit_map Bool.not
def BitInt.Bits.neg_naive : Bits -> Bits
| .nil false => .nil false
| .nil true => .bit true (.nil false)
| .bit false bs => .bit false bs.neg_naive
| .bit true bs => .bit true bs.not

def BitInt.Bits.neg_eq_neg_naive (a: Bits): a.neg ≈ a.neg_naive := by
  induction a with
  | nil a => revert a; decide
  | bit a as ih =>
    unfold neg neg_naive
    cases a
    dsimp
    apply bit_bit
    exact ih
    cases as with
    | nil a =>
      revert a
      decide
    | bit a' as => rfl

instance : Neg BitInt.Bits := ⟨.neg⟩

def BitInt.Bits.pred_succ {a: Bits} : a.pred.succ ≈ a := by
  induction a with
  | nil a => revert a; decide
  | bit a as ih =>
    cases a <;> (apply bit_bit)
    assumption
    rfl

def BitInt.Bits.succ_pred {a: Bits} : a.succ.pred ≈ a := by
  induction a with
  | nil a => revert a; decide
  | bit a as ih =>
    cases a <;> (apply bit_bit)
    rfl
    assumption

def BitInt.Bits.succ.spec {a b: Bits} : a ≈ b ↔ a.succ ≈ b.succ := by
  induction a generalizing b with
  | nil a =>
      induction b with
      | nil b => revert a b; decide
      | bit b bs ih =>
        apply Iff.intro
        intro h
        cases h
        cases a
        apply bit_bit
        assumption
        apply nil_bit
        apply ih.mp
        assumption
        intro h
        cases a <;> cases b <;> rw [succ, succ] at h
        all_goals cases h
        apply nil_bit
        assumption
        apply nil_bit
        apply ih.mpr
        assumption
  | bit a as ih =>
    cases b with
    | nil b =>
        apply Iff.intro
        intro h
        cases h
        cases a
        apply bit_bit
        assumption
        apply bit_nil
        apply Bits.trans
        apply ih.mp
        assumption
        rfl
        intro h
        cases a <;> cases b <;> rw [succ, succ] at h
        all_goals cases h <;> rename_i h
        apply bit_nil
        assumption
        apply bit_nil
        clear ih
        induction as with
        | nil a =>
          cases a <;> cases h
          rfl
        | bit a as ih =>
          cases a <;> cases h
          apply bit_nil
          apply ih
          assumption
    | bit b bs =>
      apply Iff.intro
      intro h
      cases h
      cases a
      apply bit_bit
      assumption
      apply bit_bit
      apply ih.mp
      assumption
      intro h
      cases a <;> cases b <;> cases h
      apply bit_bit
      assumption
      apply bit_bit
      apply ih.mpr
      assumption

def BitInt.Bits.pred.spec {a b: Bits} : a ≈ b ↔ a.pred ≈ b.pred := by
  apply flip Iff.trans
  symm
  apply succ.spec
  apply Iff.intro
  intro h
  apply Bits.trans
  apply pred_succ
  apply flip Bits.trans
  symm
  apply pred_succ
  exact h
  intro h
  apply Bits.trans
  symm
  apply pred_succ
  apply flip Bits.trans
  apply pred_succ
  assumption

def BitInt.Bits.neg_eq_not_succ (a: BitInt.Bits) : -a ≈ a.not.succ := by
  apply trans
  apply neg_eq_neg_naive
  induction a with
  | nil a => revert a; decide
  | bit a as ih =>
    cases a
    apply bit_bit
    assumption
    apply bit_bit
    apply bit_map.spec
    rfl

def BitInt.Bits.not_not (a: BitInt.Bits) : a.not.not = a := by
  induction a with
  | nil a => revert a; decide
  | bit a as ih => rw [not, bit_map, bit_map, ←not, ih, Bool.not, Bool.not_not]

def BitInt.Bits.not.spec {a b: Bits} : a ≈ b ↔ a.not ≈ b.not := by
  apply Iff.intro
  apply bit_map.spec
  intro eq
  rw [←not_not a, ←not_not b]
  apply bit_map.spec
  assumption

def BitInt.Bits.neg_neg₀ (a: BitInt.Bits) : a.neg_naive.neg_naive ≈ a := by
  induction a with
  | nil a => revert a; decide
  | bit a as ih =>
    cases a <;> apply bit_bit
    assumption
    rw [not_not]

def BitInt.Bits.neg.spec {a b: Bits} : a ≈ b ↔ -a ≈ -b := by
  revert a b
  suffices ∀a b: Bits, a ≈ b -> a.neg_naive ≈ b.neg_naive by
    intro  a b
    apply Iff.intro
    intro h
    apply trans
    apply neg_eq_neg_naive
    apply flip trans
    symm
    apply neg_eq_neg_naive
    apply this
    assumption
    intro h
    apply Bits.trans
    symm
    apply neg_neg₀
    apply flip Bits.trans
    apply neg_neg₀
    apply this
    apply trans
    symm
    apply neg_eq_neg_naive
    apply flip trans
    apply neg_eq_neg_naive
    assumption
  intro a b h
  induction h with
  | nil_nil => rfl
  | nil_bit a as eq ih =>
    cases a
    apply nil_bit
    assumption
    apply bit_bit
    apply succ.spec.mpr
    apply trans ih
    apply trans _ (neg_eq_not_succ as)
    symm
    apply neg_eq_neg_naive
  | bit_nil a as eq ih =>
    cases a
    apply bit_nil
    assumption
    apply bit_bit
    apply Bits.trans
    apply not.spec.mp
    assumption
    rfl
  | bit_bit a as bs eq ih =>
    cases a <;> (apply bit_bit)
    assumption
    apply not.spec.mp
    assumption

def BitInt.Bits.neg_neg (a: BitInt.Bits) : - -a ≈ a := by
  apply trans
  apply neg.spec.mp
  apply neg_eq_neg_naive
  apply trans
  apply neg_eq_neg_naive
  apply neg_neg₀

def BitInt.Bits.succ_eq_not_neg (a: BitInt.Bits) : a.succ ≈ a.not.neg := by
  apply flip trans
  symm
  apply neg_eq_neg_naive
  induction a with
  | nil a => revert a; decide
  | bit a as ih =>
    cases a
    apply bit_bit
    rw [←not, not_not]
    apply bit_bit
    assumption

def BitInt.Bits.pred_eq_neg_not (a: BitInt.Bits) : a.pred ≈ a.neg.not := by
  apply succ.spec.mpr
  apply Bits.trans
  apply pred_succ
  apply flip Bits.trans
  apply neg_eq_not_succ
  symm
  apply neg_neg

def BitInt.Bits.pred_eq_neg_succ_neg (a: BitInt.Bits) : a.pred ≈ a.neg.succ.neg := by
  apply Bits.trans
  apply pred_eq_neg_not
  apply flip Bits.trans
  apply neg.spec.mp
  symm
  apply succ_eq_not_neg
  apply flip Bits.trans
  symm
  apply neg_neg
  rfl

def BitInt.Bits.nil_cmp (a: Bool) : Bits -> Ordering
| .nil b => compare b a
| .bit b bs => (nil_cmp a bs).then (compare a b)

def BitInt.neg : BitInt -> BitInt := by
  apply lift (mk ∘ Bits.neg)
  intro a b eq
  apply sound
  apply Bits.neg.spec.mp
  assumption

def BitInt.succ : BitInt -> BitInt := by
  apply lift (mk ∘ Bits.succ)
  intro a b eq
  apply sound
  apply Bits.succ.spec.mp
  assumption

def BitInt.pred : BitInt -> BitInt := by
  apply lift (mk ∘ Bits.pred)
  intro a b eq
  apply sound
  apply Bits.pred.spec.mp
  assumption

instance : Neg BitInt := ⟨.neg⟩
def BitInt.mk_neg_one : -1 = mk (-1) := rfl

def BitInt.mk_neg (a: Bits) : -(mk a) = mk (-a) := by
  unfold Neg.neg instNegBitInt instNegBits
  dsimp
  apply lift_mk
def BitInt.mk_not (a: Bits) : (mk a).not = mk a.not := by
  unfold not
  apply lift_mk
def BitInt.mk_succ (a: Bits) : (mk a).succ = mk a.succ := lift_mk
def BitInt.mk_pred (a: Bits) : (mk a).pred = mk a.pred := lift_mk

def BitInt.pred_succ (a: BitInt) : a.pred.succ = a := by
  induction a using ind with | mk a =>
  rw [mk_pred, mk_succ]
  apply sound
  apply Bits.pred_succ

def BitInt.succ_pred (a: BitInt) : a.succ.pred = a := by
  induction a using ind with | mk a =>
  rw [mk_succ, mk_pred]
  apply sound
  apply Bits.succ_pred

def BitInt.neg_eq_not_succ (a: BitInt) : -a = a.not.succ := by
  induction a using ind with | mk a =>
  rw [mk_neg, mk_not, mk_succ]
  apply sound
  apply Bits.neg_eq_not_succ

def BitInt.not_not (a: BitInt) : a.not.not = a := by
  induction a using ind with | mk a =>
  rw [mk_not, mk_not]
  apply sound
  rw [Bits.not_not]

def BitInt.neg_neg (a: BitInt) : - -a = a := by
  induction a using ind with | mk a =>
  rw [mk_neg, mk_neg]
  apply sound
  apply Bits.neg_neg

def BitInt.succ_eq_not_neg (a: BitInt) : a.succ = -a.not := by
  induction a using ind with | mk a =>
  rw [mk_succ, mk_not, mk_neg]
  apply sound
  apply Bits.succ_eq_not_neg

def BitInt.pred_eq_neg_not (a: BitInt) : a.pred = (-a).not := by
  induction a using ind with | mk a =>
  rw [mk_pred, mk_neg, mk_not]
  apply sound
  apply Bits.pred_eq_neg_not

def BitInt.pred_eq_neg_succ_neg (a: BitInt) : a.pred = -(-a).succ := by
  induction a using ind with | mk a =>
  rw [mk_pred, mk_neg, mk_succ, mk_neg]
  apply sound
  apply Bits.pred_eq_neg_succ_neg

def BitInt.succ.inj (a b: BitInt) : a.succ = b.succ -> a = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_succ, mk_succ]
  intro h
  apply sound
  apply Bits.succ.spec.mpr
  apply exact
  assumption

def BitInt.pred.inj (a b: BitInt) : a.pred = b.pred -> a = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_pred, mk_pred]
  intro h
  apply sound
  apply Bits.pred.spec.mpr
  apply exact
  assumption

def BitInt.neg.inj (a b: BitInt) : -a = -b -> a = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_neg, mk_neg]
  intro h
  apply sound
  apply Bits.neg.spec.mpr
  apply exact
  assumption

def BitInt.not.inj (a b: BitInt) : a.not = b.not -> a = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_not, mk_not]
  intro h
  apply sound
  apply Bits.not.spec.mpr
  apply exact
  assumption

def bit_add_carry : Bool -> Bool -> Bool -> Bool × Bool
| false, false, x
| false, x, false
| x, false, false => ⟨false,x⟩
| true, true, x
| true, x, true
| x, true, true => ⟨true,x⟩

def BitInt.Bits.nil_add (a: Bits) : Bool -> Bool -> Bits
| false, false => a
| false, true => a.succ
| true, false => a.pred
| true, true => a

def BitInt.Bits.add_with_carry : Bits -> Bits -> Bool -> Bits
| nil a, b, carry => b.nil_add a carry
| a, nil b, carry => a.nil_add b carry
| bit a as, bit b bs, c =>
  have (carry, sum) := bit_add_carry a b c
  bit sum (add_with_carry as bs carry)

def BitInt.Bits.add : Bits -> Bits -> Bits := (add_with_carry · · false)

instance : Add BitInt.Bits := ⟨.add⟩

def BitInt.Bits.add.def (a b: Bits) : a + b = a.add b := rfl

def BitInt.Bits.add_with_carry.eq_add_if (a b c) : add_with_carry a b c ≈ if c then (a + b).succ else a + b := by
  cases c
  rfl
  rw [if_pos rfl]
  suffices add_with_carry a b true ≈ (add_with_carry a b false).succ from this
  induction a generalizing b with
  | nil a =>
    cases b with
    | nil b => revert a b; decide
    | bit b bs =>
      cases a <;> cases b <;>
      unfold add_with_carry
      apply succ.spec.mp
      rfl
      apply succ.spec.mp
      rfl
      symm
      apply pred_succ
      symm
      apply pred_succ
  | bit a as ih =>
    cases b with
    | nil b =>
      cases a <;> cases b <;>
      unfold add_with_carry
      apply succ.spec.mp
      rfl
      symm
      apply pred_succ
      apply succ.spec.mp
      rfl
      symm
      apply pred_succ
    | bit b bs =>
      unfold add_with_carry
      cases a <;> cases b <;> unfold bit_add_carry <;> dsimp
      rfl
      apply bit_bit
      apply ih
      apply bit_bit
      apply ih
      apply bit_bit
      rfl

def BitInt.Bits.add_with_carry.nil_left :
  add_with_carry (nil a) b c = nil_add b a c := by cases b <;> rfl
def BitInt.Bits.add_with_carry.nil_right :
  add_with_carry a (nil b) c = nil_add a b c := by
    cases a
    rename_i a
    revert a b c; decide
    rfl

def BitInt.Bits.add_with_carry.spec (a b c d: Bits) (carry: Bool) :
  a ≈ c ->
  b ≈ d ->
  add_with_carry a b carry ≈ add_with_carry c d carry := by
  intro ac bd
  induction ac generalizing b d carry with
  | nil_nil a =>
    rw [nil_left, nil_left]
    cases a <;> cases carry <;> unfold nil_add <;> dsimp
    assumption
    apply succ.spec.mp
    assumption
    apply pred.spec.mp
    assumption
    assumption
  | nil_bit a as ac ih =>
    rw [nil_left]
    cases bd with
    | nil_nil b =>
      cases a <;> cases b <;> cases carry
      all_goals
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply nil_bit
        try assumption
      all_goals
        apply flip trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        assumption
        rfl
    | nil_bit b bs bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        try apply nil_bit
        try apply bit_bit
        apply flip trans
        apply ih
        assumption
        rfl
    | bit_nil b bs bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        apply bit_bit
        apply trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply bd
        apply flip trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply ac
        rfl
    | bit_bit b bs ds bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        apply bit_bit
        apply trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply bd
        apply flip trans
        apply ih
        rfl
        rw [nil_left]
        rfl
  | bit_nil a as ac ih =>
    cases bd with
    | nil_nil b =>
      cases a <;> cases b <;> cases carry
      all_goals
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply bit_nil
        try assumption
      all_goals
        apply trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        assumption
        rfl
    | nil_bit b bs bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply bit_bit
        apply trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply ac
        apply flip trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply bd
        rfl
    | bit_nil b bs bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        try apply bit_nil
        try apply bit_bit
        apply trans
        apply ih
        assumption
        rfl
    | bit_bit b bs ds bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        apply bit_bit
        apply flip trans
        try apply succ.spec.mp
        try apply pred.spec.mp
        apply bd
        apply trans
        apply ih
        rfl
        rw [nil_left]
        rfl
  | bit_bit a as cs ac ih =>
    cases bd with
    | nil_nil b =>
      cases a <;> cases b <;> cases carry
      all_goals
        apply bit_bit
        try apply succ.spec.mp
        try apply pred.spec.mp
        assumption
    | nil_bit b bs bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        apply bit_bit
        apply flip trans
        apply ih
        assumption
        rw [nil_right]
        rfl
    | bit_nil b bs bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        apply bit_bit
        apply trans
        apply ih
        assumption
        rw [nil_right]
        rfl
    | bit_bit b bs ds bd =>
      cases a <;> cases b <;> cases carry
      all_goals
        apply bit_bit
        apply trans
        apply ih
        assumption
        rfl

def BitInt.Bits.add.spec (a b c d: Bits) :
  a ≈ c ->
  b ≈ d ->
  a + b ≈ c + d := by
  apply add_with_carry.spec

def BitInt.Bits.add.spec_left (k a b: Bits) :
  a ≈ b ->
  a + k ≈ b + k := by
  intro ac
  apply add_with_carry.spec
  assumption
  rfl

def BitInt.Bits.add.spec_right (k a b: Bits) :
  a ≈ b ->
  k + a ≈ k + b := by
  apply add_with_carry.spec
  rfl

def BitInt.Bits.add_zero_iff {a b: Bits} : b ≈ 0 ↔ a + b ≈ a := by
  rw [add.def]
  induction a generalizing b with
  | nil a =>
    induction b with
    | nil b => revert a b; decide
    | bit b bs ih =>
      apply Iff.intro
      intro h
      cases h
      cases a <;> unfold add add_with_carry
      apply bit_nil
      assumption
      apply bit_nil
      apply succ.spec.mpr
      apply Bits.trans
      apply pred_succ
      assumption
      cases a <;> unfold add add_with_carry
      intro h
      cases h
      apply bit_nil
      assumption
      intro h
      cases b <;> cases h
      apply bit_nil
      apply pred.spec.mpr
      assumption
  | bit a as ih =>
    cases b with
    | nil b =>
      apply Iff.intro
      intro h
      cases h
      rfl
      cases b <;> unfold add add_with_carry nil_add <;> dsimp
      intros
      rfl
      intro h
      apply False.elim
      cases a <;> unfold pred at h
      contradiction
      contradiction
    | bit b bs =>
      apply Iff.intro
      intro h
      cases h
      unfold add add_with_carry bit_add_carry
      cases a <;> dsimp
      apply bit_bit
      apply ih.mp
      assumption
      apply bit_bit
      apply ih.mp
      assumption
      unfold add add_with_carry bit_add_carry
      cases a <;> cases b <;> dsimp <;> intro h
      all_goals cases h
      all_goals apply bit_nil
      apply ih.mpr
      assumption
      apply ih.mpr
      assumption

def BitInt.Bits.zero_add_iff {a b: Bits} : a ≈ 0 ↔ a + b ≈ b := by
  rw [add.def]
  induction b generalizing a with
  | nil b =>
    induction a with
    | nil a => revert a b; decide
    | bit a as ih =>
      apply Iff.intro
      intro h
      cases h
      cases b
      apply bit_nil
      assumption
      apply bit_nil
      apply succ.spec.mpr
      apply Bits.trans
      apply pred_succ
      assumption
      cases b
      intro h
      cases h
      apply bit_nil
      assumption
      intro h
      cases a <;> cases h
      apply bit_nil
      apply pred.spec.mpr
      assumption
  | bit b bs ih =>
    cases a with
    | nil a =>
      apply Iff.intro
      intro h
      cases h
      rfl
      intro h
      cases a <;> cases b
      all_goals cases h
      rfl
      rfl
    | bit a as =>
      apply Iff.intro
      intro h
      cases h
      cases b
      apply bit_bit
      apply ih.mp
      assumption
      apply bit_bit
      apply ih.mp
      assumption
      cases a <;> cases b <;> intro h
      all_goals cases h
      all_goals apply bit_nil
      apply ih.mpr
      assumption
      apply ih.mpr
      assumption

def BitInt.Bits.add_neg_one_iff {a b: Bits} : b ≈ -1 ↔ a + b ≈ a.pred := by
  rw [add.def]
  induction a generalizing b with
  | nil a =>
    induction b with
    | nil b => revert a b; decide
    | bit b bs ih =>
      apply Iff.intro
      intro h
      cases h
      cases a <;> unfold add add_with_carry
      apply bit_nil
      assumption
      apply bit_bit
      assumption
      intro h
      cases a <;> cases b <;> cases h
      apply bit_nil
      assumption
      apply bit_nil
      assumption
  | bit a as ih =>
    cases b with
    | nil b =>
      apply Iff.intro
      intro h
      cases h
      rfl
      intro h
      cases a <;> cases b
      all_goals cases h
      rfl
      rfl
    | bit b bs =>
      apply Iff.intro
      intro h
      cases h
      unfold add add_with_carry bit_add_carry
      cases a <;> dsimp
      apply bit_bit
      apply ih.mp
      assumption
      apply bit_bit
      apply trans
      apply add_with_carry.spec
      rfl
      assumption
      rw [add_with_carry.nil_right]
      rfl
      intro h
      unfold add add_with_carry bit_add_carry at h
      cases a <;> cases b <;> dsimp at h
      all_goals cases h
      apply bit_nil
      apply ih.mpr
      assumption
      apply bit_nil
      apply ih.mpr
      rename_i h
      apply flip trans
      apply pred.spec.mp
      apply h
      apply flip trans
      apply pred.spec.mp
      symm
      apply add_with_carry.eq_add_if
      rw [if_pos rfl]
      symm
      apply succ_pred

def BitInt.Bits.neg_one_add_iff {a b: Bits} : a ≈ -1 ↔ a + b ≈ b.pred := by
  rw [add.def]
  induction b generalizing a with
  | nil b =>
    induction a with
    | nil a => revert a b; decide
    | bit a as ih =>
      apply Iff.intro
      intro h
      cases h
      cases b <;> unfold add add_with_carry
      apply bit_nil
      assumption
      unfold nil_add; dsimp
      apply pred.spec.mp
      apply bit_nil
      assumption
      intro h
      unfold add add_with_carry at h
      cases b <;> (unfold nil_add at h; dsimp at h)
      cases h
      apply bit_nil
      assumption
      apply pred.spec.mpr
      assumption
  | bit b bs ih =>
    cases a with
    | nil a =>
      apply Iff.intro
      intro h
      cases h
      rfl
      unfold add add_with_carry nil_add
      cases a <;> dsimp
      intro h
      cases b <;> nomatch h
      intro
      rfl
    | bit a as =>
      apply Iff.intro
      intro h
      cases h
      unfold add add_with_carry bit_add_carry
      cases b <;> dsimp
      apply bit_bit
      apply ih.mp
      assumption
      apply bit_bit
      apply trans
      apply add_with_carry.spec
      assumption
      rfl
      rw [add_with_carry.nil_left]; rfl
      intro h
      cases a <;> cases b <;> cases h
      all_goals
        apply bit_nil
        rename_i h
        apply ih.mpr
      assumption
      apply flip trans
      apply pred.spec.mp
      assumption
      apply flip trans
      apply pred.spec.mp
      symm
      apply add_with_carry.eq_add_if
      rw [if_pos rfl]
      apply flip trans
      symm
      apply succ_pred
      rfl

def BitInt.Bits.add_succ (a b: Bits) : a + b.succ ≈ (a + b).succ := by
  rw [add.def, add.def]
  induction a generalizing b with
  | nil a =>
    cases b with
    | nil b => revert a b; decide
    | bit b bs =>
      unfold add add_with_carry
      cases a <;> cases b
      any_goals rfl
      any_goals (rw [succ]; dsimp)
      apply flip Bits.trans
      symm
      apply Bits.pred_succ
      rfl
      apply flip Bits.trans
      symm
      apply Bits.pred_succ
      apply bit_bit
      apply succ_pred
  | bit a as ih =>
    cases b with
    | nil b =>
      cases a <;> cases b
      all_goals apply bit_bit
      any_goals rw [add_with_carry.nil_right]
      any_goals rfl
      symm
      apply pred_succ
    | bit b bs =>
      cases a <;> cases b
      all_goals apply bit_bit
      rfl
      apply ih
      apply add_with_carry.eq_add_if
      apply Bits.trans
      apply ih
      symm
      apply add_with_carry.eq_add_if

def BitInt.Bits.succ_add (a b: Bits) : a.succ + b ≈ (a + b).succ := by
  rw [add.def, add.def]
  induction a generalizing b with
  | nil a =>
    cases b with
    | nil b => revert a b; decide
    | bit b bs =>
      cases a <;> cases b
      all_goals apply bit_bit
      any_goals rw [add_with_carry.nil_left]
      any_goals rfl
      symm
      apply pred_succ
  | bit a as ih =>
    cases b with
    | nil b =>
      cases a <;> cases b
      all_goals apply bit_bit
      any_goals rfl
      symm
      apply pred_succ
      apply succ_pred
    | bit b bs =>
      cases a <;> cases b
      all_goals apply bit_bit
      any_goals rfl
      apply add_with_carry.eq_add_if
      apply ih
      apply flip trans
      symm
      apply add_with_carry.eq_add_if
      apply ih

def BitInt.Bits.add_pred (a b: Bits) : a + b.pred ≈ (a + b).pred := by
  apply succ.spec.mpr
  apply trans
  symm
  apply add_succ
  apply trans
  apply add.spec
  rfl
  apply pred_succ
  symm
  apply pred_succ

def BitInt.Bits.pred_add (a b: Bits) : a.pred + b ≈ (a + b).pred := by
  apply succ.spec.mpr
  apply trans
  symm
  apply succ_add
  apply trans
  apply add.spec
  apply pred_succ
  rfl
  symm
  apply pred_succ

def BitInt.add : BitInt -> BitInt -> BitInt := by
  apply lift₂ (fun _ _ => mk _) _
  exact Bits.add
  intros
  apply sound
  apply Bits.add.spec
  assumption
  assumption

instance : Add BitInt := ⟨.add⟩

def BitInt.mk_add (a b: Bits) : mk a + mk b = mk (a + b) := by
  unfold HAdd.hAdd instHAdd Add.add
  apply lift₂_mk

def BitInt.add.add_zero_iff (a b: BitInt) : b = 0 ↔ a + b = a := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply Iff.intro
  intro h
  rw [mk_add]
  apply sound
  apply BitInt.Bits.add_zero_iff.mp
  apply exact
  assumption
  rw [mk_add]
  intro h
  rw [mk_zero]
  apply sound
  apply BitInt.Bits.add_zero_iff.mpr
  apply exact
  assumption

def BitInt.add.zero_add_iff (a b: BitInt) : a = 0 ↔ a + b = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply Iff.intro
  intro h
  rw [mk_add]
  apply sound
  apply BitInt.Bits.zero_add_iff.mp
  apply exact
  assumption
  rw [mk_add]
  intro h
  rw [mk_zero]
  apply sound
  apply BitInt.Bits.zero_add_iff.mpr
  apply exact
  assumption

def BitInt.add.add_zero (a: BitInt) : a + 0 = a := by
  apply (add_zero_iff _ _).mp
  rfl

def BitInt.add.zero_add (a: BitInt) : 0 + a = a := by
  apply (zero_add_iff _ _).mp
  rfl

def BitInt.add.add_succ (a b: BitInt) : a + b.succ = (a + b).succ := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_succ, mk_add, mk_add, mk_succ]
  apply sound
  exact Bits.add_succ a b

def BitInt.add.succ_add (a b: BitInt) : a.succ + b = (a + b).succ := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_succ, mk_add, mk_add, mk_succ]
  apply sound
  exact Bits.succ_add a b

def BitInt.add.add_pred (a b: BitInt) : a + b.pred = (a + b).pred := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_pred, mk_add, mk_add, mk_pred]
  apply sound
  exact Bits.add_pred a b

def BitInt.add.pred_add (a b: BitInt) : a.pred + b = (a + b).pred := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_pred, mk_add, mk_add, mk_pred]
  apply sound
  exact Bits.pred_add a b

inductive BitInt.Bits.IsNegative : Bits -> Prop where
| nil : IsNegative (nil true)
| bit a as : IsNegative as -> IsNegative (bit a as)
inductive BitInt.Bits.IsPositive : Bits -> Prop where
| nil : IsPositive (nil false)
| bit a as : IsPositive as -> IsPositive (bit a as)

instance BitInt.Bits.decIsNegative : ∀(a: Bits), Decidable (IsNegative a)
| .nil false => .isFalse (nomatch ·)
| .nil true => .isTrue .nil
| .bit a as =>
  match decIsNegative as with
  | .isTrue h => .isTrue (.bit _ _ h)
  | .isFalse h => .isFalse fun g => by cases g; contradiction

instance BitInt.Bits.decIsPositive : ∀(a: Bits), Decidable (IsPositive a)
| .nil false => .isTrue .nil
| .nil true => .isFalse (nomatch ·)
| .bit a as =>
  match decIsPositive as with
  | .isTrue h => .isTrue (.bit _ _ h)
  | .isFalse h => .isFalse fun g => by cases g; contradiction

instance BitInt.Bits.pos_or_neg : ∀(a: Bits), a.IsPositive ∨ a.IsNegative
| .nil false => .inl .nil
| .nil true => .inr .nil
| .bit _ as =>
  match pos_or_neg as with
  | .inl h => .inl (.bit _ _ h)
  | .inr h => .inr (.bit _ _ h)

instance BitInt.Bits.not_pos_and_neg : ∀(a: Bits), a.IsPositive -> a.IsNegative -> False
| .bit _ as, .bit _ _ pos, .bit _ _ neg => not_pos_and_neg as pos neg

def BitInt.Bits.neg_iff_not_pos (a: Bits) : a.IsNegative ↔ ¬a.IsPositive := by
  by_cases neg:a.IsNegative <;> by_cases pos:a.IsPositive
  exfalso
  apply not_pos_and_neg <;> assumption
  apply Iff.intro (fun _ => pos) (fun _ => neg)
  apply Iff.intro (fun _ => by contradiction) (fun _ => by contradiction)
  cases a.pos_or_neg <;> contradiction

def BitInt.Bits.pos_iff_not_neg (a: Bits) : a.IsPositive ↔ ¬a.IsNegative := by
  by_cases neg:a.IsNegative <;> by_cases pos:a.IsPositive
  exfalso
  apply not_pos_and_neg <;> assumption
  apply Iff.intro (fun _ => by contradiction) (fun _ => by contradiction)
  apply Iff.intro (fun _ => neg) (fun _ => pos)
  cases a.pos_or_neg <;> contradiction

def BitInt.Bits.not_neg_eq_pos (a: Bits) :
  a.IsNegative ->
  a.not.IsPositive := by
  intro neg
  induction neg with
  | nil => trivial
  | bit a as _ ih =>
    apply IsPositive.bit
    assumption

def BitInt.Bits.not_pos_eq_neg (a: Bits) :
  a.IsPositive ->
  a.not.IsNegative := by
  intro neg
  induction neg with
  | nil => trivial
  | bit a as _ ih =>
    apply IsNegative.bit
    assumption

def BitInt.Bits.IsPositive.eqv (a b: Bits) :
  a ≈ b ->
  a.IsPositive ->
  b.IsPositive := by
  intro eq pos
  induction eq with
  | nil_nil => assumption
  | nil_bit _ _ _ ih  =>
    apply IsPositive.bit
    apply ih
    assumption
  | bit_nil _ _ _ ih =>
    cases pos
    apply ih
    assumption
  | bit_bit _ _ _ _ ih =>
    apply IsPositive.bit
    apply ih
    cases pos
    assumption

def BitInt.Bits.neg_neg_eq_pos (a: Bits) :
  a.IsNegative ->
  (-a).IsPositive := by
  intro neg
  induction neg with
  | nil => trivial
  | bit a as ih =>
    cases a
    apply IsPositive.bit
    assumption
    apply IsPositive.eqv
    symm
    apply neg_eq_neg_naive
    apply IsPositive.bit
    apply not_neg_eq_pos
    assumption

def BitInt.Bits.pos_eqv_ofNat (a: Bits) :
  a.IsPositive ->
  ∃a': Nat, a ≈ ofNat a' := by
  intro pos
  induction pos with
  | nil => exists 0
  | bit a as _ ih =>
    obtain ⟨a',prf⟩ := ih
    exists a' * 2 + if a then 1 else 0
    cases a
    any_goals rw [if_pos rfl]
    any_goals rw [if_neg Bool.noConfusion]
    all_goals unfold ofNat
    cases a'
    dsimp
    apply bit_nil
    assumption
    rw [Nat.succ_mul]
    dsimp
    rw [Nat.add_assoc, Nat.add_mod, Nat.mul_mod]
    apply bit_bit
    rw [Nat.mul_comm, Nat.mul_add_div, Nat.div_self]
    repeat trivial
    rw [Nat.add_mod, Nat.mul_mod_left]
    apply bit_bit
    rw [Nat.mul_comm, Nat.mul_add_div, Nat.div_eq_of_lt]
    repeat trivial

def BitInt.Bits.neg_eqv_ofNat (a: Bits) :
  a.IsNegative ->
  ∃a': Nat, a ≈ -ofNat a' := by
  intro neg
  obtain ⟨ a', prf ⟩ := pos_eqv_ofNat _ (neg_neg_eq_pos _ neg)
  exists a'
  apply flip trans
  apply Bits.neg.spec.mp
  assumption
  symm
  apply neg_neg

def BitInt.Bits.pos_eqv_of_nat (a: Bits) :
  a.IsPositive ->
  ∃a': nat, a ≈ of_nat a' := by
  intro pos
  induction pos with
  | nil => exists 0
  | bit a as _ ih =>
    obtain ⟨a',prf⟩ := ih
    exists 2 * a' + if a then 1 else 0
    cases a
    any_goals rw [if_pos rfl]
    any_goals rw [if_neg Bool.noConfusion]
    all_goals unfold of_nat
    cases a'
    rw [nat.zero_eq, nat.mul_zero, nat.add_zero, ←nat.zero_eq]
    dsimp
    apply bit_nil
    assumption
    rename_i n
    have : 2 * n.succ = 1 + 1 + 2 * n := by
      rw [nat.mul_succ]
      rfl
    rw [this, nat.add_zero, nat.one_add, nat.succ_add]
    dsimp
    have : (1: nat) + 1 = 2 := rfl
    rw [nat.add.comm 1, nat.add.assoc, nat.mod.add,
      nat.mod.mul, nat.mod.self, nat.zero_mul, nat.zero_mod, nat.zero_add,
      this, nat.mod.self]
    apply bit_bit
    rw [nat.div.mul_add, nat.div.self, nat.add_one]
    exact prf
    rfl
    rfl
    rw [nat.add_one]
    dsimp
    rw [nat.mod.add, nat.mod.mul, nat.mod.self, nat.zero_mul, nat.zero_mod, nat.zero_add]
    apply bit_bit
    rw [nat.div.mul_add, nat.div.if_lt, nat.add_zero]
    assumption
    repeat rfl

def BitInt.Bits.neg_eqv_of_nat (a: Bits) :
  a.IsNegative ->
  ∃a': nat, a ≈ -of_nat a' := by
  intro neg
  obtain ⟨ a', prf ⟩ := pos_eqv_of_nat _ (neg_neg_eq_pos _ neg)
  exists a'
  apply flip trans
  apply Bits.neg.spec.mp
  assumption
  symm
  apply neg_neg

def BitInt.Bits.eqv_ofNat_or_negOfNat (a: Bits) :
  ∃a': nat, a ≈ of_nat a' ∨ a ≈ -of_nat a' := by
  by_cases h:a.IsNegative
  obtain ⟨a',h⟩ := neg_eqv_of_nat _ h
  exists a'
  exact .inr h
  obtain ⟨a',h⟩ := pos_eqv_of_nat _ ((pos_iff_not_neg _).mpr h)
  exists a'
  exact .inl h

instance : Repr Ordering where
  reprPrec o := match o with
    | .lt => reprPrec "lt"
    | .eq => reprPrec "eq"
    | .gt => reprPrec "gt"

def BitInt.Bits.cmp : Bits -> Bits -> Ordering
| .nil a, .nil b => compare b a
| .nil a, bs => bs.nil_cmp a
| as, .nil b => (as.nil_cmp b).swap
| .bit a as, .bit b bs => (cmp as bs).then (compare a b)

instance : Ord BitInt.Bits where
  compare := BitInt.Bits.cmp
