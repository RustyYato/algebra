import Algebra.Nat.Add
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
| nil x : Equiv (.nil x) (.nil x)
| nil_bit x xs : Equiv (.nil x) xs -> Equiv (.nil x) (.bit x xs)
| bit_nil x xs : Equiv xs (.nil x) -> Equiv (.bit x xs) (.nil x)
| bit x as bs : Equiv as bs -> Equiv (.bit x as) (.bit x bs)

instance BitInt.Bits.setoid : Setoid Bits where
  r := Bits.Equiv
  iseqv.refl := by
    intro x
    induction x with
    | nil => exact .nil _
    | bit b bs ih => exact ih.bit _
  iseqv.symm := by
    intro x y h
    induction h with
    | nil => exact .nil _
    | nil_bit _ _ _ ih => exact ih.bit_nil
    | bit_nil _ _ _ ih => exact ih.nil_bit
    | bit _ _ _ _ ih => exact ih.bit _
  iseqv.trans := by
    intro a b c ab bc
    induction ab generalizing c with
    | nil => exact bc
    | nil_bit _ _ _ ih =>
      cases bc
      exact .nil _
      apply Equiv.nil_bit
      apply ih
      assumption
    | bit_nil _ _ _ ih =>
      cases bc
      apply Equiv.bit_nil
      assumption
      apply Equiv.bit
      apply ih
      assumption
    | bit _ _ _ _ ih =>
      cases bc
      apply Equiv.bit_nil
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
| .nil true, true | .nil false, false => .isTrue (.nil _)
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
    | .isTrue h => .isTrue (h.bit _)
    | .isFalse h => .isFalse (fun g => by cases g; contradiction)

def BitInt.Bits.IsMinimal.spec (a b: Bits) : a ≈ b -> a.IsMinimal -> b.IsMinimal -> a = b := by
  intro eq amin bmin
  induction eq with
  | nil => rfl
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
  | bit _ _ _ _ ih =>
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
  | nil => exact ⟨.nil _,.nil _⟩
  | bit b bs ih =>
    have := push_bit.spec b ih.right
    apply And.intro _ this.right
    apply Bits.trans (ih.left.bit _) this.left

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

def BitInt.sound' : ∀a b: BitInt, a.bits ≈ b.bits -> a = b := by
  intro a b eq
  apply bits.inj
  apply Bits.IsMinimal.spec
  assumption
  exact a.is_minimal
  exact b.is_minimal
def BitInt.sound : ∀a b: Bits, a ≈ b -> mk a = mk b := by
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
def BitInt.exact : ∀a b: Bits, mk a = mk b -> a ≈ b := by
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

@[reducible]
def BitInt.Bits.ofNat : Nat -> Bits
| 0 => .nil false
| n + 1 => .bit ((n + 1) % 2 == 1) (ofNat ((n + 1) / 2))
decreasing_by
  exact ofNat.rec_lemma

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

instance BitInt.Bits.OfNatInst : OfNat BitInt n := ⟨⟨.ofNat n,ofNat.is_minimal n⟩⟩

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
  | nil => rfl
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
  | bit _ _ _ _ ih =>
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
      apply Bits.Equiv.nil_bit
      apply ih
      intro n
      conv => { rhs; rw [←@Bits.test_bit_bit_succ _ a] }
      rw [←h n.succ, Bits.test_bit_nil, Bits.test_bit_nil]
  | bit a _ _ _ ih =>
    cases bmin with
    | nil =>
      cases h 0
      apply Bits.Equiv.bit_nil
      apply ih
      exact (.nil _)
      intro n
      conv => { lhs; rw [←@Bits.test_bit_bit_succ _ a] }
      rw [h n.succ, Bits.test_bit_nil, Bits.test_bit_nil]
    | bit =>
      cases h 0
      apply Bits.Equiv.bit
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
  | nil => rfl
  | nil_bit =>
    apply Bits.Equiv.nil_bit
    assumption
  | bit_nil =>
    apply Bits.Equiv.bit_nil
    assumption
  | bit _ _ _ _ ih =>
    apply Bits.Equiv.bit
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
  | nil a =>
    rw [nil_bit_zip_with, nil_bit_zip_with]
    apply bit_map.spec
    assumption
  | nil_bit a cs _ ih =>
    cases bd
    apply Bits.Equiv.nil_bit
    apply flip Bits.trans
    apply bit_map.spec
    assumption
    rfl
    apply Bits.Equiv.nil_bit
    apply flip Bits.trans
    apply ih
    assumption
    rfl
    apply Bits.Equiv.bit
    apply flip Bits.trans
    apply bit_map.spec
    assumption
    apply Bits.trans
    apply bit_map.spec
    assumption
    rfl
    apply Bits.Equiv.bit
    apply flip Bits.trans
    apply ih
    assumption
    rw [nil_bit_zip_with]
  | bit_nil _ _ _ ih =>
    rw [nil_bit_zip_with]
    cases bd
    apply Bits.Equiv.bit_nil
    apply Bits.trans
    apply bit_map.spec
    assumption
    rfl
    apply Bits.Equiv.bit
    apply Bits.trans
    apply bit_map.spec
    assumption
    apply flip Bits.trans
    apply bit_map.spec
    assumption
    rfl
    apply Bits.Equiv.bit_nil
    apply Bits.trans
    apply ih
    assumption
    rfl
    apply Bits.Equiv.bit
    apply Bits.trans
    apply ih
    assumption
    rw [nil_bit_zip_with]
  | bit _ _ _ _ ih =>
    cases bd
    all_goals apply Bits.Equiv.bit
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
