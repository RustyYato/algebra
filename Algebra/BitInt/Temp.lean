import Algebra.BitInt.Basic

def BitInt.sub.IsPositive {a b: BitInt} : a ≤ b ↔ (b - a).IsPositive := by
  induction a using strongInduction generalizing b with
  | zero =>
    rw [sub_zero]
    exact IsPositive.def
  | succ a ih =>
    rw [sub_succ, ←sub.pred_sub]
    apply Iff.trans succ_le_iff_le_pred
    apply ih
  | pred a ih =>
    rw [sub_pred, ←sub.succ_sub]
    apply Iff.trans le_succ_iff_pred_le.symm
    apply ih

def BitInt.Bits.sub.IsPositive {a b: Bits} : a ≤ b ↔ (b - a).IsPositive := by
  apply Iff.trans mk_le.symm
  apply Iff.trans _ (mk_IsPositive _)
  rw [←mk_sub]
  exact BitInt.sub.IsPositive

def BitInt.Bits.strip_even : Bits -> Bits
| .nil a => .nil a
| .bit false a => a.strip_even
| .bit true a => .bit true a

def BitInt.Bits.toNat.spec (a b: Bits) :
  a.IsPositive ->
  a ≈ b ->
  a.toNat = b.toNat := by
  intro apos ab
  induction ab with
  | nil_nil _ => rfl
  | nil_bit a b ab ih =>
    unfold toNat
    erw [←ih, Nat.zero_mul]
    cases apos
    rw [if_neg Bool.noConfusion]
    assumption
  | bit_nil b a ab ih =>
    cases apos
    unfold toNat
    erw [ih, Nat.zero_mul, Nat.zero_add]
    rename_i h
    cases (IsPositive.spec _ _ ab).mp h
    rw [if_neg Bool.noConfusion]
    assumption
  | bit_bit x a b _ ih =>
    cases apos
    unfold toNat
    congr 1
    rw [ih]
    assumption

def BitInt.Bits.strip_even.spec (a b: Bits) :
  a ≈ b ->
  a.strip_even ≈ b.strip_even := by
  intro ab
  induction ab with
  | nil_nil _ => rfl
  | nil_bit a b ab ih =>
    cases a
    apply ih
    apply nil_bit
    assumption
  | bit_nil b a ab ih =>
    cases b
    apply ih
    apply bit_nil
    assumption
  | bit_bit x a b ab ih =>
    cases x
    apply ih
    apply bit_bit
    assumption

def BitInt.Bits.common_twos (n: nat) : Bits -> Bits -> Bits × Bits × nat
| .nil false, .bit false b => common_twos n.succ (.nil false) b
| .bit false a, .bit false b => common_twos n.succ a b
| .bit false a, .nil false => common_twos n.succ a (.nil false)
| a, b => ⟨a.strip_even, b.strip_even, n⟩

def BitInt.Bits.abs (a: Bits) : Bits := if a < 0 then -a else a

inductive BitInt.Bits.IsPosOdd : Bits -> Prop where
| intro : BitInt.Bits.IsPositive as -> IsPosOdd (bit true as)

def BitInt.Bits.IsPosOdd.IsPositive : IsPosOdd x -> IsPositive x
| .intro h => IsPositive.bit _ _ h

def BitInt.Bits.strip_even.IsPosOdd : Bits.IsPositive a -> IsPosOdd a.strip_even ∨ a ≈ 0 := by
  intro pos
  induction pos with
  | nil =>
    exact .inr (by rfl)
  | bit a as as_pos ih =>
    cases a
    cases ih
    rw [strip_even]
    apply Or.inl; assumption
    apply Or.inr
    apply bit_nil; assumption
    apply Or.inl
    apply IsPosOdd.intro
    assumption

def BitInt.Bits.strip_even_le_self : Bits.IsPositive a -> a.strip_even ≤ a := by
  intro pos
  induction pos with
  | nil =>
    exact .inr (by rfl)
  | bit a as as_pos ih =>
    cases a
    cases ih
    rw [strip_even]
    apply Or.inl; sorry
    apply Or.inr
    apply bit_nil; assumption
    apply Or.inl
    apply IsPosOdd.intro
    assumption

def BitInt.Bits.toNat.lt (a b: Bits) :
  Bits.IsPositive a ->
  a < b -> a.toNat < b.toNat := by
  sorry

def BitInt.Bits.toNat.le (a b: Bits) :
  Bits.IsPositive a ->
  a ≤ b -> a.toNat ≤ b.toNat := by
  sorry

def BitInt.Bits.gcd'.term (a b: Bits) (ha: a.IsPosOdd) (hb: b.IsPosOdd) :
  a < b ->
  (b - a).strip_even.toNat < b.toNat := by
  intro a_lt_b
  cases ha with | intro ha =>
  cases hb with | intro hb =>
  rename_i as bs
  have : bit true bs - bit true as ≈ bit false (bs - as) := by
    rw [sub.def]
    apply trans
    apply add.spec
    rfl
    apply neg_eq_neg_naive
    apply bit_bit
    apply trans
    exact add_with_carry.eq_add_if bs as.not true
    rw [if_pos rfl]
    apply BitInt.exact
    rw [←mk_succ, ←mk_add, ←BitInt.add.add_succ, mk_succ,
      ←sound (Bits.neg_eq_not_succ as), mk_add]
    rfl
  have pos : (bs - as).IsPositive := by
    apply sub.IsPositive.mp
    left
    cases a_lt_b
    assumption
  have posodd' : (bs - as).strip_even.IsPosOdd := by
    cases strip_even.IsPosOdd pos
    assumption
    rename_i h
    cases a_lt_b <;> rename_i a_lt_b
    have := not_le_of_lt' _ _ a_lt_b (.inr (sub.eq_zero_iff.mp h))
    contradiction
  rw [toNat.spec _ _ _ (strip_even.spec _ _ this)]
  unfold strip_even
  apply Nat.lt_of_le_of_lt
  apply BitInt.Bits.toNat.le
  exact posodd'.IsPositive
  apply Bits.strip_even_le_self
  exact pos
  apply BitInt.Bits.toNat.lt
  exact pos
  · apply mk_lt.mp
    rw [←mk_sub]
    show _ < mk (bit false bs).succ
    erw [←mk_succ, ←sound (Bits.mul.two_mul _), ←mk_mul, BitInt.mul.two_mul, ←BitInt.add.add_succ]
    apply BitInt.add.lt_left
    apply lt_of_le_of_lt
    show -mk as ≤ 0
    apply BitInt.neg.swap_le.mpr
    rw [BitInt.neg_neg, BitInt.neg.zero, BitInt.mk_zero]
    apply mk_le.mpr
    apply IsPositive.def.mpr
    assumption
    apply lt_of_le_of_lt _ BitInt.lt_succ_self
    rw [BitInt.mk_zero]
    apply mk_le.mpr
    apply IsPositive.def.mpr
    assumption
  apply (IsPositive.spec _ _ _).mp
  exact posodd'.IsPositive
  symm
  apply trans
  apply strip_even.spec
  exact this
  rw [strip_even]

def BitInt.Bits.gcd' (a b: Bits) (ha: a.IsPosOdd) (hb: b.IsPosOdd) : Bits :=
  match decOrd a b with
  | .lt h => gcd' a (b - a).strip_even ha (by
    have : (b - a).IsPositive := by
      apply IsPositive.def.mp
      apply add.of_le_left (k := a)
      apply mk_le.mp
      erw [←mk_add, BitInt.add.add_zero, ←mk_add, ←mk_sub,
        ←BitInt.add_sub_assoc, BitInt.add.comm, BitInt.add_sub_assoc,
        BitInt.sub.self, BitInt.add.add_zero]
      apply mk_le.mpr
      left
      assumption
    cases strip_even.IsPosOdd this
    assumption
    rename_i g
    have := BitInt.Bits.sub.eq_zero_iff.mp g
    have := not_le_of_lt' _ _ h (.inr this)
    contradiction)
  | .eq _ => a
  | .gt h => gcd' (a - b).strip_even b (by
    have : (a - b).IsPositive := by
      apply IsPositive.def.mp
      apply add.of_le_left (k := b)
      apply mk_le.mp
      erw [←mk_add, BitInt.add.add_zero, ←mk_add, ←mk_sub,
        ←BitInt.add_sub_assoc, BitInt.add.comm, BitInt.add_sub_assoc,
        BitInt.sub.self, BitInt.add.add_zero]
      apply mk_le.mpr
      left
      assumption
    cases strip_even.IsPosOdd this
    assumption
    rename_i g
    have := BitInt.Bits.sub.eq_zero_iff.mp g
    have := not_le_of_lt' _ _ h (.inr this)
    contradiction) hb
termination_by a.toNat + b.toNat
decreasing_by
  · apply Nat.add_lt_add_left
    apply gcd'.term
    repeat assumption
  · apply Nat.add_lt_add_right
    apply gcd'.term
    repeat assumption

def BitInt.Bits.gcd (a b: Bits) :=
  match h:common_twos 0 a.abs b.abs with
  | ⟨a',b',n⟩ => (gcd' a' b' sorry sorry).shl n

-- #eval (20: BitInt.Bits)
-- #eval (30: BitInt.Bits)
-- #eval BitInt.Bits.common_twos 0 20 30

-- def BitInt.Bits.gcd (a b: Bits) : Bits :=

--   sorry

-- def BitInt.Bits.sqrt.spec (a b: Bits) :
--   a ≈ b ->
--   (apos: a.IsPositive) ->
--   (bpos: b.IsPositive) ->
--   (sqrt a apos).1 ≈ (sqrt b bpos).1 := by
--   intro ab apos bpos
--   induction a, apos using BitInt.Bits.sqrt.induct generalizing b with
--   | case1 is_neg pos =>
--     cases pos
--     show 0 ≈ _
--     induction b, bpos using BitInt.Bits.sqrt.induct with
--     | case1 is_neg pos => rfl
--     | case2 => nomatch ab
--     | case3 => cases ab; rfl
--     | case4 b₀ b₁ bs bpos b' bsqrt bsqrt_sq bs_sqrt_eq bsuccsqrt_sq hb ih =>
--       cases ab <;> rename_i ab
--       cases ab
--       rw [sqrt]
--       dsimp
--       rw [if_neg]
--       apply nil_bit
--       apply ih
--       assumption
--       rw [bs_sqrt_eq]
--       dsimp
--       apply not_le_of_lt'

--       have : (bit false (bit false (bs.sqrt _).snd) + bit false (bit false (bs.sqrt _).fst)).succ ≤ bit false (bit false bs) := h

--       sorry
--     | case5 => sorry
--   | case2 => sorry
--   | case3 => sorry
--   | case4 => sorry
--   | case5 => sorry

-- #eval BitInt.Bits.sqrt 100 (by decide)
