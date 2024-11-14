import Algebra.BitInt.Basic

-- def BitInt.sub.IsPositive {a b: BitInt} : a ≤ b ↔ (b - a).IsPositive := by
--   induction a using strongInduction generalizing b with
--   | zero =>
--     rw [sub_zero]
--     exact IsPositive.def
--   | succ a ih =>
--     rw [sub_succ]
--     rw [add.succ_add, ←add.add_succ, ←neg.pred] at h
--     rw [ih h, pred_succ]
--   | pred a ih =>
--     rw [add.pred_add, ←add.add_pred, ←neg.succ] at h
--     rw [ih h, succ_pred]

-- def BitInt.Bits.strip_even : Bits -> Bits
-- | .nil a => .nil a
-- | .bit false a => a.strip_even
-- | .bit true a => .bit true a

-- def BitInt.Bits.common_twos (n: nat) : Bits -> Bits -> Bits × Bits × nat
-- | .nil false, .bit false b => common_twos n.succ (.nil false) b
-- | .bit false a, .bit false b => common_twos n.succ a b
-- | .bit false a, .nil false => common_twos n.succ a (.nil false)
-- | a, b => ⟨a.strip_even, b.strip_even, n⟩

-- def BitInt.Bits.abs (a: Bits) : Bits := if a < 0 then -a else a

-- inductive BitInt.Bits.IsOdd : Bits -> Prop where
-- | intro : BitInt.Bits.IsPositive as -> IsOdd (bit true as)

-- def BitInt.Bits.strip_even.IsOdd : Bits.IsPositive a -> IsOdd a.strip_even ∨ a ≈ 0 := by
--   intro pos
--   induction pos with
--   | nil =>
--     exact .inr (by rfl)
--   | bit a as as_pos ih =>
--     cases a
--     cases ih
--     rw [strip_even]
--     apply Or.inl; assumption
--     apply Or.inr
--     apply bit_nil; assumption
--     apply Or.inl
--     apply IsOdd.intro
--     assumption

-- def BitInt.Bits.gcd' (a b: Bits) (ha: a.IsOdd) (hb: b.IsOdd) : Bits :=
--   match decOrd a b with
--   | .lt h => gcd' a (b - a).strip_even ha (by
--     have := IsPositive.def.mpr
--     sorry)
--   | .eq _ => a
--   | .gt _ => gcd' (a - b).strip_even b sorry sorry
-- termination_by a.length + b.length
-- decreasing_by
--   · sorry
--   · sorry

-- def BitInt.Bits.gcd (a b: Bits) :=
--   have ⟨a,b,n⟩ := common_twos 0 a.abs b.abs
--   have g := gcd' a b
--   sorry

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
