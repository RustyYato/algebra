structure Range where
  lo: Nat
  hi: Nat

abbrev range (l h: Nat) : Range := ⟨l,h⟩

instance : Membership UInt8 Range where
  mem x r := r.lo ≤ x.toNat ∧ x.toNat ≤ r.hi

inductive State where
| State1
| State2
| State3
| State4
| State5
| State6
| State7
| State8

inductive IsValidUtf8At : List UInt8 -> State -> Prop where
| Empty : IsValidUtf8At [] .State1
| ByteAscii : b ∈ range 0x00 0x7f -> IsValidUtf8At bs .State1 -> IsValidUtf8At (b::bs) .State1
| ByteC2DF : b ∈ range 0xc2 0xdf -> IsValidUtf8At bs .State2 -> IsValidUtf8At (b::bs) .State1
| ByteE0 : IsValidUtf8At bs .State4 -> IsValidUtf8At (0xe0::bs) .State1
| StateE1EC : b ∈ range 0xe1 0xec -> IsValidUtf8At bs .State3 -> IsValidUtf8At (b::bs) .State1
| StateED : IsValidUtf8At bs .State5 -> IsValidUtf8At (0xed::bs) .State1
| StateEEEF : b ∈ range 0xee 0xef -> IsValidUtf8At bs .State3 -> IsValidUtf8At (b::bs) .State1
| ByteF0 : IsValidUtf8At bs .State6 -> IsValidUtf8At (0xf0::bs) .State1
| ByteF1F3 : b ∈ range 0xf1 0xf3 -> IsValidUtf8At bs .State7 -> IsValidUtf8At (b::bs) .State1
| ByteF4 : IsValidUtf8At bs .State8 -> IsValidUtf8At (0xf4::bs) .State1

| ExitS3 : b ∈ range 0x80 0xbf -> IsValidUtf8At bs .State2 -> IsValidUtf8At (b::bs) .State3
| ExitS4 : b ∈ range 0xa0 0xbf -> IsValidUtf8At bs .State2 -> IsValidUtf8At (b::bs) .State4
| ExitS5 : b ∈ range 0x80 0x9f -> IsValidUtf8At bs .State2 -> IsValidUtf8At (b::bs) .State5
| ExitS6 : b ∈ range 0x90 0xbf -> IsValidUtf8At bs .State3 -> IsValidUtf8At (b::bs) .State6
| ExitS7 : b ∈ range 0x80 0xbf -> IsValidUtf8At bs .State3 -> IsValidUtf8At (b::bs) .State7
| ExitS8 : b ∈ range 0x80 0x8f -> IsValidUtf8At bs .State3 -> IsValidUtf8At (b::bs) .State8

| ExitS2 : b ∈ range 0x80 0xbf -> IsValidUtf8At bs .State1 -> IsValidUtf8At (b::bs) .State2

def IsValidUtf8 := (IsValidUtf8At · .State1)

def s : String := "Hello"
def s' := s.toUTF8.data.toList

def IsValidUtf8.append (a b: List UInt8) :
  IsValidUtf8 a -> IsValidUtf8 b -> IsValidUtf8 (a ++ b) := sorry

def ByteArray.toList.spec (a: ByteArray) :
  a.toList = a.data.toList := sorry

def Array.toList.spec (a: List α) :
  (Array.mk a).toList = a := sorry

def UInt32.toNatToUint8toNat (c: UInt32) :
  c.toNat.toUInt8.toNat = c.toNat % 256 := rfl

def Nat.mod2_spec : ∀n, n % 2 = 0 ∨ n % 2 = 1 := by
  intro n
  cases h:n % 2
  exact .inl rfl
  rename_i m
  cases m
  exact .inr rfl
  have := @Nat.mod_lt n 2 (by trivial)
  rw [h] at this
  contradiction

def Nat.trailing_zeros (a: Nat) : 0 < a -> Nat := by
  intro a_pos
  if a % 2 = 1 then
    exact 0
  else
    exact 1 + Nat.trailing_zeros (a / 2) (by
      have : a % 2 = 0 := by cases Nat.mod2_spec a <;> trivial
      apply Nat.lt_of_mul_lt_mul_right
      rw [Nat.div_mul_cancel, Nat.zero_mul]
      assumption
      exact dvd_of_mod_eq_zero this)

def Nat.testBit_trailing_zeros (a: Nat) (a_pos: 0 < a) :
  a.testBit (a.trailing_zeros a_pos) = true := by
  induction a, a_pos using Nat.trailing_zeros.induct with
  | case1 a a_pos h =>
    unfold trailing_zeros
    rw [dif_pos h]
    unfold testBit
    apply (bne_iff_ne _ _).mpr
    intro g
    rw [Nat.shiftRight_zero, Nat.one_and_eq_mod_two, h] at g
    contradiction
  | case2 a a_pos h ih =>
    have : a % 2 = 0 := by cases Nat.mod2_spec a <;> trivial
    unfold testBit trailing_zeros
    rw [dif_neg h]
    rw [Nat.one_add, Nat.shiftRight_succ_inside]
    apply ih

-- ∀maxbit, b.testBit maxbit < a.testBit maxbit -> ∃n > maxbit, a.testBit n < b.testBit n

#print not_and

def Nat.le_of_bitwise (a b: Nat) :
  (∀n, a.testBit n ≤ b.testBit n) ->
  a ≤ b := by
  induction a, b using Nat.bitwise.induct with
  | f a b => exact false
  | case1 | case3 | case5 => contradiction
  | case2 b h =>
    clear h
    apply Iff.intro
    · intro h
      exists 0
      intro n _
      rw [zero_testBit]
      apply Bool.false_le
    · intro h
      apply Nat.zero_le
  | case4 a a_pos h =>
    apply Iff.intro
    · intro h
      cases Nat.le_zero.mp h
      contradiction
    · intro ⟨maxbit,prf⟩
      apply Nat.le_zero.mpr
      apply Nat.eq_of_testBit_eq
      intro n
      have := prf n
      sorry
  | case6 => sorry

def Nat.bitwise_lt (a b: Nat) :
  (a < b) ↔ (∃maxbit, a.testBit maxbit < b.testBit maxbit ∧ ∀n > maxbit, a.testBit n ≤ b.testBit n) := by
  induction a, b using Nat.bitwise.induct with
  | f a b => exact false
  | case1 | case3 | case5 => contradiction
  | case2 b h =>
    apply Iff.intro
    · intro b_pos
      exists b.trailing_zeros b_pos
      apply And.intro
      rw [zero_testBit, Nat.testBit_trailing_zeros]
      trivial
      intro n g
      rw [zero_testBit]
      apply Bool.false_le
    · intro ⟨maxbit,bset,anotset⟩
      refine zero_lt_of_ne_zero ?case2.mpr.h
      intro g
      subst g
      rw [zero_testBit] at bset
      contradiction
  | case4 a a_pos h =>
    clear h
    apply Iff.intro
    intro h
    contradiction
    intro ⟨h,prf,_⟩
    rw [zero_testBit] at prf
    have := Bool.lt_irrefl _ (Bool.lt_of_le_of_lt (Bool.false_le _) prf)
    contradiction
  | case6 a b a_pos b_pos a' b' =>
    rename_i a_odd b_odd h ih
    clear a_odd b_odd h
    apply Iff.intro
    · intro h
      cases decLt a (2 * (b / 2))
      case isTrue h =>
        replace h := Nat.div_lt_of_lt_mul h
        have ⟨maxbit,set,unsetas⟩ := ih.mp h
        exists maxbit.succ
        repeat any_goals apply And.intro
        rw [testBit_succ, testBit_succ]
        exact set
        intro n n_gt
        cases n
        contradiction
        rw [testBit_succ, testBit_succ]
        apply unsetas
        apply Nat.lt_of_succ_lt_succ
        assumption
      case isFalse h₀ =>
        have squeeze : ∀ n m: Nat, m < n -> n < m + 1 -> False := by
          intros n m m_lt_n n_lt_m_succ
          have := Nat.le_of_lt_succ n_lt_m_succ
          have := Nat.lt_of_lt_of_le m_lt_n this
          exact Nat.lt_irrefl _ this
        replace h₀ := Nat.le_of_not_lt h₀
        cases Nat.lt_or_eq_of_le h₀ <;> rename_i h₀
        cases Nat.mod2_spec b <;> rename_i g
        rw [←Nat.div_add_mod b 2, g, Nat.add_zero] at h
        have := Nat.lt_irrefl _ <| Nat.lt_trans h h₀
        contradiction
        rw [←Nat.div_add_mod b 2, g] at h
        have := Nat.lt_irrefl _ <| Nat.lt_of_lt_of_le h h₀
        contradiction
        subst a
        clear h₀
        exists 0
        have : b % 2 = 1 := by
          conv at h => {
            rhs
            rw [←Nat.div_add_mod b 2]
          }
          have := Nat.pos_of_lt_add_right h
          cases Nat.mod2_spec b <;> rename_i g
          rw [g] at this
          contradiction
          assumption
        apply And.intro
        repeat any_goals apply And.intro
        unfold testBit
        rw [Nat.shiftRight_zero, Nat.one_and_eq_mod_two,
          Nat.one_and_eq_mod_two, Nat.shiftRight_zero, this,
          Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
        trivial
        intro n n_pos
        cases n
        contradiction
        unfold testBit
        repeat rw [Nat.shiftRight_succ_inside]
        rw [Nat.mul_comm, Nat.mul_div_cancel]
        apply Bool.le_refl
        trivial
    · intro ⟨maxbit,set,unsetas⟩
      cases maxbit
      have := Nat.le_of_bitwise (a / 2) (b / 2) (by
        intro n
        have := unsetas n.succ (Nat.zero_lt_succ _)
        rw [testBit_succ, testBit_succ] at this
        exact this)

      cases decLt a (2 * (b / 2))
      case isTrue h =>

        sorry
      case isFalse h =>
        sorry

def Nat.le_or_left  (a b: Nat) : a ≤ a ||| b := by
  suffices a ≤ a.bitwise Bool.or b from this
  induction a, b using Nat.bitwise.induct
  rename_i a b
  exact Bool.or a b
  apply Nat.zero_le
  apply Nat.zero_le
  repeat (
    unfold Nat.bitwise
    rw [if_neg, if_pos]
    apply Nat.le_refl
    rfl
    assumption
  )
  rename_i a b a_nz b_ns a' b' a_odd b_odd h _
  dsimp
  unfold Nat.bitwise
  rw [if_neg, if_neg]
  dsimp
  rw [if_pos]
  conv => { lhs; rw [←Nat.div_add_mod a 2] }
  rw [Nat.two_mul]
  apply Nat.add_le_add
  apply Nat.add_le_add
  repeat assumption
  apply Nat.le_of_lt_succ
  apply Nat.mod_lt
  trivial
  repeat assumption
  unfold Nat.bitwise

  rename_i a b a_nz b_ns a' b' a_odd b_odd h _
  rw [if_neg, if_neg]
  dsimp
  rw [if_neg]
  conv => { lhs; rw [←Nat.div_add_mod a 2] }
  rw [Nat.two_mul]
  have := (Bool.or_eq_false_iff _ _).mp (Bool.eq_false_iff.mpr h)
  have : a % 2 = 0 := by
    have := decide_eq_false_iff_not.mp (this.left)
    match h:a%2 with
    | 0 => rfl
    | 1 => contradiction
    | n + 2 =>
      have := @Nat.mod_lt a 2 (by trivial)
      rw [h] at this
      contradiction
  rw [this, Nat.add_zero]
  apply Nat.add_le_add
  repeat assumption

def Nat.or_comm  (a b: Nat) : a ||| b = b ||| a := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_or, testBit_or, Bool.or_comm]

def Nat.le_or_right  (a b: Nat) : b ≤ a ||| b := by
  rw [Nat.or_comm]
  apply Nat.le_or_left

def Nat.or_le_or  (a b k: Nat) : a ≤ b -> a ||| k ≤ b ||| k := by
  intro a_le_b
  suffices a.bitwise Bool.or k ≤ b.bitwise Bool.or k from this
  induction b, k using Nat.bitwise.induct generalizing a with
  | f b k => exact b.or k
  | case1 b h =>
    unfold bitwise
    rw [if_pos (Nat.le_zero.mp a_le_b), if_pos h, if_pos rfl]
    apply Nat.le_refl
  | case2 b h => contradiction
  | case3 b b_pos h =>
    unfold bitwise
    repeat rw [if_pos rfl]
    have : true.or false = true := rfl
    rw [if_neg b_pos, if_pos this, if_pos this]
    have : false.or true = true := rfl
    rw [if_pos this]
    split
    apply Nat.zero_le
    assumption
  | case4 => contradiction
  | case5 b k b_pos k_pos b' k' =>
    rename_i b_odd k_odd h ih
    rw [bitwise]
    rw [if_neg k_pos]
    dsimp
    split
    subst a
    have := ih 0 (Nat.zero_le _)
    apply Nat.le_or_right
    conv => { rhs; rw [bitwise] }
    rw [if_neg b_pos, if_neg k_pos, if_pos h]
    replace ih := ih (a / 2) (by
        apply Nat.le_of_mul_le_mul_left _
        have : 0 < 2 := by trivial
        exact this
        apply flip Nat.le_trans
        apply @Nat.le_of_add_le_add_right _ 1
        have : 2 * (a / 2) + 1 ≤ 2 * (b / 2) + 1 := by
          have : ∀n, n % 2 = 0 ∨ n % 2 = 1 := Nat.mod2_spec
          cases this a <;> rename_i h₀
          <;> cases this b <;> rename_i h₁
          rw [Nat.mul_comm 2, Nat.mul_comm 2, Nat.div_mul_cancel, Nat.div_mul_cancel]
          apply Nat.add_le_add_right
          assumption
          exact dvd_of_mod_eq_zero h₁
          exact dvd_of_mod_eq_zero h₀
          rw [Nat.mul_comm 2, Nat.div_mul_cancel, ←h₁, Nat.div_add_mod, h₁]
          apply Nat.succ_le_of_lt
          apply Nat.lt_of_le_of_ne a_le_b
          intro h₂
          rw [h₂] at h₀
          rw [h₀] at h₁
          contradiction
          exact dvd_of_mod_eq_zero h₀
          rw [←h₀, Nat.div_add_mod, h₀, Nat.mul_comm 2, Nat.div_mul_cancel]
          apply Nat.le_trans a_le_b
          apply Nat.le_succ
          exact dvd_of_mod_eq_zero h₁
          conv => { lhs; rw [←h₀] }
          rw [←h₁, Nat.div_add_mod, Nat.div_add_mod]
          assumption
        exact this
        apply Nat.le_refl
      )
    split
    repeat apply Nat.add_le_add
    repeat apply ih
    apply Nat.le_refl
    apply flip Nat.le_trans
    apply Nat.le_succ
    apply Nat.add_le_add
    repeat apply ih
  | case6 b k b_pos k_pos b' k' b_odd k_odd =>
    rename_i h ih
    have h' := Bool.eq_false_iff.mpr h
    have h' := (Bool.or_eq_false_iff _ _).mp h'
    have := of_decide_eq_false h'.left
    have := of_decide_eq_false h'.right
    have b_even : b % 2 = 0 := by cases Nat.mod2_spec b <;> trivial
    have k_even : k % 2 = 0 := by cases Nat.mod2_spec k <;> trivial
    rw [bitwise]
    rw [if_neg k_pos, if_pos (by rfl: false.or true = true)]
    dsimp
    split
    apply Nat.le_or_right
    conv => {
      rhs
      rw [bitwise]
      rw [if_neg k_pos, if_neg b_pos, if_neg h]
    }
    split
    rename_i g
    cases (Bool.or_eq_true_iff _ _).mp g <;> rename_i g





    sorry







def String.utf8EncodeChar.IsValidUtf8 (c: Char) : IsValidUtf8 (String.utf8EncodeChar c) := by
  cases c with
  | mk val valid_char =>
  cases val with
  | mk val =>
  cases val with
  | mk val valLt =>
  unfold utf8EncodeChar UInt32.toUInt8 UInt32.toNat Nat.toUInt8 UInt8.ofNat Fin.ofNat
  have lift_and : ∀a b: UInt8, (a &&& b).toNat = a.toNat &&& b.toNat := by intros; rfl
  have lift_or : ∀a b: UInt8, (a ||| b).toNat = a.toNat ||| b.toNat := by intros; rfl
  have lift_ofNat : ∀n: Nat, (@OfNat.ofNat UInt8 n).toNat = n := by intros; rfl
  dsimp
  split
  · apply IsValidUtf8At.ByteAscii
    apply And.intro
    apply Nat.zero_le
    unfold UInt8.toNat
    rename_i h
    dsimp
    rw [Nat.mod_eq_of_lt]
    exact h
    apply Nat.lt_of_le_of_lt h
    trivial
    apply IsValidUtf8At.Empty
  split
  · apply IsValidUtf8At.ByteC2DF
    sorry
    apply IsValidUtf8At.ExitS2
    apply And.intro
    rw [lift_or, lift_and, lift_ofNat, lift_ofNat]
    unfold UInt8.toNat
    dsimp
    apply flip Nat.le_trans
    rw [Nat.or_comm]
    apply Nat.le_or_left
    apply Nat.le_refl
    rw [lift_or, lift_and, lift_ofNat, lift_ofNat]
    unfold UInt8.toNat
    dsimp
    apply @Nat.le_trans _  (63 ||| 128)
    sorry





    sorry
  split
  · sorry
  · sorry

def String.IsValidUtf8 (s: String) : IsValidUtf8 s.toUTF8.toList := by
  cases s with | mk s =>
  unfold String.toUTF8
  rw [ByteArray.toList.spec, Array.toList.spec]
  dsimp
  induction s with
  | nil => apply IsValidUtf8At.Empty
  | cons c s ih =>
    rw [List.bind_cons]
    apply IsValidUtf8.append _ _ _ ih
    apply String.utf8EncodeChar.IsValidUtf8
