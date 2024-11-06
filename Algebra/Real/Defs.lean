import Algebra.Rat.Defs
import Algebra.Equiv

def CauchySeq.is_cauchy (f: nat -> Rat) : Prop :=
  ∀ε: Rat, 0 < ε -> ∃n: nat, ∀k ≥ n, ‖f n - f k‖ < ε

def CauchySeq.is_cauchy_equiv (f g: nat -> Rat) : Prop :=
  ∀ε: Rat, 0 < ε -> ∃n: nat, ∀x y, n ≤ x -> n ≤ y -> ‖f x - g y‖ < ε

def CauchySeq.is_cauchy_iff_is_cauchy_equiv { f: nat -> Rat } :
  is_cauchy f ↔ is_cauchy_equiv f f := by
  unfold is_cauchy is_cauchy_equiv
  apply Iff.intro
  · intro c ε ε_pos
    have ⟨ n, prf ⟩ := c (ε / 2) (Rat.half_pos ε_pos)
    exists n
    intro x y n_le_x n_le_y
    rw [←Rat.zero_add (_ - _), ←Rat.sub.self (f n), Rat.sub.eq_add_neg,
      Rat.add.assoc, Rat.sub.eq_add_neg, Rat.add.comm_right (-f n),
      ←Rat.add.assoc, ←Rat.sub.eq_add_neg, ←Rat.sub.eq_add_neg]
    apply lt_of_le_of_lt
    apply Rat.abs.add_le
    rw [Rat.half_sum ε]
    apply Rat.add.lt
    apply prf
    assumption
    rw [Rat.abs.sub_comm]
    apply prf
    assumption
  · intro c ε ε_pos
    have ⟨ n, prf ⟩ := c ε ε_pos
    exists n
    intro k k_ge_n
    apply prf
    rfl
    assumption

structure CauchySeq where
  seq: nat -> Rat
  seq_is_cauchy: CauchySeq.is_cauchy seq

instance : CoeFun CauchySeq (fun _ => nat -> Rat) where
  coe := CauchySeq.seq

-- marked noncomputable so that lean doesn't try to geneRate any code for this
noncomputable
def CauchySeq.max_to (s: CauchySeq) : nat -> Rat
| .zero => s 0
| .succ n => max (s n.succ) (s.max_to n)

def CauchySeq.max_to.spec (s: CauchySeq) (n: nat) : ∀x ≤ n, s x ≤ s.max_to n := by
  intro x x_le_n
  induction n with
  | zero =>
    cases nat.le_zero x_le_n
    rfl
  | succ n ih =>
    cases lt_or_eq_of_le x_le_n <;> rename_i h
    apply le_trans (ih (nat.le_of_lt_succ h))
    apply le_max_right
    subst h
    apply le_max_left

def CauchySeq.upper_bound (s: CauchySeq) : ∃r: Rat, ∀k, s k < r := by
  have ⟨ n, prf ⟩ := (is_cauchy_iff_is_cauchy_equiv.mp s.seq_is_cauchy) 1 (by decide)
  exists 1 + s.max_to n.succ
  intro k
  have := max_to.spec s n k
  apply if h:n < k then ?_ else ?_
  · rw [←Rat.zero_add (s k), ←Rat.sub.self (s n.succ),
      Rat.sub.eq_add_neg, Rat.add.right_comm, Rat.add.assoc, ←Rat.sub.eq_add_neg]
    apply lt_of_le_of_lt
    apply Rat.add.le
    rfl
    have : s k - s n.succ ≤ ‖s k - s n.succ‖ := by
      rw [Rat.abs.eq_max]
      apply le_max_left
    exact this
    rw [Rat.add.comm]
    apply Rat.add_lt_of_lt_of_le
    rw [Rat.abs.sub_comm]
    apply prf
    apply le_of_lt
    apply nat.lt_succ_self
    apply le_of_lt
    assumption
    apply le_max_left
  · replace h := le_of_not_lt h
    apply lt_of_le_of_lt
    apply this
    assumption
    apply lt_of_le_of_lt _ _
    exact 0 + s.max_to n.succ
    rw [Rat.zero_add]
    apply le_max_right
    apply Rat.add_lt_of_lt_of_le
    trivial
    rfl

def CauchySeq.upper_bound_with (s: CauchySeq) (x: Rat) : ∃r > x, ∀k, s k < r := by
  have ⟨ r, prf ⟩  := s.upper_bound
  exists max r (x + 1)
  apply And.intro
  apply flip lt_of_lt_of_le
  apply le_max_right
  conv => { lhs; rw [←Rat.zero_add x] }
  rw [Rat.add.comm]
  apply Rat.add.lt_right.mp
  trivial
  intro k
  apply lt_of_lt_of_le
  apply prf
  apply le_max_left

instance CauchySeq.HasEquivInst : HasEquiv CauchySeq := ⟨(is_cauchy_equiv ·.seq ·.seq)⟩
def CauchySeq.equiv_def (a b: CauchySeq) : (a ≈ b) = (is_cauchy_equiv a.seq b.seq) := rfl

@[refl]
def CauchySeq.refl (a: CauchySeq) : a ≈ a := by
  apply is_cauchy_iff_is_cauchy_equiv.mp
  exact a.seq_is_cauchy

@[symm]
def CauchySeq.symm {a b: CauchySeq} : a ≈ b -> b ≈ a := by
  intro ab ε ε_pos
  have ⟨n,prf⟩ := ab ε ε_pos
  exists n
  intro x y nx ny
  rw [Rat.abs.sub_comm]
  apply prf <;> assumption

def CauchySeq.trans {a b c: CauchySeq} : a ≈ b -> b ≈ c -> a ≈ c := by
  intro ab bc ε ε_pos
  have ⟨n,nprf⟩ := ab _ (Rat.half_pos ε_pos)
  have ⟨m,mprf⟩ := bc _ (Rat.half_pos (Rat.half_pos ε_pos))
  have ⟨o,oprf⟩ := (is_cauchy_iff_is_cauchy_equiv.mp b.seq_is_cauchy) _ (Rat.half_pos (Rat.half_pos ε_pos))
  exists max o (max n m)
  intro x y nx ny
  replace ⟨_,nx⟩  := max_le_iff.mp nx
  have ⟨_,_⟩  := max_le_iff.mp nx
  replace ⟨_,ny⟩  := max_le_iff.mp ny
  have ⟨_,_⟩  := max_le_iff.mp ny
  rw [←Rat.add_zero (a x - c y), ←Rat.sub.self (b y)]
  rw [←Rat.add_zero (a x - c y), ←Rat.sub.self (b x)]
  repeat rw [Rat.sub.eq_add_neg]
  rw [←Rat.add.assoc, ←Rat.add.assoc,
    Rat.add.assoc (a x + _ + _), Rat.add.assoc (a x + _ + _),
    Rat.add.right_comm _ (-c y), Rat.add.assoc _ (b x),
    Rat.add.left_comm _ (b y),
    ←Rat.add.assoc, ←Rat.add.assoc, Rat.add.assoc,
    Rat.add.right_comm (a x)]
  apply lt_of_le_of_lt
  apply Rat.abs.add_le
  apply lt_of_le_of_lt
  apply Rat.add.le
  apply Rat.abs.add_le
  rfl
  have : ε = ε / 2 + ε / 2 / 2 + ε / 2 / 2 := by rw [Rat.add.assoc, ←Rat.half_sum, ←Rat.half_sum]
  repeat rw [←Rat.sub.eq_add_neg]
  rw [this, Rat.abs.sub_comm (b y)]
  apply Rat.add.lt
  apply Rat.add.lt
  apply nprf <;> assumption
  apply mprf <;> assumption
  apply oprf <;> assumption

instance CauchySeq.setoid : Setoid CauchySeq where
  r a b := a ≈ b
  iseqv := ⟨CauchySeq.refl,CauchySeq.symm,CauchySeq.trans⟩

def Real := Equiv CauchySeq.setoid
notation "ℝ" => Real
def Real.mk : CauchySeq -> ℝ := Equiv.mk CauchySeq.setoid
def Real.ind : {motive: ℝ -> Prop} -> (mk: ∀x, motive (mk x)) -> ∀r, motive r := Equiv.ind
def Real.lift : (f: CauchySeq -> α) -> (∀a b, a ≈ b -> f a = f b) -> ℝ -> α := Equiv.lift
def Real.lift₂ : (f: CauchySeq -> CauchySeq -> α) -> (∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> ℝ -> ℝ -> α := Equiv.lift₂
def Real.liftProp : (f: CauchySeq -> Prop) -> (∀a b, a ≈ b -> (f a ↔ f b)) -> ℝ -> Prop := Equiv.liftProp
def Real.liftProp₂ : (f: CauchySeq -> CauchySeq -> Prop) -> (∀a b c d, a ≈ c -> b ≈ d -> (f a b ↔ f c d)) -> ℝ -> ℝ -> Prop := Equiv.liftProp₂
def Real.lift_mk : lift f all_eq (mk a) = f a := Equiv.lift_mk _ _ _
def Real.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := Equiv.lift₂_mk _ _ _ _
def Real.liftProp_mk : liftProp f all_eq (mk a) ↔ f a := Equiv.liftProp_mk _ _ _
def Real.liftProp₂_mk : liftProp₂ f all_eq (mk a) (mk b) ↔ f a b := Equiv.liftProp₂_mk _ _ _ _
def Real.exact : mk a = mk b -> a ≈ b := Equiv.exact _ _
def Real.sound : a ≈ b -> mk a = mk b := Equiv.sound _ _

def CauchySeq.ofRat (r: ℚ) : CauchySeq := by
  apply CauchySeq.mk (Function.const _ r)
  intro ε ε_pos
  exists 0
  intro k _
  unfold Function.const
  rw [Rat.sub.self, Rat.abs.zero]
  exact ε_pos

def Real.ofRat (r: ℚ) : ℝ := mk (CauchySeq.ofRat r)

instance : Coe ℚ ℝ := ⟨Real.ofRat⟩
instance : OfNat ℝ n := ⟨Real.ofRat (OfNat.ofNat n)⟩

def Real.coe.def (r: ℚ) : (↑r: ℝ) = ofRat r := rfl
def Real.ofNat.def (n: Nat) : (OfNat.ofNat n: ℝ) = ofRat (OfNat.ofNat n) := rfl

def Real.zero_eq : (0: ℚ) = (0: ℝ) := rfl
def Real.one_eq : (1: ℚ) = (1: ℝ) := rfl

def CauchySeq.add.spec (a b c d: CauchySeq):
  a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n + b n) (fun n => c n + d n) := by
  intro ac bd ε ε_pos
  have ⟨n,nprf⟩  := ac _ (Rat.half_pos ε_pos)
  have ⟨m,mprf⟩  := bd _ (Rat.half_pos ε_pos)
  exists max n m
  intro x y hx hy
  have ⟨_, _⟩ := max_le_iff.mp hx
  have ⟨_, _⟩ := max_le_iff.mp hy
  dsimp
  rw [Rat.sub.eq_add_neg, Rat.neg_add, Rat.add.assoc, Rat.add.comm_left (b x), ←Rat.add.assoc]
  apply lt_of_le_of_lt
  apply Rat.abs.add_le
  rw [Rat.half_sum ε]
  apply Rat.add.lt
  apply nprf <;> assumption
  apply mprf <;> assumption

def CauchySeq.add (a b: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => a n + b n)
  apply is_cauchy_iff_is_cauchy_equiv.mpr
  apply add.spec <;> trivial

def Real.add : ℝ -> ℝ -> ℝ := by
  apply Real.lift₂ (fun _ _ => mk _) _
  exact CauchySeq.add
  intro a b c d ac bd
  apply sound
  apply CauchySeq.add.spec <;> assumption

instance : Add CauchySeq := ⟨.add⟩
instance : Add ℝ := ⟨.add⟩
