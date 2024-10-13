import Algebra.Rat.Order

def div_pos {ε k: rat} : 0 < ε -> 0 < k -> 0 < ε / k := by
  intro hε hk
  rw [rat.div.def]
  apply rat.mul.pos_pos_is_pos
  assumption
  apply rat.inv.pos
  trivial
def half_pos {ε: rat} : 0 < ε -> 0 < ε / 2 := by
  intro h
  apply div_pos h
  trivial
def half_sum (ε: rat) : ε = ε / 2 + ε / 2 := by
    rw [←rat.mul_two (ε / 2)]
    rw [rat.div.def, rat.mul.assoc, rat.mul.comm _ 2, rat.mul.inv_right, rat.mul.one_right]
    trivial

def is_cauchy (f: nat -> rat) : Prop :=
  ∀ε: rat, 0 < ε -> ∃n: nat, ∀k ≥ n, (f n - f k).abs < ε

def is_cauchy_equiv (f g: nat -> rat) : Prop :=
  ∀ε: rat, 0 < ε -> ∃n: nat, ∀x y, n ≤ x -> n ≤ y -> (f x - g y).abs < ε

def is_cauchy_iff_is_cauchy_equiv { f: nat -> rat } :
  is_cauchy f ↔ is_cauchy_equiv f f := by
  apply Iff.intro
  · intro c ε ε_pos
    have ⟨ n, prf ⟩ := c (ε / 2) (half_pos ε_pos)
    exists n
    intro x y n_le_x n_le_y
    rw [←rat.add.zero_left (_ - _), ←rat.sub.self (f n), rat.sub.def,
      rat.add.assoc, rat.sub.def, rat.add.comm_right (-f n),
      ←rat.add.assoc, ←rat.sub.def, ←rat.sub.def]
    apply lt_of_le_of_lt
    apply rat.abs.tri
    rw [half_sum ε]
    apply rat.add.lt_of_lt
    apply prf
    assumption
    rw [rat.abs.sub_symm]
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
  seq: nat -> rat
  seq_is_cauchy: is_cauchy seq

instance : CoeFun CauchySeq (fun _ => nat -> rat) where
  coe := CauchySeq.seq

-- marked noncomputable so that lean doesn't try to generate any code for this
noncomputable
def CauchySeq.max_to (s: CauchySeq) : nat -> rat
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
    apply max.ge_right
    subst h
    apply max.ge_left

def CauchySeq.bounded (s: CauchySeq) : ∃r: rat, ∀k, s k < r := by
  have ⟨ n, prf ⟩ := (is_cauchy_iff_is_cauchy_equiv.mp s.seq_is_cauchy) 1 (by decide)
  exists 1 + s.max_to n.succ
  intro k
  have := max_to.spec s n k
  cases lt_or_ge n k
  · rw [←rat.add.zero_left (s k), ←rat.sub.self (s n.succ),
      rat.sub.def, rat.add.right_comm, rat.add.assoc, ←rat.sub.def]
    apply lt_of_le_of_lt
    apply rat.add.le_of_le
    rfl
    have : s k - s n.succ ≤ (s k - s n.succ).abs := by
      rw [rat.abs.eq_max]
      apply max.ge_left
    exact this
    rw [rat.add.comm]
    apply rat.add_lt_of_lt_of_le
    rw [rat.abs.sub_symm]
    apply prf
    apply le_of_lt
    apply nat.lt_succ_self
    apply le_of_lt
    assumption
    apply max.ge_left
  · apply lt_of_le_of_lt
    apply this
    assumption
    apply lt_of_le_of_lt _ _
    exact 0 + s.max_to n.succ
    rw [rat.add.zero_left]
    apply max.ge_right
    apply rat.add_lt_of_lt_of_le
    trivial
    rfl

def CauchySeq.bounded' (s: CauchySeq) (x: rat) : ∃r > x, ∀k, s k < r := by
  have ⟨ r, prf ⟩  := s.bounded
  exists max r (x + 1)
  apply And.intro
  apply flip lt_of_lt_of_le
  apply max.ge_right
  conv => { lhs; rw [←rat.add.zero_right x] }
  apply rat.add.lt_of_add_left
  trivial
  intro k
  apply lt_of_lt_of_le
  apply prf
  apply max.ge_left

def CauchySeq.Equiv (a b: CauchySeq) := is_cauchy_equiv a.seq b.seq

instance CauchySeq.HasEquivInst : HasEquiv CauchySeq := ⟨ Equiv ⟩

@[refl]
def CauchySeq.Equiv.refl (a: CauchySeq) : a ≈ a := by
  apply is_cauchy_iff_is_cauchy_equiv.mp
  exact a.seq_is_cauchy

@[symm]
def CauchySeq.Equiv.symm {a b: CauchySeq} : a ≈ b -> b ≈ a := by
  intro ab ε ε_pos
  have ⟨ n, prf ⟩  := ab ε ε_pos
  exists n
  intro x y n_le_x n_le_y
  rw [rat.abs.sub_symm]
  apply prf <;> assumption

def CauchySeq.Equiv.trans {a b c: CauchySeq} : a ≈ b -> b ≈ c -> a ≈ c := by
  intro xy yz
  intro ε ε_pos
  have ⟨ nxy, prfxy ⟩  := xy (ε / 2) (half_pos ε_pos)
  have ⟨ nyz, prfyz ⟩  := yz (ε / 2) (half_pos ε_pos)
  exists max nxy nyz
  intro x y x_ge_max y_ge_max
  rw [←rat.add.zero_right (_ - _)]
  rw [←rat.sub.self (b.seq x)]
  rw [rat.sub.def, rat.sub.def, rat.add.assoc,
    rat.add.comm _ (-_),
    ←rat.add.assoc (-_),
    rat.add.comm _ (-_),
    ←rat.add.assoc,
    ←rat.add.assoc,
    rat.add.assoc _ (-_),
    rat.add.comm (-_)]
  rw [←rat.sub.def, ←rat.sub.def]
  apply lt_of_le_of_lt
  apply rat.abs.tri
  rw [half_sum ε]
  apply rat.add.lt_of_lt
  apply prfxy
  apply flip le_trans
  assumption
  apply max.ge_left
  apply le_trans _ x_ge_max
  apply max.ge_left
  apply prfyz
  apply flip le_trans
  assumption
  apply max.ge_right
  apply le_trans _ y_ge_max
  apply max.ge_right

instance CauchySeq.setoid : Setoid CauchySeq where
  r := Equiv
  iseqv := ⟨ Equiv.refl, Equiv.symm, Equiv.trans ⟩

def CauchySeq.equiv_def (a b: CauchySeq) : (a ≈ b) = is_cauchy_equiv a.seq b.seq := rfl

def real := Quotient CauchySeq.setoid

def real.mk : CauchySeq -> real := Quotient.mk CauchySeq.setoid
def real.ind : { motive: real -> Prop } -> (seq: ∀s, motive (mk s)) -> ∀r, motive r := Quotient.ind
def real.lift : (f: CauchySeq -> α) -> (∀a b, a ≈ b -> f a = f b) -> real -> α := Quotient.lift
def real.lift₂ : (f: CauchySeq -> CauchySeq -> α) -> (∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> real -> real -> α := Quotient.lift₂
def real.lift_mk : lift f all_eq (mk a) = f a := rfl
def real.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := rfl
def real.exact : mk a = mk b -> a ≈ b := Quotient.exact
def real.sound : a ≈ b -> mk a = mk b := Quotient.sound
def real.exists_rep : ∀r, ∃c, mk c = r := Quotient.exists_rep

def real.of_rat (r: rat) : real := by
  apply real.mk
  apply CauchySeq.mk (fun _ => r)
  intro ε ε_pos
  exists 0
  intro m _
  dsimp
  rw [rat.sub.self, rat.abs.zero]
  assumption

instance real.coe_rat : Coe rat real := ⟨ of_rat ⟩

def real.coe_eq_of_rat (r: rat) : ↑r = of_rat r := rfl

abbrev real.ofNat (n: Nat) : real := of_rat (rat.ofNat n)

instance real.ofNatInst : OfNat real n where
  ofNat := real.ofNat n

def real.zero_eq : 0 = of_rat 0 := rfl
def real.one_eq : 1 = of_rat 1 := rfl

def CauchySeq.Equiv.add (a b c d: CauchySeq) :
  a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n + b n) (fun n => c n + d n) := by
  intro ac bd
  intro ε ε_pos
  have ⟨ n, nprf ⟩ := ac (ε / 2) (half_pos ε_pos)
  have ⟨ m, mprf ⟩ := bd (ε / 2) (half_pos ε_pos)
  exists max n m
  intro x y max_le_x max_le_y
  dsimp
  rw [rat.sub.def, rat.neg.add, rat.add.assoc, rat.add.comm_left (b x), ←rat.add.assoc, ←rat.sub.def, ←rat.sub.def]
  apply lt_of_le_of_lt
  apply rat.abs.tri
  rw [half_sum ε]
  apply rat.add.lt_of_lt
  apply nprf
  apply le_trans _ max_le_x
  apply max.ge_left
  apply le_trans _ max_le_y
  apply max.ge_left
  apply mprf
  apply le_trans _ max_le_x
  apply max.ge_right
  apply le_trans _ max_le_y
  apply max.ge_right

def CauchySeq.add (a b: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => a n + b n)
  apply is_cauchy_iff_is_cauchy_equiv.mpr
  apply CauchySeq.Equiv.add <;> rfl

def real.add : real -> real -> real := by
  apply lift₂ (fun a b => mk _) _
  exact CauchySeq.add
  intro a b c d ac bd
  apply sound
  apply CauchySeq.Equiv.add <;> assumption

instance CauchySeq.AddInst : Add CauchySeq := ⟨ add ⟩
instance real.AddInst : Add real := ⟨ add ⟩

def real.of_rat.add (a b: rat) : of_rat a + of_rat b = of_rat (a + b) := rfl

def CauchySeq.Equiv.neg (a b: CauchySeq) :
  a ≈ b ->
  is_cauchy_equiv (fun n => -a n) (fun n => -b n) := by
  intro ab
  intro ε ε_pos
  dsimp only
  have ⟨ n, prf ⟩ := ab ε ε_pos
  exists n
  intro k k_ge_n
  rw [←rat.abs.neg, rat.neg.sub, rat.sub.def, rat.neg_neg, rat.add.comm, ←rat.sub.def]
  apply prf

def CauchySeq.neg (a: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => -a n)
  apply is_cauchy_iff_is_cauchy_equiv.mpr
  apply CauchySeq.Equiv.neg
  rfl

def real.neg : real -> real := by
  apply lift (fun _ => mk _) _
  exact CauchySeq.neg
  intro a b ab
  apply sound
  apply CauchySeq.Equiv.neg
  assumption

instance CauchySeq.NegInst : Neg CauchySeq := ⟨ neg ⟩
instance real.NegInst : Neg real := ⟨ neg ⟩

def real.of_rat.neg (a: rat) : -of_rat a = of_rat (-a) := rfl

instance CauchySeq.SubInst : Sub CauchySeq where
  sub a b := a + -b
instance real.SubInst : Sub real where
  sub a b := a + -b

def real.of_rat.sub (a b: rat) : of_rat a - of_rat b = of_rat (a - b) := rfl

def CauchySeq.Equiv.abs.helper_1 (a b: CauchySeq) :
  0 ≤ a.seq x ->
  b.seq y < 0 ->
  (a.seq x - b.seq y).abs < ε ->
  (a.seq x + b.seq y).abs < ε := by
  intro a_nonneg b_neg h
  rw [rat.abs.def] at *
  have b_lt_a := lt_of_lt_of_le b_neg a_nonneg
  split at h <;> rename_i h'
  · apply lt_of_le_of_lt _ h
    split <;> rename_i g
    · apply rat.add.le_of_add_left
      apply le_trans
      exact le_of_lt b_neg
      rw [←rat.neg.zero]
      apply rat.neg.swap_le
      exact le_of_lt b_neg
    · rw [←rat.neg.sub]
      apply rat.neg.swap_le
      rw [rat.add.comm, rat.sub.def]
      apply rat.add.le_of_add_left
      apply flip le_trans
      assumption
      rw [←rat.neg.zero]
      apply rat.neg.swap_le
      assumption
  · replace h' := lt_of_not_ge h'
    have : a x - b y + b y < 0 + b y := rat.add.lt_of_add_right h'
    rw [rat.sub.add_cancel, rat.add.zero_left] at this
    have := lt_antisymm b_lt_a this
    contradiction

def CauchySeq.Equiv.abs (a b: CauchySeq) :
  a ≈ b -> is_cauchy_equiv (fun n => (a n).abs) (fun n => (b n).abs) := by
  intro ab ε ε_pos
  dsimp
  have ⟨ n, prf ⟩ := ab ε ε_pos
  exists n
  intro x y n_le_x n_le_y
  rw [rat.abs.def (a x), rat.abs.def (b y)]
  have := prf x y n_le_x n_le_y
  split <;> rename_i ah <;> split <;> rename_i bh
  · assumption
  · rw [rat.sub.def, rat.neg_neg]
    apply abs.helper_1
    assumption
    apply lt_of_not_ge
    assumption
    assumption
  · rw [rat.sub.def, ←rat.neg.add, rat.abs.neg]
    rw [rat.add.comm]
    apply abs.helper_1
    assumption
    apply lt_of_not_ge
    assumption
    rw [rat.abs.sub_symm]
    assumption
  · rw [←rat.abs.neg, rat.sub.def, rat.neg.add, rat.neg_neg, rat.neg_neg, ←rat.sub.def]
    assumption

def CauchySeq.abs (a: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => (a n).abs)
  apply is_cauchy_iff_is_cauchy_equiv.mpr
  apply CauchySeq.Equiv.abs
  rfl

def real.abs : real -> real := by
  apply lift (fun _ => mk _) _
  exact CauchySeq.abs
  intro a b ab
  apply sound
  apply CauchySeq.Equiv.abs
  assumption

def CauchySeq.Equiv.mul (a b c d: CauchySeq):
  a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n * b n) (fun n => c n * d n) := by
  intro ac bd ε ε_pos

  have ⟨ amax, amax_gt_one, amaxprf ⟩ := a.abs.bounded' 1
  have ⟨ dmax, dmax_gt_one, dmaxprf ⟩ := d.abs.bounded' 1

  let L := max amax dmax
  have : 0 < L := by
    apply flip lt_of_le_of_lt
    apply max.gt
    apply Or.inl amax_gt_one
    trivial
  let ε₀: rat := ε / (2 * dmax)
  let ε₁: rat := ε / (2 * amax)

  have ε₀_pos : 0 < ε₀ := by
    apply div_pos ε_pos
    apply rat.mul.pos_pos_is_pos
    trivial
    apply lt_trans _ dmax_gt_one
    trivial
  have ε₁_pos : 0 < ε₁ := by
    apply div_pos ε_pos
    apply rat.mul.pos_pos_is_pos
    trivial
    apply lt_trans _ amax_gt_one
    trivial

  have ⟨ n, nprf ⟩ := ac ε₀ ε₀_pos
  have ⟨ m, mprf ⟩ := bd ε₁ ε₁_pos

  exists max n m
  intro x y max_le_x max_le_y
  dsimp

  -- = |a b - c d + a d - a d|
  -- = |a b - a d - c d + a d|
  -- = |a b - a d + a d - c d|
  -- = |a (b - d) + (a - c) d|
  -- ≤ |a (b - d)| + |(a - c) d|
  -- = |a| |(b - d)| + |(a - c)| |d|
  -- < amax ε/(2 amax) + (ε/(2 dmax)) dmax
  -- = ε/2 + ε/2
  -- = ε

  rw [←rat.add.zero_right (_ - _), ←rat.sub.self (a x * d y),
    rat.sub.def, rat.sub.def, rat.add.assoc,
    rat.add.comm_right (-_),
    ←rat.add.assoc,
    ←rat.sub.def, ←rat.sub.def,
    ←rat.sub.mul_left, ←rat.sub.mul_right]
  apply lt_of_le_of_lt
  apply rat.abs.tri
  rw [half_sum ε]
  apply rat.add.lt_of_lt
  · rw [rat.abs.mul]
    apply lt_of_le_of_lt
    apply rat.mul.le_nonneg_left
    apply le_of_lt
    apply mprf
    apply le_trans _ max_le_x
    apply max.ge_right
    apply le_trans _ max_le_y
    apply max.ge_right
    apply rat.abs.nonneg
    apply lt_of_lt_of_le (_: _ < amax * ε₁) _
    apply flip (rat.mul.lt_pos_right _ _ _)
    assumption
    apply amaxprf
    dsimp [ε₁]
    rw [←rat.div_div ε, rat.mul.div_cancel]
    intro
    subst amax
    contradiction
  · rw [rat.abs.mul]
    apply lt_of_le_of_lt
    apply rat.mul.le_nonneg_right
    apply le_of_lt
    apply nprf
    apply le_trans _ max_le_x
    apply max.ge_left
    apply le_trans _ max_le_y
    apply max.ge_left
    apply rat.abs.nonneg
    apply lt_of_lt_of_le (_: _ < ε₀ * dmax) _
    apply flip (rat.mul.lt_pos_left _ _ _)
    assumption
    apply dmaxprf
    dsimp [ε₀]
    rw [←rat.div_div ε, rat.mul.comm, rat.mul.div_cancel]
    intro
    subst dmax
    contradiction

def CauchySeq.mul (a b: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => a n * b n) _
  apply is_cauchy_iff_is_cauchy_equiv.mpr
  apply CauchySeq.Equiv.mul <;> rfl

def real.mul : real -> real -> real := by
  apply lift₂ (fun _ _ => mk _) _
  exact CauchySeq.mul
  intro a b c d ab cd
  apply sound
  apply CauchySeq.Equiv.mul <;> assumption

instance CauchySeq.MulInst : Mul CauchySeq := ⟨ mul ⟩
instance real.MulInst : Mul real := ⟨ mul ⟩

def real.of_rat.mul (a b: rat) : of_rat a * of_rat b = of_rat (a * b) := rfl
