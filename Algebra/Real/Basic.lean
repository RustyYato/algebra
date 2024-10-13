import Algebra.Rat.Order

def half_pos {ε: rat} : 0 < ε -> 0 < ε / 2 := by
  intro h
  rw [rat.div.def]
  apply rat.mul.pos_pos_is_pos
  assumption
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
