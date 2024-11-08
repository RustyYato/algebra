import Algebra.Rat.Defs
import Algebra.Equiv
import Algebra.ClassicLogic

def CauchySeq.Eventually (P: nat -> Prop) : Prop := ∃k, ∀n, k ≤ n -> P n
def CauchySeq.Eventually₂ (P: nat -> nat -> Prop) : Prop := ∃k, ∀n m, k ≤ n -> k ≤ m -> P n m

def CauchySeq.is_cauchy (f: nat -> Rat) : Prop :=
  ∀ε: Rat, 0 < ε -> ∃n: nat, ∀k ≥ n, ‖f n - f k‖ < ε

def CauchySeq.is_cauchy_equiv (f g: nat -> Rat) : Prop :=
  ∀ε: Rat, 0 < ε -> Eventually₂ fun x y => ‖f x - g y‖ < ε

def CauchySeq.Eventually.to₂ : Eventually a -> Eventually₂ fun i _ => a i := by
  intro ⟨i,hi⟩
  exists i
  intro n _ hn _
  apply hi; assumption

def CauchySeq.Eventually.merge : Eventually a -> Eventually b -> Eventually fun i => a i ∧ b i := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  exists max i j
  intro n hn
  apply And.intro
  apply hi
  apply le_trans _ hn
  apply le_max_left
  apply hj
  apply le_trans _ hn
  apply le_max_right

def CauchySeq.Eventually₂.merge : Eventually₂ a -> Eventually₂ b -> Eventually₂ fun i j => a i j ∧ b i j := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  exists max i j
  intro m n hm hn
  apply And.intro
  apply hi
  apply le_trans _ hm
  apply le_max_left
  apply le_trans _ hn
  apply le_max_left
  apply hj
  apply le_trans _ hm
  apply le_max_right
  apply le_trans _ hn
  apply le_max_right

def CauchySeq.is_cauchy_iff_is_cauchy_equiv { f: nat -> Rat } :
  is_cauchy f ↔ is_cauchy_equiv f f := by
  unfold is_cauchy is_cauchy_equiv
  apply Iff.intro
  · intro c ε ε_pos
    have ⟨ n, prf ⟩ := c _ (Rat.half_pos ε_pos)
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
  seq_is_cauchy: CauchySeq.is_cauchy_equiv seq seq

def CauchySeq.mk' (seq: nat -> Rat) (h: is_cauchy seq) := by
  apply CauchySeq.mk seq
  apply is_cauchy_iff_is_cauchy_equiv.mp
  assumption

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
  have ⟨ n, prf ⟩ := s.seq_is_cauchy 1 (by decide)
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
  have ⟨ r, prf ⟩ := s.upper_bound
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
def CauchySeq.refl (a: CauchySeq) : a ≈ a := a.seq_is_cauchy

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
  have ⟨o,oprf⟩ := b.seq_is_cauchy _ (Rat.half_pos (Rat.half_pos ε_pos))
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
  have : ε = ε /? 2 + ε /? 2 /? 2 + ε /? 2 /? 2 := by rw [Rat.add.assoc, ←Rat.half_sum, ←Rat.half_sum]
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
def Real.liftProp' : (f: CauchySeq -> Prop) -> (∀a b, a ≈ b -> f a -> f b) -> ℝ -> Prop := by
  intro f h
  apply liftProp f
  intro a b ab
  apply Iff.intro
  exact h _ _ ab
  exact h _ _ (CauchySeq.symm ab)
def Real.liftProp₂' : (f: CauchySeq -> CauchySeq -> Prop) -> (∀a b c d, a ≈ c -> b ≈ d -> f a b -> f c d) -> ℝ -> ℝ -> Prop := by
  intro f h
  apply liftProp₂ f
  intro a b c d ab cd
  apply Iff.intro
  exact h _ _ _ _ ab cd
  exact h _ _ _ _ (CauchySeq.symm ab) (CauchySeq.symm cd)
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
  intros
  unfold Function.const
  rw [Rat.sub.self, Rat.abs.zero]
  exact ε_pos

def Real.ofRat (r: ℚ) : ℝ := mk (CauchySeq.ofRat r)

instance : Coe ℚ ℝ := ⟨Real.ofRat⟩
instance : OfNat ℝ n := ⟨Real.ofRat (OfNat.ofNat n)⟩
instance : OfNat CauchySeq n := ⟨CauchySeq.ofRat (OfNat.ofNat n)⟩

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
  rw [Rat.sub.eq_add_neg, Rat.neg_add, Rat.add.assoc, Rat.add.comm_left (b x), ←Rat.add.assoc]
  apply lt_of_le_of_lt
  apply Rat.abs.add_le
  rw [Rat.half_sum ε]
  apply Rat.add.lt
  apply nprf <;> assumption
  apply mprf <;> assumption

def CauchySeq.add (a b: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => a n + b n)
  apply add.spec <;> trivial

def Real.add : ℝ -> ℝ -> ℝ := by
  apply Real.lift₂ (fun _ _ => mk _) _
  exact CauchySeq.add
  intro a b c d ac bd
  apply sound
  apply CauchySeq.add.spec <;> assumption

instance : Add CauchySeq := ⟨.add⟩
instance : Add ℝ := ⟨.add⟩

def Real.mk_add (a b: CauchySeq) : mk a + mk b = mk (a + b) := lift₂_mk
def Real.ofRat.add (a b: ℚ) : (a + b: ℝ) = ((a + b): ℚ) := lift₂_mk

def CauchySeq.add.def (a b: CauchySeq) : a + b = a.add b := rfl

def CauchySeq.neg.spec (a b: CauchySeq):
  a ≈ b ->
  is_cauchy_equiv (fun n => -a n) (fun n => -b n) := by
  intro ab ε ε_pos
  have ⟨n,nprf⟩  := ab _ ε_pos
  exists n
  intro x y hx hy
  dsimp
  rw [←Rat.abs.neg, Rat.sub.eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.neg_neg, ←Rat.sub.eq_add_neg]
  apply nprf <;> assumption

def CauchySeq.neg (a: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => -a n)
  apply neg.spec <;> trivial

def Real.neg : ℝ -> ℝ := by
  apply Real.lift (fun _ => mk _) _
  exact CauchySeq.neg
  intro a b ab
  apply sound
  apply CauchySeq.neg.spec <;> assumption

instance : Neg CauchySeq := ⟨.neg⟩
instance : Neg ℝ := ⟨.neg⟩

def Real.mk_neg (a: CauchySeq) : -mk a = mk (-a) := lift_mk
def Real.ofRat.neg (a: ℚ) : (-a: ℝ) = ((-a): ℚ) := lift_mk

def CauchySeq.neg.def (a: CauchySeq) : -a = a.neg := rfl

def CauchySeq.neg_neg (a: CauchySeq) : - -a ≈ a := by
  rw [neg.def, neg.def]
  unfold neg
  dsimp
  intro ε ε_pos
  dsimp
  have ⟨n,prf⟩ := a.seq_is_cauchy ε ε_pos
  exists n
  intro x y _ _
  rw [Rat.neg_neg]
  apply prf <;> assumption

instance : Sub CauchySeq where
  sub a b := a + -b
instance : Sub ℝ where
  sub a b := a + -b

def CauchySeq.sub.eq_add_neg (a b: CauchySeq) : a - b = a + -b := rfl
def Real.sub.eq_add_neg (a b: ℝ) : a - b = a + -b := rfl

def Real.mk_sub (a b: CauchySeq) : mk a - mk b = mk (a - b) := by
  rw [sub.eq_add_neg, mk_neg, mk_add]
  rfl

def Real.ofRat.sub (a b: ℚ) : (a - b: ℝ) = ((a - b): ℚ) := mk_sub _ _

def CauchySeq.lower_bound (s: CauchySeq) : ∃r: Rat, ∀k, r < s k := by
  have ⟨r,prf⟩  := (-s).upper_bound
  exists -r
  intro k
  apply Rat.neg.swap_lt.mpr
  rw [Rat.neg_neg]
  apply prf

def CauchySeq.lower_bound_with (s: CauchySeq) (x: Rat) : ∃r < x, ∀k, r < s k := by
  have ⟨r,prf⟩ := (-s).upper_bound_with (-x)
  exists -r
  apply And.intro
  apply Rat.neg.swap_lt.mpr
  rw [Rat.neg_neg]
  apply prf.left
  intro k
  apply Rat.neg.swap_lt.mpr
  rw [Rat.neg_neg]
  apply prf.right

def CauchySeq.IsPos (a: CauchySeq) := ∃B > 0, Eventually fun n => B ≤ a n
def CauchySeq.IsNeg (a: CauchySeq) := ∃B < 0, Eventually fun n => a n ≤ B

instance : LT CauchySeq where
  lt a b := (a - b).IsPos

def CauchySeq.shifted (a: CauchySeq) (x: nat) : CauchySeq := by
  apply CauchySeq.mk' (fun n => a (n + x))
  intro ε ε_pos
  have ⟨n,prf⟩ := a.seq_is_cauchy ε ε_pos
  exists n - x
  intro k hk
  dsimp
  apply prf
  by_cases h:n ≤ x
  rw [nat.sub.eq_zero.mpr, nat.zero_add]
  assumption
  assumption
  replace h := lt_of_not_le h
  rw [nat.sub_add_inv]
  apply le_of_lt
  assumption
  by_cases h:n ≤ x
  apply le_trans h
  apply nat.add.le_right
  replace h := lt_of_not_le h
  have := nat.add.of_le_cancel_left x (n - x) k hk
  rw [nat.add.comm]
  rw [nat.add.comm, nat.sub_add_inv] at this
  assumption
  apply le_of_lt; assumption

def CauchySeq.sub.eq_zero_of_equiv {a b: CauchySeq} : a ≈ b ↔ a - b ≈ 0 := by
  apply Iff.intro
  intro ab ε ε_pos
  have ⟨n,prf⟩ := ab ε ε_pos
  exists n
  intro x y hx _
  erw [Rat.sub_zero,]
  apply prf <;> assumption
  intro ab ε ε_pos
  have ⟨n,prf⟩ := ab _ (Rat.half_pos ε_pos)
  have ⟨n₀,n₀prf⟩ := a.seq_is_cauchy _ (Rat.half_pos ε_pos)
  have ⟨n₁,n₁prf⟩ := b.seq_is_cauchy _ (Rat.half_pos ε_pos)
  exists max n (max n₀ n₁)
  intro x y hx hy
  replace ⟨hx,hx₀⟩ := max_le_iff.mp hx
  replace ⟨hx₀,hx₁⟩ := max_le_iff.mp hx₀
  replace ⟨hy,hy₀⟩ := max_le_iff.mp hy
  replace ⟨hy₀,hy₁⟩ := max_le_iff.mp hy₀
  have x': ‖(a x - b x) - 0‖ < _ := prf _ _ hx hy
  have y': ‖(a y - b y) - 0‖ < _ := prf _ _ hy hx
  rw [Rat.sub_zero] at x' y'
  apply (Rat.mul.lt_mul_pos (k := ‖2: ℚ‖) (by decide)).mpr
  have : ‖2:ℚ‖ = 2 := rfl
  rw [Rat.abs.mul, Rat.mul.comm, Rat.two_mul, this, Rat.mul.comm _ 2]
  rw [←Rat.add_zero (_ + _), ←Rat.sub.self (b x + a y)]
  repeat first|rw [Rat.sub.eq_add_neg]|rw [Rat.add.neg]
  repeat rw [Rat.add.assoc]

  repeat first|rw [Rat.add.comm _ (-b x)]|rw [←Rat.add.assoc]
  rw [Rat.add.comm (-b x), ←Rat.sub.eq_add_neg (a x)]
  repeat rw [Rat.add.assoc]
  apply lt_of_le_of_lt
  apply Rat.abs.add_le

  repeat first|rw [Rat.add.comm _ (a y)]|rw [←Rat.add.assoc]
  rw [←Rat.sub.eq_add_neg (a y)]
  repeat rw [Rat.add.assoc]
  apply lt_of_le_of_lt
  apply Rat.add.le; rfl
  apply Rat.abs.add_le

  repeat first|rw [Rat.add.comm _ (-a y)]|rw [←Rat.add.assoc]
  rw [Rat.add.comm (-a y), ←Rat.sub.eq_add_neg (a x)]
  repeat rw [Rat.add.assoc]
  apply lt_of_le_of_lt
  apply Rat.add.le; rfl
  apply Rat.add.le; rfl
  apply Rat.abs.add_le

  rw [Rat.add.comm _ (b x), ←Rat.sub.eq_add_neg]
  have : 2 * ε = ε /? 2 + ε /? 2 + ε /? 2 + ε /? 2 := by
    rw [←Rat.two_mul, Rat.add.assoc, ←Rat.two_mul, ←Rat.two_mul, Rat.mul_div_cancel]
  rw [this]
  repeat rw [←Rat.add.assoc]
  apply Rat.add.lt
  apply Rat.add.lt
  apply Rat.add.lt
  exact x'
  exact y'
  apply n₀prf
  assumption
  assumption
  apply n₁prf
  assumption
  assumption

def Real.sub_zero (a: ℝ) : a - a = 0 := by
  induction a using ind with | mk a =>
  rw [mk_sub]
  apply sound
  apply CauchySeq.sub.eq_zero_of_equiv.mp
  rfl

def Real.of_sub_zero (a b: ℝ) : a - b = 0 -> a = b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_sub]
  intro h
  apply sound
  apply CauchySeq.sub.eq_zero_of_equiv.mpr
  exact exact h

def CauchySeq.IsPos.spec (a b: CauchySeq) : a ≈ b -> a.IsPos -> b.IsPos := by
  intro ab ⟨A,A_pos,a₀,ha₀⟩
  exists A /? 2
  apply And.intro (Rat.half_pos A_pos) _
  have ⟨n,nprf⟩ := ab _ (Rat.half_pos A_pos)
  exists max a₀ n
  intro k hk
  have ⟨a₀_le_k,n_le_k⟩ := max_le_iff.mp hk
  -- apply le_trans _ (Rat.sub.le_left_pos (b k) ‖a k - b k‖ (Rat.abs.zero_le _))
  dsimp at ha₀
  by_cases h:a.seq k ≤ b.seq k
  apply le_trans
  apply le_of_lt
  apply Rat.div.lt_pos A 2
  assumption
  decide
  apply le_trans (ha₀ k a₀_le_k) h
  replace h := lt_of_not_le h
  have := Rat.add.le (ha₀ k (a₀_le_k)) (le_of_lt (Rat.neg.swap_lt.mp (nprf _ _ n_le_k n_le_k)))
  conv at this  in A + _ => { lhs; rw [Rat.half_sum A] }
  rw [Rat.add.assoc, ←Rat.sub.eq_add_neg, Rat.sub.self,
    Rat.add_zero, Rat.abs.of_zero_le.mp, Rat.sub.neg, Rat.sub.eq_add_neg, Rat.add.comm_left,
    ←Rat.sub.eq_add_neg, Rat.sub.self, Rat.add_zero] at this
  exact this
  apply Rat.add.le_left.mpr
  rw [Rat.sub_add_cancel, Rat.zero_add]
  apply le_of_lt
  assumption

def CauchySeq.not_IsPos_and_IsNeg (x: CauchySeq) : x.IsPos -> x.IsNeg -> False := by
  intro ⟨a,a_pos,ak,aprf⟩ ⟨b,b_neg,bk,bprf⟩
  dsimp at *
  have a' := aprf (max ak bk) (le_max_left _ _)
  have b' := bprf (max ak bk) (le_max_right _ _)
  have a_le_b := le_trans a' b'
  have := lt_of_le_of_lt a_le_b b_neg
  exact lt_asymm a_pos this

def CauchySeq.neg.IsPos {a: CauchySeq} : a.IsPos ↔ (-a).IsNeg := by
  apply Iff.intro
  intro ⟨B,B_pos,a,ha⟩
  exists -B
  apply And.intro
  apply Rat.neg.swap_lt.mpr
  rw [Rat.neg_neg]
  assumption
  exists a
  intro n a_le_n
  apply Rat.neg.swap_le.mp
  apply ha _ a_le_n

  intro ⟨B,B_neg,a,ha⟩
  exists -B
  apply And.intro
  apply Rat.neg.swap_lt.mpr
  rw [Rat.neg_neg]
  assumption
  exists a
  intro n a_le_n
  apply Rat.neg.swap_le.mpr
  rw [Rat.neg_neg]
  apply ha _ a_le_n

def CauchySeq.neg.IsNeg {a: CauchySeq} : a.IsNeg ↔ (-a).IsPos := by
  apply Iff.intro
  intro ⟨B,B_pos,a,ha⟩
  exists -B
  apply And.intro
  apply Rat.neg.swap_lt.mpr
  rw [Rat.neg_neg]
  assumption
  exists a
  intro n a_le_n
  apply Rat.neg.swap_le.mp
  apply ha _ a_le_n

  intro ⟨B,B_neg,a,ha⟩
  exists -B
  apply And.intro
  apply Rat.neg.swap_lt.mpr
  rw [Rat.neg_neg]
  assumption
  exists a
  intro n a_le_n
  apply Rat.neg.swap_le.mpr
  rw [Rat.neg_neg]
  apply ha _ a_le_n

def CauchySeq.IsNeg.spec (a b: CauchySeq) : a ≈ b -> a.IsNeg -> b.IsNeg := by
  intro ab a_neg
  have : -a ≈ -b := neg.spec a b ab
  apply neg.IsNeg.mpr
  exact (neg.IsNeg.mp a_neg).spec _ this

def Real.IsPos : ℝ -> Prop := by
  apply liftProp' CauchySeq.IsPos
  apply CauchySeq.IsPos.spec

def Real.IsNeg : ℝ -> Prop := by
  apply liftProp' CauchySeq.IsNeg
  apply CauchySeq.IsNeg.spec

def Real.mk_IsPos (a: CauchySeq) : (mk a).IsPos ↔ a.IsPos := liftProp_mk
def Real.mk_IsNeg (a: CauchySeq) : (mk a).IsNeg ↔ a.IsNeg := liftProp_mk

def CauchySeq.abs.proof1 (a b: Rat) :
  0 ≤ a -> b ≤ 0 -> ‖a - b‖ < ε -> ‖a + b‖ < ε := by
  intro ha hb habs
  cases lt_or_eq_of_le hb <;> rename_i hb
  apply lt_of_le_of_lt _ habs
  apply Rat.abs.add_le_sub
  intro h
  have := h.mp ha
  exact lt_irrefl <| lt_of_le_of_lt (h.mp ha) hb
  subst b
  rw [Rat.sub_zero] at habs
  rw [Rat.add_zero]
  assumption

def CauchySeq.abs.spec (a : CauchySeq) :
  a ≈ b ->
  is_cauchy_equiv (fun n => ‖a n‖) (fun n => ‖b n‖)
  := by
  intro ab ε ε_pos
  dsimp
  have ⟨n,prf⟩ := ab _ (Rat.half_pos ε_pos)
  exists n
  intro x y hx hy
  rw [Rat.abs.eq_max (a x), Rat.abs.eq_max (b y)]
  rw [max_def, max_def]
  split <;> split <;> rename_i h g
  rw [←Rat.add.neg, ←Rat.sub.eq_add_neg, Rat.abs.neg]
  apply lt_trans
  apply prf <;> assumption
  apply Rat.div.lt_pos ε 2
  assumption
  decide
  rw [←Rat.add.neg, Rat.abs.neg]
  rw [Rat.add.comm]
  apply abs.proof1
  apply Rat.zero_le_iff_neg_le.mpr
  apply le_of_lt
  apply lt_of_not_le
  assumption
  apply Rat.le_zero_iff_le_neg.mpr
  assumption
  rw [Rat.abs.sub_comm]
  apply lt_trans
  apply prf <;> assumption
  apply Rat.div.lt_pos
  assumption
  decide
  rw [Rat.sub_neg]
  apply abs.proof1
  apply Rat.zero_le_iff_neg_le.mpr
  apply le_of_lt
  apply lt_of_not_le
  assumption
  apply Rat.le_zero_iff_le_neg.mpr
  assumption
  apply lt_trans
  apply prf <;> assumption
  apply Rat.div.lt_pos
  assumption
  decide
  apply lt_trans
  apply prf <;> assumption
  apply Rat.div.lt_pos
  assumption
  decide

def CauchySeq.abs (a: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => ‖a n‖)
  apply abs.spec
  rfl

def Real.abs : ℝ -> ℝ := by
  apply lift (mk ∘ CauchySeq.abs)
  intros
  apply sound
  apply CauchySeq.abs.spec
  assumption

instance : AbsoluteValue CauchySeq CauchySeq := ⟨CauchySeq.abs⟩
instance : AbsoluteValue ℝ ℝ := ⟨Real.abs⟩

theorem CauchySeq.abv_pos_of_non_zero {f : CauchySeq} (hf : ¬f ≈ 0) :
    ∃ K > 0, Eventually fun j => K ≤ ‖f j‖ := by
  haveI := ClassicLogic.propDecide
  apply ClassicLogic.byContradiction
  intro nk
  refine hf fun ε ε_pos => ?_
  replace nk : ∀ (x : ℚ), 0 < x → ∀ (x_1 : nat), ∃ x_2, ∃ (_ : x_1 ≤ x_2), ‖f x_2‖ < x := by
    intro x hx n
    have nk := not_exists.mp (not_and.mp (not_exists.mp nk x) hx) n
    have ⟨m,prf⟩ := ClassicLogic.not_forall.mp nk
    have ⟨hm,prf⟩  := ClassicLogic.not_imp.mp prf
    exists m
    exists hm
    apply lt_of_not_le
    assumption

  have ⟨i,hi⟩ := f.seq_is_cauchy _ (Rat.half_pos ε_pos)
  rcases nk _ (Rat.half_pos ε_pos) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k _ jk _ => ?_⟩
  have : ∀y, seq 0 y = 0 := fun _ => rfl
  dsimp
  rw [this, Rat.sub_zero]
  have := lt_of_le_of_lt (Rat.abs.add_le _ _) (Rat.add.lt (hi k j (le_trans ij jk) ij) hj)
  rwa [Rat.sub_add_cancel, ←Rat.half_sum] at this

def CauchySeq.IsPos_or_IsNeg_of_non_zero {a: CauchySeq} (h: ¬a ≈ 0) : a.IsPos ∨ a.IsNeg := by
  have ⟨K, K_pos, even⟩ := abv_pos_of_non_zero h
  have ⟨i,hi⟩  := Eventually₂.merge even.to₂ (a.seq_is_cauchy K K_pos)
  rcases le_total 0 (a i) with apos | aneg
  · apply Or.inl
    refine ⟨K,K_pos,i,?_⟩
    intro j ij
    have ⟨this,_⟩ := hi j i ij (le_refl _)
    have ⟨h₁,h₂⟩ := hi i j (le_refl _) ij
    rwa [Rat.abs.of_zero_le.mp] at this
    rw [Rat.abs.of_zero_le.mp apos] at h₁
    apply Rat.add.of_le_left_pos
    apply le_trans h₁
    apply (Rat.add.le_left (k := -K)).mpr
    rw [Rat.add.right_comm _ _ (-K), Rat.add_neg_self, Rat.zero_add]
    rw [Rat.abs.sub_comm] at h₂
    have ⟨h₃, _⟩ := Rat.abs.lt_iff.mp h₂
    apply (Rat.add.le_right (k := -a.seq i)).mpr
    rw [←Rat.add.assoc, Rat.neg_self_add, Rat.zero_add]
    apply le_of_lt
    rw [Rat.add.comm, ←Rat.sub.eq_add_neg]
    assumption
  · apply Or.inr
    refine ⟨-K,Rat.neg.swap_lt.mp K_pos,i,?_⟩
    intro j ij
    have ⟨this,_⟩ := hi j i ij (le_refl _)
    have ⟨h₁,h₂⟩ := hi i j (le_refl _) ij
    apply Rat.neg.swap_le.mpr; rw [Rat.neg_neg]
    rwa [Rat.abs.of_le_zero.mp] at this
    rw [Rat.abs.of_le_zero.mp aneg] at h₁
    apply Rat.neg.swap_le.mpr
    apply Rat.add.of_le_left_pos
    apply le_trans h₁
    apply (Rat.add.le_left (k := -K)).mpr
    rw [Rat.add.right_comm _ _ (-K), Rat.add_neg_self, Rat.zero_add]
    have ⟨h₃, _⟩ := Rat.abs.lt_iff.mp h₂
    apply (Rat.add.le_right (k := a.seq i)).mpr
    rw [←Rat.add.assoc, Rat.add_neg_self, Rat.zero_add]
    apply le_of_lt
    rw [←Rat.sub.eq_add_neg]
    assumption

def CauchySeq.invert.spec (a b: CauchySeq) (ha: ¬a ≈ 0) (hb: ¬b ≈ 0) :
  a ≈ b -> is_cauchy_equiv (fun n => if h:a n ≠ 0 then (a n)⁻¹ else 0) (fun n => if h:b n ≠ 0 then (b n)⁻¹ else 0) := by
  revert a b

  suffices ∀a b: CauchySeq, ¬a ≈ 0 -> ¬b ≈ 0 -> a ≈ b -> a.IsPos -> is_cauchy_equiv (fun n => if h:a n ≠ 0 then (a n)⁻¹ else 0) (fun n => if h:b n ≠ 0 then (b n)⁻¹ else 0) by
    intro a b ha hb ab
    rcases IsPos_or_IsNeg_of_non_zero ha with apos | aneg
    apply this <;> assumption
    intro ε ε_pos
    have ⟨i,prf⟩ := this (-a) (-b) (by
      intro  h₀
      apply ha
      apply Real.exact
      rw [←Real.sound (neg_neg a), ←Real.mk_neg, Real.sound h₀, Real.mk_neg]
      rfl) (by
      intro  h₀
      apply hb
      apply Real.exact
      rw [←Real.sound (neg_neg b), ←Real.mk_neg, Real.sound h₀, Real.mk_neg]
      rfl) (neg.spec a b ab) (neg.IsNeg.mp aneg) ε ε_pos
    dsimp at prf
    exists i
    intro x y hx hy
    dsimp
    replace prf := prf x y hx hy
    split at prf <;> split at prf <;> rename_i h g
    · rw [dif_pos, dif_pos]
      unfold Neg.neg instNegCauchySeq neg at prf
      dsimp at prf
      rw [←Rat.neg_inv _ (by
        intro h₀
        apply h
        suffices -a x = 0 from this
        rw [h₀]
        rfl), ←Rat.neg_inv _ (by
        intro h₀
        apply g
        suffices -b y = 0 from this
        rw [h₀]
        rfl), Rat.neg_sub_neg, Rat.abs.sub_comm] at prf
      exact prf
    · rw [dif_pos, dif_neg]
      unfold Neg.neg instNegCauchySeq neg at prf
      dsimp at prf
      rw [←Rat.neg_inv _ (by
        intro h₀
        apply h
        suffices -a x = 0 from this
        rw [h₀]
        rfl), Rat.sub_zero, Rat.abs.neg] at prf
      rw [Rat.sub_zero]
      exact prf
      intro g₀
      apply g
      intro g
      apply g₀
      have g : -b y = 0 := g
      rw [←Rat.neg_neg (b y), g]
      rfl
    · rw [dif_neg, dif_pos]
      rw [Rat.zero_sub, Rat.abs.neg]
      rw [Rat.zero_sub] at prf
      have prf : ‖-(-b y)⁻¹‖ < ε := prf
      rw [←Rat.neg_inv _ (by
        intro g₀
        apply g
        suffices -b y = 0 from this
        rw [g₀]
        rfl), Rat.neg_neg] at prf
      exact prf
      intro h₀
      apply h
      intro h
      apply h₀
      have h : -a x = 0 := h
      rw [←Rat.neg_neg (a x), h]
      rfl
    · rw [dif_neg, dif_neg]
      exact ε_pos

      intro g₀
      apply g
      intro g
      apply g₀
      have g : -b y = 0 := g
      rw [←Rat.neg_neg (b y), g]
      rfl

      intro h₀
      apply h
      intro h
      apply h₀
      have h : -a x = 0 := h
      rw [←Rat.neg_neg (a x), h]
      rfl
  intro a b ha hb
  intro ab apos
  have bpos := apos.spec b ab
  intro ε ε_pos
  dsimp
  rcases apos with ⟨Ka,Ka_pos,evena⟩
  rcases bpos with ⟨Kb,Kb_pos,evenb⟩
  have acau := a.seq_is_cauchy ε ε_pos
  have bcau := b.seq_is_cauchy ε ε_pos
  have ab := ab (Ka * Kb * ε) (by
    apply Rat.mul.pos
    apply Rat.mul.pos
    repeat assumption)
  have even := Eventually.merge evena evenb
  have cau := Eventually₂.merge acau bcau
  have ⟨i,prf⟩  := (Eventually₂.merge even.to₂ cau).merge ab
  clear acau bcau evena evenb even cau
  exists i
  intro n m hn hm
  have ⟨_,_⟩ := prf n m hn hm
  have ⟨⟨⟨Kah,Kbh'⟩,acau,bcau⟩,ab⟩ := prf n m hn hm
  have ⟨⟨⟨Kah,Kbh⟩,acau,bcau⟩,ab⟩ := prf m n hm hn
  clear Kah Kbh' acau bcau ab prf
  rw [dif_pos, dif_pos, Rat.inv_sub_inv, Rat.div.eq_mul_inv, ←Rat.abs.mul]
  rw [Rat.mul.inv, ←Rat.abs.mul]
  rw [Rat.mul.comm]
  apply lt_of_le_of_lt
  apply Rat.mul.le_left_pos _
  apply Rat.mul.le_left_pos (b := Ka⁻¹) _
  rw [Rat.abs.of_zero_le.mp]
  · apply (Rat.inv.swap_le _ _ _ _ _).mp Kah
    symm
    apply ne_of_lt
    apply lt_of_lt_of_le Ka_pos
    assumption
    apply Iff.intro <;> intro g
    apply le_trans
    apply le_of_lt Ka_pos
    assumption
    exact le_of_lt Ka_pos
  apply (Rat.mul.le_mul_pos _).mpr
  rw [Rat.inv_self_mul, Rat.zero_mul]
  trivial
  apply lt_of_lt_of_le Ka_pos
  assumption
  intro h
  rw [h] at Kbh
  exact lt_irrefl <| lt_of_lt_of_le Kb_pos Kbh
  apply Rat.abs.zero_le
  apply Rat.abs.zero_le
  rw [Rat.mul.comm (Ka⁻¹)]
  apply lt_of_le_of_lt
  apply Rat.mul.le_left_pos _
  apply Rat.mul.le_left_pos (b := Kb⁻¹) _
  rw [Rat.abs.of_zero_le.mp]
  · apply (Rat.inv.swap_le _ _ _ _ _).mp Kbh
    apply Iff.intro <;> intro g
    apply le_trans
    apply le_of_lt Kb_pos
    assumption
    apply le_of_lt Kb_pos
  apply Rat.inv.zero_le_iff.mp
  apply le_trans
  apply le_of_lt Kb_pos
  assumption
  apply Rat.inv.zero_le_iff.mp
  apply le_of_lt Ka_pos
  apply Rat.abs.zero_le
  rw [Rat.mul.comm]
  apply lt_of_lt_of_le
  apply (Rat.mul.lt_mul_pos _).mp
  rw [Rat.abs.sub_comm]
  apply ab
  apply Rat.mul.pos
  apply Rat.inv.zero_lt_iff.mp
  assumption
  apply Rat.inv.zero_lt_iff.mp
  assumption
  rw [Rat.mul.assoc, Rat.mul.comm, Rat.mul.assoc ε, Rat.mul.comm Ka,
    ←Rat.mul.inv, Rat.inv_self_mul, Rat.mul_one]
  intro h
  rw [h] at Kah
  exact lt_irrefl <| lt_of_lt_of_le Ka_pos Kah
  intro h
  rw [h] at Kbh
  exact lt_irrefl <| lt_of_lt_of_le Kb_pos Kbh

def CauchySeq.invert (c: CauchySeq) (h: ¬c ≈ 0) : CauchySeq := by
  apply CauchySeq.mk (fun n => if h:c n ≠ 0 then (c n)⁻¹ else 0)
  apply CauchySeq.invert.spec
  assumption
  assumption
  rfl

def Real.invert (x: ℝ) (h: x ≠ 0) : ℝ := by
  apply Equiv.liftWith (· ≠ (0: ℝ)) (fun _ _ => mk _) _ _ h
  intro x h
  apply x.invert
  intro h₀
  apply h
  exact sound h₀
  intro a b ab ha hb
  apply sound
  apply CauchySeq.invert.spec
  intro h₀; apply ha; exact sound h₀
  intro h₀; apply hb; exact sound h₀
  assumption

instance : Invert CauchySeq (¬· ≈ 0) := ⟨CauchySeq.invert⟩
instance : Invert ℝ (· ≠ 0) := ⟨Real.invert⟩

def Real.non_zero_of_cauchy {a: CauchySeq} : ¬a ≈ 0 -> mk a ≠ 0 := by
  intro g
  intro h
  apply g
  exact exact h

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Real.non_zero_of_cauchy <;> invert_tactic)

def Real.mk_invert (a: CauchySeq) (ha: ¬a ≈ 0) : (mk a)⁻¹ = mk (a⁻¹) := Equiv.liftWith_mk
