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

def Real.neg_neg (a: ℝ) : - -a = a := by
  induction a using ind with | mk a =>
  rw [mk_neg, mk_neg]
  apply sound
  apply CauchySeq.neg_neg

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

def Real.mk_abs (a: CauchySeq) : ‖mk a‖ = mk ‖a‖ := lift_mk

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

def CauchySeq.invert.spec_of_pos : ∀a b: CauchySeq, a ≈ b -> a.IsPos ->
  is_cauchy_equiv (fun n => if h:a n ≠ 0 then (a n)⁻¹ else 0) (fun n => if h:b n ≠ 0 then (b n)⁻¹ else 0) := by
  intro a b
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
    apply Iff.intro <;> intro
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
    apply Iff.intro <;> intro
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

def CauchySeq.invert.spec (a b: CauchySeq) (ha: ¬a ≈ 0) :
  a ≈ b -> is_cauchy_equiv (fun n => if h:a n ≠ 0 then (a n)⁻¹ else 0) (fun n => if h:b n ≠ 0 then (b n)⁻¹ else 0) := by
  intro ab
  rcases IsPos_or_IsNeg_of_non_zero ha with apos | aneg
  apply invert.spec_of_pos <;> assumption
  intro ε ε_pos
  have ⟨i,prf⟩ := invert.spec_of_pos (-a) (-b) (neg.spec a b ab) (neg.IsNeg.mp aneg) ε ε_pos
  refine ⟨i,?_⟩
  intro x y hx hy
  dsimp at prf
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

def CauchySeq.invert (c: CauchySeq) (h: ¬c ≈ 0) : CauchySeq := by
  apply CauchySeq.mk (fun n => if h:c n ≠ 0 then (c n)⁻¹ else 0)
  apply CauchySeq.invert.spec
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
  assumption

instance : Invert CauchySeq (¬· ≈ 0) := ⟨CauchySeq.invert⟩
instance : Invert ℝ (· ≠ 0) := ⟨Real.invert⟩

def CauchySeq.invert.def  (a: CauchySeq) (h: ¬a ≈ 0) : a⁻¹ = a.invert h := rfl

def Real.non_zero_of_cauchy {a: CauchySeq} : ¬a ≈ 0 -> mk a ≠ 0 := by
  intro g
  intro h
  apply g
  exact exact h

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Real.non_zero_of_cauchy <;> invert_tactic)

def Real.non_zero_of_nat (n: Nat) : OfNat.ofNat (n + 1) ≠ (0: ℝ) := by
  intro h
  have ⟨i,prf⟩ := exact h 1 (by decide)
  replace prf := prf i i (le_refl _) (le_refl _)
  unfold CauchySeq.ofRat at prf
  dsimp at prf
  rw [Rat.sub_zero] at prf
  rw [Rat.abs.of_zero_le.mp] at prf
  have := Rat.ofNat.of_lt_one _ prf
  contradiction
  apply Rat.ofNat.zero_le

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Real.non_zero_of_nat)

def Real.mk_inv (a: CauchySeq) (ha: ¬a ≈ 0) : (mk a)⁻¹ = mk (a⁻¹) := Equiv.liftWith_mk

def CauchySeq.mul.spec (a b c d: CauchySeq) :
  a ≈ c -> b ≈ d -> is_cauchy_equiv (fun n => a n * b n) (fun n => c n * d n) := by
  intro ac bd ε ε_pos
  have ⟨amax,one_lt_amax,amax_spec⟩ := ‖a‖.upper_bound_with 1
  have ⟨dmax,one_lt_dmax,dmax_spec⟩ := ‖d‖.upper_bound_with 1

  have amax_pos : 0 < amax := lt_of_le_of_lt (by decide) one_lt_amax
  have dmax_pos : 0 < dmax := lt_of_le_of_lt (by decide) one_lt_dmax

  let ε₀ := (ε /? 2) /? dmax
  let ε₁ := (ε /? 2) /? amax

  have ε₀_pos : 0 < ε₀ := by
    apply Rat.div.pos
    apply Rat.div.pos
    assumption
    decide
    assumption
  have ε₁_pos : 0 < ε₁ := by
    apply Rat.div.pos
    apply Rat.div.pos
    assumption
    decide
    assumption

  have ⟨an,an_prf⟩ := ac _ ε₀_pos
  have ⟨bn,bn_prf⟩ := bd _ ε₁_pos

  exists max an bn
  intro x y hx hy
  have ⟨_,_⟩ := max_le_iff.mp hx
  have ⟨_,_⟩ := max_le_iff.mp hy

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

  rw [←Rat.add_zero (_ - _), ←Rat.neg_self_add (a x * d y),
    Rat.sub.eq_add_neg, Rat.add.assoc, Rat.add.comm_left (-_),
    ←Rat.add.assoc, Rat.add.comm (-_), ←Rat.sub.eq_add_neg,
    ←Rat.sub.eq_add_neg, ←Rat.mul_sub, ←Rat.sub_mul]
  apply lt_of_le_of_lt
  apply Rat.abs.add_le
  rw [←Rat.abs.mul, ←Rat.abs.mul]
  rw [Rat.half_sum ε]
  apply Rat.add.lt
  apply lt_of_le_of_lt
  apply Rat.mul.le_left_pos
  apply Rat.abs.zero_le
  apply le_of_lt
  apply amax_spec
  rw [Rat.mul.comm]
  apply lt_of_lt_of_le
  apply (Rat.mul.lt_mul_pos _).mp
  apply bn_prf <;> assumption
  assumption
  rw [Rat.mul.comm, Rat.mul_div_cancel]
  rw [Rat.mul.comm]
  apply lt_of_le_of_lt
  apply Rat.mul.le_left_pos
  apply Rat.abs.zero_le
  apply le_of_lt
  apply dmax_spec
  rw [Rat.mul.comm]
  apply lt_of_lt_of_le
  apply (Rat.mul.lt_mul_pos _).mp
  apply an_prf <;> assumption
  assumption
  rw [Rat.mul.comm, Rat.mul_div_cancel]

def CauchySeq.mul (a b: CauchySeq) : CauchySeq := by
  apply CauchySeq.mk (fun n => a n * b n)
  apply mul.spec <;> rfl

def Real.mul : ℝ -> ℝ -> ℝ := by
  apply lift₂ (fun _ _ => mk _) _
  exact CauchySeq.mul
  intro a b c d ac bd
  apply sound
  apply CauchySeq.mul.spec <;> assumption

instance : Mul CauchySeq := ⟨.mul⟩
instance : Mul ℝ := ⟨.mul⟩

def Real.mk_mul (a b: CauchySeq) : mk a * mk b = mk (a * b) := lift₂_mk

def CauchySeq.mul.def (a b: CauchySeq) : a * b = a.mul b := rfl

instance : CheckedDiv CauchySeq (¬· ≈ 0) where
  checked_div a b h := a * b⁻¹
instance : CheckedDiv ℝ (· ≠ 0) where
  checked_div a b h := a * b⁻¹

def CauchySeq.div.eq_mul_inv (a b: CauchySeq) (h: ¬b ≈ 0) : a /? b = a * b⁻¹ := rfl
def Real.div.eq_mul_inv (a b: ℝ) (h: b ≠ 0) : a /? b = a * b⁻¹ := rfl

def Real.mk_div (a b: CauchySeq) (h: ¬b ≈ 0) : mk a /? mk b = mk (a /? b) := by
  rw [CauchySeq.div.eq_mul_inv, div.eq_mul_inv, mk_inv, mk_mul]

def CauchySeq.equiv_of_pointwise (a b: CauchySeq) : (∀n, a n = b n) -> a ≈ b := by
  intro h ε ε_pos
  have ⟨i, prf⟩  := a.seq_is_cauchy ε ε_pos
  exists i
  intro n m _ _
  rw [←h]
  apply prf <;> assumption

def CauchySeq.equiv_of_pointwise_after (a b: CauchySeq) (k: nat) : (∀n, k ≤ n -> a n = b n) -> a ≈ b := by
  intro h ε ε_pos
  have ⟨i, prf⟩  := a.seq_is_cauchy ε ε_pos
  exists max i k
  intro n m hn hm
  have ⟨_,_⟩ := max_le_iff.mp hn
  have ⟨_,_⟩ := max_le_iff.mp hm
  rw [←h]
  apply prf <;> assumption
  assumption

def CauchySeq.mul.comm (a b: CauchySeq) : a * b ≈ b * a := by
  rw [mul.def, mul.def]
  unfold mul
  apply CauchySeq.equiv_of_pointwise
  intro n
  dsimp
  rw [Rat.mul.comm]

def Real.mul.comm (a b: ℝ) : a * b = b * a := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_mul, mk_mul]
  apply sound
  apply CauchySeq.mul.comm

def CauchySeq.mul.assoc (a b c: CauchySeq) : a * b * c ≈ a * (b * c) := by
  repeat rw [mul.def]
  unfold mul
  apply CauchySeq.equiv_of_pointwise
  intro n
  dsimp
  rw [Rat.mul.assoc]

def Real.mul.assoc (a b c: ℝ) : a * b * c = a * (b * c) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction c using ind with | mk c =>
  repeat rw [mk_mul]
  apply sound
  apply CauchySeq.mul.assoc

def CauchySeq.add.comm (a b: CauchySeq) : a + b ≈ b + a := by
  rw [add.def, add.def]
  unfold add
  apply CauchySeq.equiv_of_pointwise
  intro n
  dsimp
  rw [Rat.add.comm]

def Real.add.comm (a b: ℝ) : a + b = b + a := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_add, mk_add]
  apply sound
  apply CauchySeq.add.comm

def CauchySeq.add.assoc (a b c: CauchySeq) : a + b + c ≈ a + (b + c) := by
  repeat rw [add.def]
  unfold add
  apply CauchySeq.equiv_of_pointwise
  intro n
  dsimp
  rw [Rat.add.assoc]

def Real.add.assoc (a b c: ℝ) : a + b + c = a + (b + c) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction c using ind with | mk c =>
  repeat rw [mk_add]
  apply sound
  apply CauchySeq.add.assoc

def Real.mul.right_comm (a b c: ℝ) :
  a * b * c = a * c * b := by rw [Real.mul.assoc, Real.mul.comm b, Real.mul.assoc]

def Real.mul.left_comm (a b c: ℝ) :
  a * b * c = c * b * a := by rw [Real.mul.comm _ c, Real.mul.comm a, Real.mul.assoc]

def Real.mul.comm_left (a b c: ℝ) :
  a * (b * c) = b * (a * c) := by
  rw [←Real.mul.assoc, ←Real.mul.assoc, Real.mul.comm a]

def Real.mul.comm_right (a b c: ℝ) :
  a * (b * c) = c * (b * a) := by
  rw [Real.mul.comm _ c, Real.mul.comm a, Real.mul.assoc]

def Real.add.right_comm (a b c: ℝ) :
  a + b + c = a + c + b := by rw [Real.add.assoc, Real.add.comm b, Real.add.assoc]

def Real.add.left_comm (a b c: ℝ) :
  a + b + c = c + b + a := by rw [Real.add.comm _ c, Real.add.comm a, Real.add.assoc]

def Real.add.comm_left (a b c: ℝ) :
  a + (b + c) = b + (a + c) := by
  rw [←Real.add.assoc, ←Real.add.assoc, Real.add.comm a]

def Real.add.comm_right (a b c: ℝ) :
  a + (b + c) = c + (b + a) := by
  rw [Real.add.comm _ c, Real.add.comm a, Real.add.assoc]

def CauchySeq.inv_self_mul (a: CauchySeq) (h: ¬a ≈ 0) : a⁻¹ * a ≈ 1 := by
  rw [invert.def, mul.def]
  unfold invert mul
  dsimp
  intro ε ε_pos
  have ⟨K,K_pos,even⟩ := abv_pos_of_non_zero h
  have ⟨i,prf⟩ := even.to₂.merge (a.seq_is_cauchy ε ε_pos)
  exists i
  intro n m hn hm
  replace ⟨K_le_absseq, prf⟩ := prf n m hn hm
  dsimp
  rw [dif_pos]
  rw [Rat.inv_self_mul]
  have : seq 1 m = 1 := rfl
  rw [this, Rat.sub.self]
  exact ε_pos
  intro h
  rw [Rat.abs.eq_max] at K_le_absseq
  rw [h] at K_le_absseq
  have K_nonpos : K ≤ 0 := K_le_absseq
  have := lt_of_lt_of_le K_pos K_nonpos
  contradiction

def Real.inv_self_mul (a: ℝ) (h: a ≠ 0) : a⁻¹ * a = 1 := by
  induction a using ind with | mk a =>
  rw [mk_inv, mk_mul]
  apply sound
  apply CauchySeq.inv_self_mul
  intro g
  apply h
  apply sound
  assumption

def Real.mul_inv_self (a: ℝ) (h: a ≠ 0) : a * a⁻¹ = 1 := by
  rw [mul.comm]
  apply inv_self_mul

def Real.div.self (a: ℝ) (h: a ≠ 0) : a /? a = 1 := by
  rw [div.eq_mul_inv, mul_inv_self]

def Real.mul_div.assoc (a b c: ℝ) (h: c ≠ 0) : a * (b /? c) = (a * b) /? c := by
  rw [div.eq_mul_inv, div.eq_mul_inv, mul.assoc]

def Real.mul_div.comm (a b c: ℝ) (h: c ≠ 0) : a * (b /? c) = b * (a /? c) := by
  rw [div.eq_mul_inv, div.eq_mul_inv, mul.comm_left]

def CauchySeq.neg_self_add (a: CauchySeq) : -a + a ≈ 0 := by
  apply equiv_of_pointwise
  intro n
  suffices -a n + a n = 0 from this
  rw [Rat.neg_self_add]

def Real.neg_self_add (a: ℝ) : -a + a = 0 := by
  induction a using ind with | mk a =>
  rw [mk_neg, mk_add]
  apply sound
  apply CauchySeq.neg_self_add

def Real.add_neg_self (a: ℝ) : a + -a = 0 := by
  rw [add.comm, neg_self_add]

def Real.sub.self (a: ℝ) : a - a = 0 := by
  rw [sub.eq_add_neg, add_neg_self]

instance : Max ℝ where
  max a b := (a + b + ‖a - b‖) /? 2

instance : Min ℝ where
  min a b := (a + b - ‖a - b‖) /? 2

def Real.sub.neg (a b: ℝ) : -(a - b) = b - a := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_sub, mk_sub, mk_neg]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  suffices -(a n - b n) = b n - a n from this
  rw [Rat.sub.neg]

def Real.add.neg (a b: ℝ) : -(a + b) = -a + -b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_neg, mk_neg, mk_add, mk_add, mk_neg]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  show -(a n + b n) = -a n + -b n
  rw [Rat.add.neg, Rat.sub.eq_add_neg]

def Real.add.eq_iff_left {a b k: ℝ} : a = b ↔ a + k = b + k := by
  apply Iff.intro
  intro h
  rw [h]
  intro h
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction k using ind with | mk k =>
  apply sound
  rw [mk_add, mk_add] at h
  replace h := exact h
  intro ε ε_pos
  have ⟨i, prf⟩ := (k.seq_is_cauchy _ (Rat.half_pos ε_pos)).merge (h _ (Rat.half_pos ε_pos))
  exists i
  intro n m hn hm
  replace prf := prf n m hn hm
  dsimp at prf
  have : ∀a b: CauchySeq, ∀n: nat, (a + b) n = a n + b n := fun _ _ _ => rfl
  rw [this, this] at prf
  clear this
  replace ⟨kprf,prf⟩ := prf
  rw [Rat.sub.eq_add_neg, Rat.add.neg,
    Rat.sub.eq_add_neg, Rat.add.assoc,
    Rat.add.comm_left (k _),
    ←Rat.add.assoc, ←Rat.sub.eq_add_neg,
    ←Rat.sub.eq_add_neg] at prf
  rw [←Rat.add_zero (_ - _), ←Rat.sub.self (k n - k m),
    Rat.sub.eq_add_neg (k _ - k _),
    ←Rat.add.assoc, Rat.half_sum ε]
  apply lt_of_le_of_lt
  apply Rat.abs.add_le
  apply Rat.add.lt
  assumption
  rw [Rat.abs.neg]
  assumption

def Real.sub_add.comm (a b c: ℝ) : a - b + c = c - b + a := by
  rw [sub.eq_add_neg, sub.eq_add_neg, add.left_comm]
def Real.add_sub.comm (a b c: ℝ) : a + (b - c) = b + (a - c) := by
  rw [sub.eq_add_neg, sub.eq_add_neg, add.comm_left]

def Real.neg.zero : -0 = (0: ℝ) := by
  erw [mk_neg]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  rfl

def Real.zero_add (a: ℝ) : 0 + a = a := by
  induction a using ind with | mk a =>
  erw [mk_add]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  suffices 0 + a n = a n from this
  rw [Rat.zero_add]

def Real.add_zero (a: ℝ) : a + 0 = a := by
  rw [add.comm, zero_add]

def Real.one_mul (a: ℝ) : 1 * a = a := by
  induction a using ind with | mk a =>
  erw [mk_mul]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  suffices 1 * a n = a n from this
  rw [Rat.one_mul]

def Real.mul_one (a: ℝ) : a * 1 = a := by
  rw [mul.comm, one_mul]

def Real.zero_mul (a: ℝ) : 0 * a = 0 := by
  induction a using ind with | mk a =>
  erw [mk_mul]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  suffices 0 * a n = 0 from this
  rw [Rat.zero_mul]

def Real.mul_zero (a: ℝ) : a * 0 = 0 := by
  rw [mul.comm, zero_mul]

def Real.sub_zero (a: ℝ) : a - 0 = a := by
  rw [sub.eq_add_neg, neg.zero, add_zero]

def Real.zero_sub (a: ℝ) : 0 - a = -a := by
  rw [sub.eq_add_neg, zero_add]

def Real.not_pos_and_neg (a: ℝ) : a.IsPos -> a.IsNeg -> False := by
  intro h g
  induction a using ind with | mk a =>
  apply CauchySeq.not_IsPos_and_IsNeg a
  apply (mk_IsPos _).mp
  assumption
  apply (mk_IsNeg _).mp
  assumption

def Real.neg.IsPos {a: ℝ} : a.IsPos ↔ (-a).IsNeg := by
  induction a using ind with | mk a =>
  rw [mk_neg]
  apply Iff.trans (mk_IsPos _)
  apply Iff.trans _ (mk_IsNeg _).symm
  apply CauchySeq.neg.IsPos

def Real.neg.IsNeg {a: ℝ} : a.IsNeg ↔ (-a).IsPos := by
  induction a using ind with | mk a =>
  rw [mk_neg]
  apply Iff.trans (mk_IsNeg _)
  apply Iff.trans _ (mk_IsPos _).symm
  apply CauchySeq.neg.IsNeg

def Real.zero_not_pos : ¬(0: ℝ).IsPos := by
  intro h
  replace ⟨K,K_pos,i,h⟩ : CauchySeq.IsPos 0 := (mk_IsPos _).mp h
  have : K ≤ 0 := h i (le_refl _)
  exact lt_irrefl <| lt_of_le_of_lt this K_pos

def Real.zero_not_neg : ¬(0: ℝ).IsNeg := by
  intro h
  replace ⟨K,K_pos,i,h⟩ : CauchySeq.IsNeg 0 := (mk_IsNeg _).mp h
  have : 0 ≤ K := h i (le_refl _)
  exact lt_irrefl <| lt_of_le_of_lt this K_pos

def Real.pos_or_neg_of_non_zero (a: ℝ) (h: a ≠ 0) : a.IsPos ∨ a.IsNeg := by
  induction a using ind with | mk a =>
  have : ¬a ≈ 0 := by
    intro g
    apply h
    apply sound
    assumption
  rcases CauchySeq.IsPos_or_IsNeg_of_non_zero this with pos | neg
  apply Or.inl
  apply (mk_IsPos _).mpr
  assumption
  apply Or.inr
  apply (mk_IsNeg _).mpr
  assumption

def Real.add.pos (a b: ℝ) : a.IsPos -> b.IsPos -> (a + b).IsPos := by
  intro apos bpos
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  replace apos := (mk_IsPos _).mp apos
  replace bpos := (mk_IsPos _).mp bpos
  rw [mk_add]
  apply (mk_IsPos _).mpr
  rcases apos with ⟨Ka,Ka_pos,Kaeven⟩
  rcases bpos with ⟨Kb,Kb_pos,Kbeven⟩
  have ⟨i,prf⟩ := Kaeven.merge Kbeven
  exists Ka + Kb
  apply And.intro
  apply Rat.add.is_pos <;> assumption
  exists i
  intro n hn
  replace prf := prf n hn
  obtain ⟨Kah,Kbh⟩ := prf
  apply Rat.add.le <;> assumption

instance : LT CauchySeq where
  lt a b := (b - a).IsPos

instance : LT ℝ where
  lt a b := (b - a).IsPos

instance : LE CauchySeq where
  le a b := a < b ∨ a ≈ b

instance : LE ℝ where
  le a b := a < b ∨ a = b

def Real.mk_lt {a b: CauchySeq} : mk a < mk b ↔ a < b := by
  unfold LT.lt instLTReal instLTCauchySeq
  dsimp
  rw [mk_sub]
  apply mk_IsPos

def Real.two_eq : (2: ℝ) = 1 + 1 := by
  erw [mk_add]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro
  rfl

def Real.mul_add (a b k: ℝ) : k * (a + b) = k * a + k * b := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction k using ind with | mk k =>
  repeat first|rw [mk_add]|rw [mk_mul]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  show (k n * (a n + b n) = k n * a n + k n * b n)
  rw [Rat.mul_add]

def Real.add_mul (a b k: ℝ) : (a + b) * k = a * k + b * k := by
  repeat rw [mul.comm _ k]
  rw [mul_add]

def Real.sub_neg (a b: ℝ) : a - -b = a + b := by
  rw [sub.eq_add_neg, neg_neg]

def Real.two_mul (a: ℝ) : 2 * a = a + a := by
  rw [two_eq, add_mul, one_mul]

instance Real.IsLinearOrder'Inst : IsLinearOrder' ℝ where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    · intro h
      apply And.intro
      apply Or.inl
      assumption
      intro g
      rcases g with b_lt_a | b_eq_a
      replace h : (b - a).IsPos := h
      replace b_lt_a : (a - b).IsPos := b_lt_a
      apply not_pos_and_neg _ h
      apply neg.IsNeg.mpr
      rw [sub.neg]
      assumption
      subst b
      replace h : (a - a).IsPos := h
      rw [sub.self] at h
      have := zero_not_pos
      contradiction
    · rintro ⟨h₀,h₁⟩
      rcases h₀ with a_lt_b | a_eq_b
      assumption
      subst b
      have := h₁ (.inr rfl)
      contradiction
  le_total := by
    intro a b
    apply ClassicLogic.byCases (a = b)
    intro h
    apply Or.inl
    subst b
    exact .inr rfl
    intro h
    replace h : b - a ≠ 0 := by
      intro g
      apply h
      have := (add.eq_iff_left (k := a)).mp g
      rw [sub_add.comm, sub.self, zero_add, zero_add] at this
      symm
      assumption
    rcases pos_or_neg_of_non_zero _ h with pos | neg
    exact .inl (.inl pos)
    have := Real.neg.IsNeg.mp neg
    rw [sub.neg] at this
    exact .inr (.inl this)
  le_complete := by
    intro a b
    apply ClassicLogic.byCases (a = b)
    intro h
    apply Or.inl
    subst b
    exact .inr rfl
    intro h
    replace h : b - a ≠ 0 := by
      intro g
      apply h
      have := (add.eq_iff_left (k := a)).mp g
      rw [sub_add.comm, sub.self, zero_add, zero_add] at this
      symm
      assumption
    rcases pos_or_neg_of_non_zero _ h with pos | neg
    exact .inl (.inl pos)
    have := Real.neg.IsNeg.mp neg
    rw [sub.neg] at this
    apply Or.inr
    intro g
    rcases g with a_lt_b | a_eq_b
    exact not_pos_and_neg _ a_lt_b neg
    subst b
    rw [sub.self] at h
    contradiction
  le_trans := by
    intro a b c ab bc
    rcases ab with a_lt_b | a_eq_b
    rcases bc with b_lt_c | b_eq_c
    · apply Or.inl
      suffices (c - a).IsPos from this
      rw [←add_zero (c - a), ←sub.self b, sub.eq_add_neg, sub.eq_add_neg,
        add.assoc, add.comm_right (-a), ←add.assoc, ←sub.eq_add_neg, ←sub.eq_add_neg]
      apply add.pos
      exact b_lt_c
      exact a_lt_b
    · subst b
      apply Or.inl
      assumption
    · subst b
      assumption
  le_antisymm := by
    intro a b ab ba
    rcases ab with ab | _
    rcases ba with ba | _
    exfalso
    apply not_pos_and_neg
    exact ab
    apply neg.IsNeg.mpr
    rw [sub.neg]
    assumption
    symm
    assumption
    assumption

def Real.abs.of_zero_le (a: ℝ) : 0 ≤ a -> ‖a‖ = a := by
  intro h
  cases h
  · rename_i h
    induction a using ind with | mk a =>
    have ⟨K,K_pos,i,prf⟩ := mk_lt.mp h
    rw [mk_abs]
    apply sound
    apply CauchySeq.equiv_of_pointwise_after _ _ i
    intro n hn
    dsimp at prf
    have := prf n hn
    show ‖a n‖ = a n
    rw [Rat.abs.of_zero_le.mp]
    apply le_trans
    exact le_of_lt K_pos
    have : K ≤ (a n - 0) := this
    erw [Rat.sub_zero] at this
    exact this
  · subst a
    erw [Real.mk_abs]
    apply sound
    apply CauchySeq.equiv_of_pointwise
    intro n
    rfl

def Real.abs.neg (a: ℝ) : ‖-a‖ = ‖a‖ := by
  induction a using ind with | mk a =>
  rw [mk_neg, mk_abs, mk_abs]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  show ‖-a n‖ = ‖a n‖
  rw [Rat.abs.neg]

def Real.add.lt {a b k: ℝ} : a < b ↔ a + k < b + k := by
  apply Iff.intro
  intro h
  show (b + k - (a + k)).IsPos
  rw [sub.eq_add_neg, add.neg, add.assoc, add.comm_left k,
    add_neg_self, add_zero, ←sub.eq_add_neg]
  exact h
  intro h
  show (b - a).IsPos
  rw [←add_zero (_ - _), ←add_neg_self k, sub.eq_add_neg, add.assoc, add.comm_left (-a),
    ←add.assoc, ←add.neg, ←sub.eq_add_neg]
  exact h

def Real.add.le {a b k: ℝ} : a ≤ b ↔ a + k ≤ b + k := by
  apply Iff.intro
  intro h
  rcases h with a_lt_b | a_eq_b
  apply le_of_lt
  apply add.lt.mp
  assumption
  rw [a_eq_b]
  intro h
  rcases h with a_lt_b | a_eq_b
  apply Or.inl
  apply add.lt.mpr
  assumption
  rw [add.eq_iff_left.mpr a_eq_b]

def Real.abs.of_le_zero (a: ℝ) : a ≤ 0 -> ‖a‖ = -a := by
  intro h
  rw [←abs.neg]
  apply abs.of_zero_le
  apply add.le.mpr
  rw [neg_self_add, zero_add]
  assumption

def Real.abs.def (a: ℝ) : ‖a‖ = a ∨ ‖a‖ = -a := by
  cases le_total a 0
  rw [abs.of_le_zero]
  apply Or.inr rfl
  assumption
  rw [abs.of_zero_le]
  apply Or.inl rfl
  assumption

instance Real.IsLinearOrderInst : IsLinearOrder ℝ where
  min_iff_le_left := by
    intro a b
    apply Iff.intro
    intro ab
    unfold min instMinReal
    dsimp
    rw [Real.abs.of_le_zero, sub_neg, add.assoc, add_sub.comm b,
      ←add.assoc, sub.self, add_zero, ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one]
    rcases ab with ab | ab
    apply Or.inl
    suffices (0 - (a - b)).IsPos from this
    rw [zero_sub, sub.neg]
    exact ab
    subst b
    rw [sub.self]
    intro min_eq_a
    unfold min instMinReal at min_eq_a
    dsimp at min_eq_a
    rcases lt_or_le b a with ab | ba
    rw [abs.of_zero_le, sub.eq_add_neg, sub.neg, sub.eq_add_neg,
      add.assoc, add.comm_right b, ←add.assoc, add_neg_self, zero_add,
      ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one] at min_eq_a
    subst a
    rfl
    apply Or.inl
    suffices ((a - b) - 0).IsPos from this
    rw [sub_zero]
    exact ab
    assumption
  min_iff_le_right := by
    intro a b
    apply Iff.intro
    intro ba
    unfold min instMinReal
    dsimp
    rw [Real.abs.of_zero_le, sub.eq_add_neg, sub.neg, sub.eq_add_neg,
      add.assoc, add.comm_right b, ←add.assoc, add_neg_self, zero_add,
      ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one]
    rcases ba with ba | ab
    apply Or.inl
    suffices ((a - b) - 0).IsPos from this
    rw [sub_zero]
    exact ba
    subst b
    rw [sub.self]
    intro min_eq_a
    unfold min instMinReal at min_eq_a
    dsimp at min_eq_a
    rcases lt_or_le a b with ab | ba
    rw [Real.abs.of_le_zero, sub_neg, sub.eq_add_neg, add.assoc,
      add.comm_left b, ←add.assoc, add_neg_self, add_zero,
      ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one] at min_eq_a
    subst a
    rfl
    apply Or.inl
    suffices (0 - (a - b)).IsPos from this
    rw [zero_sub, sub.neg]
    exact ab
    assumption
  max_iff_le_left := by
    intro a b
    apply Iff.intro
    intro ba
    unfold max instMaxReal
    dsimp
    rw [Real.abs.of_le_zero, sub.neg, add.assoc, sub.eq_add_neg,
      add.comm_right b, ←add.assoc, add_neg_self, zero_add,
      ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one]
    rcases ba with ba | ab
    apply Or.inl
    suffices (0 - (a - b)).IsPos from this
    rw [zero_sub, sub.neg]
    exact ba
    subst b
    rw [sub.self]
    intro min_eq_a
    unfold max instMaxReal at min_eq_a
    dsimp at min_eq_a
    rcases lt_or_le b a with ab | ba
    rw [Real.abs.of_zero_le, sub.eq_add_neg,
      add.assoc, add.comm_left b, ←add.assoc, add_neg_self, add_zero,
      ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one] at min_eq_a
    subst a
    rfl
    apply Or.inl
    suffices ((a - b) - 0).IsPos from this
    rw [sub_zero]
    exact ab
    assumption
  max_iff_le_right := by
    intro a b
    apply Iff.intro
    intro ab
    unfold max instMaxReal
    dsimp
    rw [Real.abs.of_zero_le, sub.eq_add_neg,
      add.assoc, add.comm_left b, ←add.assoc, add_neg_self, add_zero,
      ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one]
    rcases ab with ab | ab
    apply Or.inl
    suffices ((a - b) - 0).IsPos from this
    rw [sub_zero]
    exact ab
    subst b
    rw [sub.self]
    intro min_eq_a
    unfold max instMaxReal at min_eq_a
    dsimp at min_eq_a
    rcases lt_or_le a b with ab | ba
    rw [Real.abs.of_le_zero, sub.neg, add.assoc, sub.eq_add_neg,
      add.comm_right b, ←add.assoc, add_neg_self, zero_add,
      ←two_mul, mul.comm, ←mul_div.assoc, div.self, mul_one] at min_eq_a
    subst a
    rfl
    apply Or.inl
    suffices (0 - (a - b)).IsPos from this
    rw [zero_sub, sub.neg]
    exact ab
    assumption

def Real.mul_neg (a b: ℝ) : a * -b = -(a * b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_neg, mk_mul, mk_mul, mk_neg]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  show (a n * -b n = -(a n * b n))
  rw [Rat.mul_neg]

def Real.neg_mul (a b: ℝ) : -a * b = -(a * b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_neg, mk_mul, mk_mul, mk_neg]
  apply sound
  apply CauchySeq.equiv_of_pointwise
  intro n
  show (-a n * b n = -(a n * b n))
  rw [Rat.neg_mul]

def Real.mul.pos_of_pos_pos (a b: ℝ) : a.IsPos -> b.IsPos -> (a * b).IsPos := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  intro apos bpos
  rw [mk_mul]
  apply (mk_IsPos _).mpr
  replace apos := (mk_IsPos _).mp apos
  replace bpos := (mk_IsPos _).mp bpos
  obtain ⟨Ka,Ka_pos,Ka_even⟩ := apos
  obtain ⟨Kb,Kb_pos,Kb_even⟩ := bpos
  have ⟨i,prf⟩ := Ka_even.merge Kb_even
  exists Ka * Kb
  apply And.intro
  apply Rat.mul.is_pos_of_pos_pos <;> assumption
  exists i
  intro n hn
  replace prf := prf n hn
  obtain ⟨Kah, Kbh⟩ := prf
  show Ka * Kb ≤ a n * b n
  apply le_trans
  apply Rat.mul.le_left_pos
  apply le_of_lt
  assumption
  assumption
  rw [Rat.mul.comm (a n), Rat.mul.comm (a n)]
  apply Rat.mul.le_left_pos
  apply le_trans
  apply le_of_lt
  exact Ka_pos
  assumption
  assumption

def Real.mul.neg_of_pos_neg (a b: ℝ) : a.IsPos -> b.IsNeg -> (a * b).IsNeg := by
  intro apos bneg
  apply neg.IsNeg.mpr
  rw [←mul_neg]
  apply pos_of_pos_pos
  assumption
  apply neg.IsNeg.mp
  assumption

def Real.mul.neg_of_neg_pos (a b: ℝ) : a.IsNeg -> b.IsPos -> (a * b).IsNeg := by
  intro apos bneg
  apply neg.IsNeg.mpr
  rw [←neg_mul]
  apply pos_of_pos_pos
  apply neg.IsNeg.mp
  assumption
  assumption

def Real.mul.pos_of_neg_neg (a b: ℝ) : a.IsNeg -> b.IsNeg -> (a * b).IsPos := by
  intro apos bneg
  rw [←neg_neg ( a* _), ←neg_mul, ←mul_neg]
  apply pos_of_pos_pos
  apply neg.IsNeg.mp
  assumption
  apply neg.IsNeg.mp
  assumption
