import Algebra.Nat.Gcd
import Algebra.Int.Mul
import Algebra.Order.Basic

structure Fract where
  num: int
  den: nat
  den_pos: 0 < den
deriving Repr, DecidableEq

def Fract.is_reduced (f: Fract) : Prop := f.num.abs.gcd f.den = 1

structure Rat extends Fract where
  ofFract ::
  is_reduced: toFract.is_reduced
deriving Repr, DecidableEq

instance : HasEquiv Fract where
  Equiv a b := a.num * b.den = b.num * a.den

def Fract.Equiv.def (a b: Fract) : (a ≈ b) = (a.num * b.den = b.num * a.den) := rfl

instance Fract.instEquiv : @Equivalence Fract (· ≈ ·) where
  refl := fun _ => rfl
  symm := by
    intro x y
    intro x_eq_y
    erw [Equiv.def, x_eq_y]
  trans := by
    intro x y z
    repeat rw [Equiv.def]
    intro x_eq_y y_eq_z

    -- xnum * yden = ynum * xden
    -- xnum * yden * zden = ynum * xden * zden
    -- (xnum * zden) * yden = ynum * xden * zden

    -- ynum * zden = znum * yden
    -- ynum * zden * xden = znum * yden * xden
    -- ynum * (zden * xden) = znum * yden * xden
    -- ynum * (xden * zden) = znum * yden * xden
    -- (xden * zden) * ynum = znum * yden * xden
    -- (xden * zden) * ynum = znum * yden  * xden
    --                       (xnum * zden) * yden = ynum * xden * zden -- from before
    --                       (znum * xden) * yden = ynum * xden * zden
    --                       (znum * yden) * xden = ynum * xden * zden
    --
    -- (xden * zden) * ynum = ynum * xden * zden
    cases y with
    | mk ynum yden yden_nz =>

    simp only at *
    cases g:ynum with
    | zero =>
      cases g
      rw [int.zero_eq] at *
      rw [int.mul.zero_left] at *
      cases int.mul.eq_zero x_eq_y with
      | inr h => cases yden <;> contradiction
      | inl h =>
      rw [h]
      clear h
      cases int.mul.eq_zero y_eq_z.symm with
      | inr h => cases yden <;> contradiction
      | inl h =>
      rw [h]
      clear h
      repeat rw [int.mul.zero_left]
    | pos_succ ynum' | neg_succ ynum' =>
      have x_eq_y' : (x.num * yden) * z.den = (x.num * yden) * z.den := rfl
      conv at x_eq_y' => {
        rhs
        rw [x_eq_y]
      }
      have y_eq_z': (ynum * z.den) * x.den = (ynum * z.den) * x.den := rfl
      conv at y_eq_z' => {
        rhs
        rw [y_eq_z]
      }
      conv at y_eq_z' => {
        lhs
        rw [int.mul.assoc, int.mul.comm z.den, ←int.mul.assoc]
      }
      have x_eq_z := Eq.trans x_eq_y' y_eq_z'
      apply int.mul.of_eq
      intro x
      have : int.of_nat yden = int.of_nat 0 := x
      cases int.of_nat.inj this
      contradiction
      clear x_eq_y' y_eq_z' g y_eq_z x_eq_y ynum' yden_nz ynum
      rw [int.mul.assoc, int.mul.comm z.den, ←int.mul.assoc, x_eq_z]
      rw [int.mul.assoc, int.mul.comm yden, ←int.mul.assoc]

@[refl]
def Fract.refl (a: Fract) : a ≈ a := Fract.instEquiv.refl _
@[symm]
def Fract.symm {a: Fract} : a ≈ b -> b ≈ a := Fract.instEquiv.symm
def Fract.trans {a b c: Fract} : a ≈ b -> b ≈ c -> a ≈ c := Fract.instEquiv.trans

def Fract.reduce (r: Fract) : Fract := ⟨
    (r.num.sign * (r.num.abs / (r.num.abs.gcd r.den))),
    (r.den / (r.num.abs.gcd r.den)), by
    apply nat.div.gt_zero r.den
    apply nat.gcd.gt_zero (Or.inr _)
    exact r.den_pos
    apply nat.dvd.le
    exact r.den_pos
    exact nat.gcd.dvd_right r.num.abs r.den⟩

def Fract.reduce.spec (r: Fract) : r.reduce.is_reduced := by
  cases r with | mk n d dpos =>
  unfold reduce is_reduced int.sign
  cases n  with
  | zero =>
    dsimp
    rw [int.zero_eq, int.abs.zero, nat.gcd.left_zero, nat.gcd.left_zero, nat.div.self]
    assumption
  | pos_succ n
  | neg_succ n =>
    dsimp
    split <;> rename_i h
    try rw [int.abs.pos_succ] at *
    try rw [int.abs.neg_succ] at *
    cases nat.div.of_eq_zero h <;> rename_i h
    have ⟨_,_⟩  := nat.gcd.eq_zero h
    contradiction
    have := nat.dvd.le nat.zero_lt_succ (nat.gcd.dvd_left n.succ d)
    have := not_le_of_lt h
    contradiction
    try rw [int.abs.pos_succ, int.abs.pos_succ] at *
    try rw [int.abs.neg_succ, int.abs.neg_succ] at *
    rename_i n₀ m
    clear n₀
    rw [←h]
    clear h
    rw [nat.gcd.div_common, nat.div.self]
    apply nat.gcd.gt_zero
    apply Or.inl
    apply nat.zero_lt_succ
    apply nat.gcd.dvd_left
    apply nat.gcd.dvd_right

def Rat.mk (a: Fract) := Rat.ofFract a.reduce (Fract.reduce.spec a)

def Fract.Equiv.reduce (r: Fract) : r ≈ r.reduce := by
  cases r with | mk n d dpos =>
  rw [Fract.Equiv.def]
  unfold reduce
  dsimp
  unfold int.sign
  cases n with
  | zero =>
    dsimp
    rw [int.zero_eq, int.mul.zero_left, int.mul.zero_left]
  | pos_succ n
  | neg_succ n =>
    dsimp
    try rw [int.abs.pos_succ]
    try rw [int.abs.neg_succ]
    split <;> rename_i h
    rw [int.zero_eq, int.mul.zero_left]
    cases nat.div.of_eq_zero h <;> rename_i h
    have ⟨_,_⟩ := nat.gcd.eq_zero h
    contradiction
    have := nat.dvd.le nat.zero_lt_succ (nat.gcd.dvd_left n.succ d)
    have := not_le_of_lt h
    contradiction
    try
      apply int.neg.inj
      rw [int.mul.neg_left, int.mul.neg_left,
        int.neg.neg_succ, int.neg.neg_succ]
    rw [int.of_nat.pos, int.of_nat.pos, int.mul.lift_nat, int.mul.lift_nat]
    congr 1
    rw [nat.dvd.mul_div, nat.mul.comm, ←nat.dvd.mul_div, h, nat.mul.comm]
    apply nat.gcd.dvd_left
    apply nat.gcd.dvd_right

def Fract.sound.proof1 (a b: nat) :
  0 < b -> 0 < int.of_nat (a.succ * b) := by
  intro b_pos
  apply int.lt.pos_nat
  apply nat.lt_of_succ_le
  have : nat.succ 0 = 1 * 1 := rfl
  rw [this]
  apply nat.mul.le
  apply nat.zero_le
  apply nat.succ_le_of_lt; assumption

def nat.mul_gcd_eq: ∀{a b c d: nat},
  a * d = c * b -> a * (nat.gcd d c) = c * (nat.gcd b a) := by
  intro a d c b
  intro ab_eq_de
  rw [←nat.gcd.common_left, ←nat.gcd.common_left, ab_eq_de, nat.mul.comm a c]

def Fract.sound.proof2 (a b aden bden: nat) :
  0 < aden ->
  0 < bden ->
  0 < a ->
  0 < b ->
  a.gcd aden = 1 ->
  b.gcd bden = 1 ->
  a * bden = b * aden ->
  a = b ∧ aden = bden := by
  intro _ _ _ _ ared bred eq
  have := nat.mul_gcd_eq eq
  rw [nat.gcd.comm, bred, nat.gcd.comm, ared, nat.mul_one, nat.mul_one] at this
  subst b
  apply And.intro rfl
  apply nat.mul.cancel_left
  assumption
  exact eq.symm

def Fract.sound (a b: Fract) :
  a.is_reduced ->
  b.is_reduced ->
  a ≈ b ->
  a = b := by
  cases a with | mk anum aden aden_pos =>
  cases b with | mk bnum bden bden_pos =>
  intro ared bred eq
  rw [Fract.Equiv.def] at eq
  unfold is_reduced at ared bred
  dsimp at *
  cases anum with
  | zero =>
    rw [int.zero_eq] at ared
    rw [int.zero_eq, int.mul.zero_left] at eq
    cases int.mul.eq_zero eq.symm <;> rename_i h
    subst bnum
    rw [int.abs.zero, nat.gcd.left_zero] at ared bred
    subst aden; subst bden
    rfl
    cases aden <;> contradiction
  | pos_succ a =>
    rw [int.abs.pos_succ] at ared
    rw [int.of_nat.pos, int.mul.lift_nat] at eq
    cases bnum with
    | zero =>
      rw [int.zero_eq, int.mul.zero_left] at eq
      rw [int.of_nat.zero] at eq
      cases nat.mul.eq_zero (int.of_nat.inj eq)
      contradiction
      subst bden
      contradiction
    | neg_succ bnum =>
      rw [←int.neg.pos_succ, ←int.mul.neg_left] at eq
      have ⟨n,nprf⟩ := int.of_gt_zero (a := int.of_nat (a.succ * bden)) (by
        apply sound.proof1; assumption)
      have ⟨m,mprf⟩ := int.of_lt_zero (a := -(int.pos_succ bnum * int.of_nat aden)) (by
        apply int.neg.swap_lt.mpr
        rw [int.neg_neg, int.neg.zero, int.of_nat.pos, int.mul.lift_nat]
        apply sound.proof1; assumption)
      rw [nprf,mprf] at eq
      contradiction
    | pos_succ b =>
      rw [int.of_nat.pos, int.mul.lift_nat] at eq
      replace eq := int.of_nat.inj eq
      have ⟨_,_⟩ := Fract.sound.proof2 _ _ _ _ aden_pos bden_pos nat.zero_lt_succ nat.zero_lt_succ ared bred eq
      congr
      apply nat.succ.inj; assumption
  | neg_succ a =>
    rw [int.abs.neg_succ] at ared
    replace eq : int.pos_succ a * int.of_nat bden = -(bnum * int.of_nat aden) := by
      rw [←eq, int.mul.neg_left,  int.neg.neg_succ]
    rw [int.of_nat.pos, int.mul.lift_nat] at eq
    cases bnum with
    | zero =>
      rw [int.zero_eq, int.mul.zero_left] at eq
      rw [int.of_nat.zero] at eq
      cases nat.mul.eq_zero (int.of_nat.inj eq)
      contradiction
      subst bden
      contradiction
    | pos_succ bnum =>
      have ⟨n,nprf⟩ := int.of_gt_zero (a := int.of_nat (a.succ * bden)) (by
        apply sound.proof1; assumption)
      have ⟨m,mprf⟩ := int.of_lt_zero (a := -(int.pos_succ bnum * int.of_nat aden)) (by
        apply int.neg.swap_lt.mpr
        rw [int.neg_neg, int.neg.zero, int.of_nat.pos, int.mul.lift_nat]
        apply sound.proof1; assumption)
      rw [nprf,mprf] at eq
      contradiction
    | neg_succ b =>
      rw [int.mul.neg_left, int.neg.neg_succ, int.of_nat.pos, int.mul.lift_nat] at eq
      replace eq := int.of_nat.inj eq
      have ⟨_,_⟩ := Fract.sound.proof2 _ _ _ _ aden_pos bden_pos nat.zero_lt_succ nat.zero_lt_succ ared bred eq
      congr
      apply nat.succ.inj; assumption

def Rat.sound (a b: Fract) :
  a ≈ b ->
  mk a = mk b := by
  intro eq
  unfold mk
  congr 1
  apply Fract.sound
  exact Fract.reduce.spec a
  exact Fract.reduce.spec b
  apply Fract.trans; symm
  apply Fract.Equiv.reduce
  apply Fract.trans; assumption
  apply Fract.Equiv.reduce

def Rat.exact (a b: Fract) :
  mk a = mk b -> a ≈ b := by
  intro eq
  apply Fract.trans
  apply Fract.Equiv.reduce
  apply flip Fract.trans; symm
  apply Fract.Equiv.reduce
  rw [Rat.ofFract.inj eq]

def Rat.lift : (f: Fract -> α) -> (∀a b, a ≈ b -> f a = f b) -> Rat -> α := fun f _ r => f r.toFract
def Rat.lift_mk : lift f all_eq (mk a) = f a := by
  apply all_eq
  symm
  apply Fract.Equiv.reduce
def Rat.lift₂ : (f: Fract -> Fract -> α) -> (∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> Rat -> Rat -> α := fun f _ r₀ r₁ => f r₀.toFract r₁.toFract
def Rat.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := by
  apply all_eq
  symm
  apply Fract.Equiv.reduce
  symm
  apply Fract.Equiv.reduce
def Rat.liftProp : (f: Fract -> Prop) -> (∀a b, a ≈ b -> (f a ↔ f b)) -> Rat -> Prop := fun f _ r => f r.toFract
def Rat.liftProp_mk : liftProp f all_eq (mk a) ↔ f a := by
  apply all_eq
  symm
  apply Fract.Equiv.reduce
def Rat.liftProp₂ : (f: Fract -> Fract -> Prop) -> (∀a b c d, a ≈ c -> b ≈ d -> (f a b ↔ f c d)) -> Rat -> Rat -> Prop := fun f _ r₀ r₁ => f r₀.toFract r₁.toFract
def Rat.liftProp₂_mk : liftProp₂ f all_eq (mk a) (mk b) ↔ f a b := by
  apply all_eq
  symm
  apply Fract.Equiv.reduce
  symm
  apply Fract.Equiv.reduce
def Rat.eq_mk_toRat (r: Rat) : r = mk r.toFract := by
  cases r with | ofFract f red =>
  cases f with | mk n d dpos =>
  congr 1
  unfold Fract.is_reduced at red
  unfold Fract.reduce int.sign
  dsimp
  dsimp at red
  cases n with
  | zero => congr; rw [red, nat.div.one]
  | pos_succ n
  | neg_succ n =>
    unfold int.abs
    unfold int.abs at red
    dsimp at *
    congr
    · split <;> rename_i h
      rw [nat.div.if_ge] at h
      contradiction
      apply nat.gcd.gt_zero
      apply Or.inl; trivial
      apply nat.dvd.le
      trivial
      apply nat.gcd.dvd_left
      try
        apply int.neg.inj
        rw [int.neg.neg_succ, int.neg.neg_succ]
      rw [int.of_nat.pos, int.of_nat.pos, ←h]
      congr
      rw [red, nat.div.one]
    · rw [red, nat.div.one]
def Rat.ind : {motive: Rat -> Prop} -> (mk: ∀f, motive (mk f)) -> ∀r, motive r := by
  intro motive ih r
  rw [r.eq_mk_toRat]
  apply ih
