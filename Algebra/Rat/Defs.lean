import Algebra.Nat.Gcd
import Algebra.Int.Mul
import Algebra.Order.Basic

class Invert (α: Sort u) (P: outParam (α -> Prop)) where
  invert: ∀a: α, P a -> α

class CheckedDiv (α: Sort u) (P: outParam (α -> Prop)) where
  checked_div: α -> ∀den: α, P den -> α

syntax "invert_tactic" : tactic

macro_rules | `(tactic|invert_tactic) => `(tactic|trivial)

syntax:max term noWs "⁻¹" : term
macro_rules | `($x⁻¹) => `(Invert.invert $x (by invert_tactic))

syntax:max term:70 "/?" term:71 : term
macro_rules | `($x /? $y) => `(CheckedDiv.checked_div $x $y (by invert_tactic))

instance [Mul α] [Invert α P] : CheckedDiv α P where
  checked_div a b _ := a * b⁻¹

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

instance (a b: Fract) : Decidable (a ≈ b) := by
  rw [Fract.Equiv.def]
  exact inferInstance

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
      rw [int.zero_mul] at *
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
      repeat rw [int.zero_mul]
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
    rw [int.zero_eq, int.zero_mul, int.zero_mul]
  | pos_succ n
  | neg_succ n =>
    dsimp
    try rw [int.abs.pos_succ]
    try rw [int.abs.neg_succ]
    split <;> rename_i h
    rw [int.zero_eq, int.zero_mul]
    cases nat.div.of_eq_zero h <;> rename_i h
    have ⟨_,_⟩ := nat.gcd.eq_zero h
    contradiction
    have := nat.dvd.le nat.zero_lt_succ (nat.gcd.dvd_left n.succ d)
    have := not_le_of_lt h
    contradiction
    try
      apply int.neg.inj
      rw [←int.neg_mul, ←int.neg_mul,
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
  apply nat.succ_le_succ (nat.zero_le _)
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
    rw [int.zero_eq, int.zero_mul] at eq
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
      rw [int.zero_eq, int.zero_mul] at eq
      rw [int.of_nat.zero] at eq
      cases nat.mul.eq_zero (int.of_nat.inj eq)
      contradiction
      subst bden
      contradiction
    | neg_succ bnum =>
      rw [←int.neg.pos_succ, int.neg_mul] at eq
      have ⟨n,nprf⟩ := int.of_nat.of_zero_lt (a := int.of_nat (a.succ * bden)) (by
        apply sound.proof1; assumption)
      have ⟨m,mprf⟩ := int.of_nat.of_lt_zero (a := -(int.pos_succ bnum * int.of_nat aden)) (by
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
      rw [←eq, ←int.neg_mul,  int.neg.neg_succ]
    rw [int.of_nat.pos, int.mul.lift_nat] at eq
    cases bnum with
    | zero =>
      rw [int.zero_eq, int.zero_mul] at eq
      rw [int.of_nat.zero] at eq
      cases nat.mul.eq_zero (int.of_nat.inj eq)
      contradiction
      subst bden
      contradiction
    | pos_succ bnum =>
      have ⟨n,nprf⟩ := int.of_nat.of_zero_lt (a := int.of_nat (a.succ * bden)) (by
        apply sound.proof1; assumption)
      have ⟨m,mprf⟩ := int.of_nat.of_lt_zero (a := -(int.pos_succ bnum * int.of_nat aden)) (by
        apply int.neg.swap_lt.mpr
        rw [int.neg_neg, int.neg.zero, int.of_nat.pos, int.mul.lift_nat]
        apply sound.proof1; assumption)
      rw [nprf,mprf] at eq
      contradiction
    | neg_succ b =>
      rw [←int.neg_mul, int.neg.neg_succ, int.of_nat.pos, int.mul.lift_nat] at eq
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

def Rat.exact_ne (a b: Fract) :
  mk a ≠ mk b -> ¬a ≈ b := by
  intro ne
  intro h
  apply ne
  exact sound _ _ h

def Fract.reduce.of_is_reduced (f: Fract) :
  f.is_reduced ->
  f.reduce = f := by
  intro red
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
      apply Or.inl; exact nat.zero_lt_succ
      apply nat.dvd.le
      exact nat.zero_lt_succ
      apply nat.gcd.dvd_left
      try
        apply int.neg.inj
        rw [int.neg.neg_succ, int.neg.neg_succ]
      rw [int.of_nat.pos, int.of_nat.pos, ←h]
      congr
      rw [red, nat.div.one]
    · rw [red, nat.div.one]

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
def Rat.eq_mk_toFract (r: Rat) : r = mk r.toFract := by
  cases r with | ofFract f red =>
  unfold mk
  congr
  rw [Fract.reduce.of_is_reduced]
  assumption
def Rat.ind : {motive: Rat -> Prop} -> (mk: ∀f, motive (mk f)) -> ∀r, motive r := by
  intro motive ih r
  rw [r.eq_mk_toFract]
  apply ih
def Rat.liftWith : {P: Rat -> Prop} -> (f: ∀a, P (mk a) -> α) -> (∀a b, a ≈ b -> (h₀: P (mk a)) -> (h₁: P (mk b)) -> f a h₀ = f b h₁) -> ∀a, P a -> α :=
  fun f _ r h => f r.toFract <| by
    rw [←eq_mk_toFract]
    exact h
def Rat.liftWith_mk :
  liftWith f all_eq (mk a) h = f a h := by
  apply all_eq
  symm
  apply Fract.Equiv.reduce
def Rat.liftWith₂ : {P: Rat -> Rat -> Prop} -> (f: ∀a b, P (mk a) (mk b) -> α) -> (∀a b c d, a ≈ c -> b ≈ d -> (h₀: P (mk a) (mk b)) -> (h₁: P (mk c) (mk d)) -> f a b h₀ = f c d h₁) -> ∀a b, P a b -> α :=
  fun f _ r₀ r₁ h => f r₀.toFract r₁.toFract <| by
    rw [←eq_mk_toFract, ←eq_mk_toFract]
    exact h
def Rat.liftWith₂_mk :
  liftWith₂ f all_eq (mk a) (mk b) h = f a b h := by
  apply all_eq
  symm
  apply Fract.Equiv.reduce
  symm
  apply Fract.Equiv.reduce

def Fract.add (a b: Fract) : Fract := .mk (a.num * int.of_nat b.den + b.num * int.of_nat a.den) (a.den * b.den) (nat.mul.lt _ _ _ _ a.den_pos b.den_pos)

instance : Add Fract := ⟨.add⟩
def Fract.add.def (a b: Fract) : a + b = a.add b := rfl

def Fract.add.spec (a b c d: Fract) :
  a ≈ c -> b ≈ d -> a + b ≈ c + d := by
  repeat rw [Equiv.def]
  repeat rw [add.def, add]
  intro ac bd
  dsimp
  rw [int.add_mul, int.add_mul]
  repeat rw [int.mul.assoc, int.mul.lift_nat]
  rw [nat.mul.comm_left, ←int.mul.lift_nat, ←int.mul.assoc]
  rw [nat.mul.comm_right, nat.mul.comm c.den, ←int.mul.lift_nat d.den, ←int.mul.assoc]
  rw [nat.mul.comm_left, nat.mul.comm d.den, ←int.mul.lift_nat a.den (_ * _), ←int.mul.assoc]
  rw [nat.mul.comm_right, ←int.mul.lift_nat b.den (_ * _), ←int.mul.assoc]
  rw [ac, bd]

def Rat.add : Rat -> Rat -> Rat := by
  apply lift₂ (fun _ _ => mk _) _
  exact Fract.add
  intro a b c d ac bd
  apply sound
  apply Fract.add.spec <;> assumption

instance : Add Rat := ⟨.add⟩

def Rat.mk_add (a b: Fract) : mk a + mk b = mk (a + b) := by
  unfold HAdd.hAdd instHAdd Add.add
  apply lift₂_mk

def Fract.mul (a b: Fract) : Fract := .mk (a.num * b.num) (a.den * b.den) (nat.mul.lt _ _ _ _ a.den_pos b.den_pos)

instance : Mul Fract := ⟨.mul⟩
def Fract.mul.def (a b: Fract) : a * b = a.mul b := rfl

def Fract.mul.spec (a b c d: Fract) :
  a ≈ c -> b ≈ d -> a * b ≈ c * d := by
  repeat rw [Equiv.def]
  repeat rw [mul.def, mul]
  intro ac bd
  dsimp
  suffices (a.num * int.of_nat c.den) * (b.num * int.of_nat d.den) =
        (c.num * int.of_nat a.den) * (d.num * int.of_nat b.den) by
        rw [int.mul.assoc, int.mul.assoc, ←int.mul.lift_nat, ←int.mul.lift_nat,
          int.mul.comm_left b.num, int.mul.comm_left d.num,
          ←int.mul.assoc, ←int.mul.assoc c.num, this]
  rw [ac, bd]

def Rat.mul : Rat -> Rat -> Rat := by
  apply lift₂ (fun _ _ => mk _) _
  exact Fract.mul
  intro a b c d ac bd
  apply sound
  apply Fract.mul.spec <;> assumption

instance : Mul Rat := ⟨.mul⟩

def Rat.mk_mul (a b: Fract) : mk a * mk b = mk (a * b) := by
  unfold HMul.hMul instHMul Mul.mul
  apply lift₂_mk

def Fract.neg (a: Fract) : Fract := .mk (-a.num) a.den a.den_pos
instance : Neg Fract := ⟨.neg⟩
def Fract.neg.def (a: Fract) : -a = a.neg := rfl

def Fract.neg.spec (a b: Fract) : a ≈ b -> -a ≈ -b := by
  intro ab
  rw [neg.def, neg.def, Equiv.def]; unfold neg
  dsimp
  rw [int.neg_mul, int.neg_mul, ab]

def Rat.neg : Rat -> Rat := by
  apply lift (fun _ => mk _) _
  exact Fract.neg
  intro a b ab
  apply sound
  apply Fract.neg.spec; assumption

instance : Neg Rat := ⟨.neg⟩

def Rat.mk_neg (a: Fract) : -mk a = mk (-a) := by
  unfold Neg.neg
  apply lift_mk

instance : Sub Fract where
  sub a b := a + -b
instance : Sub Rat where
  sub a b := a + -b

def Rat.mk_sub (a b: Fract) : mk a - mk b = mk (a - b) := by
  unfold HSub.hSub instHSub Sub.sub instSubRat instSubFract
  dsimp
  rw [mk_neg, mk_add]

def Fract.abs (a: Fract) : Fract := .mk (int.of_nat a.num.abs) a.den a.den_pos

def Fract.abs.spec (a b: Fract) : a ≈ b -> a.abs ≈ b.abs := by
  intro ab
  rw [Equiv.def]; unfold abs
  dsimp
  cases a with | mk an ad ad_pos =>
  cases b with | mk bn bd bd_pos =>
  dsimp
  cases an <;> cases bn <;> cases ad <;> cases bd
  any_goals contradiction
  rfl
  all_goals rename_i a b ad bd
  rw [int.abs.pos_succ, int.abs.pos_succ, ←int.of_nat.pos, ←int.of_nat.pos b, ab]
  rw [int.abs.neg_succ, int.abs.neg_succ, ←int.of_nat.pos, ←int.of_nat.pos b]
  apply int.neg.inj
  rw [←int.neg_mul, ←int.neg_mul, int.neg.pos_succ, int.neg.pos_succ, ab]

def Rat.abs : Rat -> Rat := by
  apply lift (fun _ => mk _) _
  exact Fract.abs
  intro a b ab
  apply sound
  apply Fract.abs.spec
  assumption

def Rat.mk_abs (a: Fract) : (mk a).abs = mk a.abs := lift_mk

instance : OfNat Fract n where
  ofNat := Fract.mk n 1 nat.zero_lt_succ
instance : OfNat Rat n where
  ofNat := Rat.ofFract (OfNat.ofNat n) nat.gcd.one_right

def Fract.num_zero : (0: Fract).num = 0 := rfl
def Fract.num_one : (1: Fract).num = 1 := rfl
def Fract.num_ofNat : (OfNat.ofNat n: Fract).num = n := rfl
def Fract.den_ofNat : (OfNat.ofNat n: Fract).den = 1 := rfl

def Rat.num_zero : (0: Rat).num = 0 := rfl
def Rat.num_ofNat : (OfNat.ofNat n: Rat).num = n := rfl
def Rat.den_ofNat : (OfNat.ofNat n: Rat).den = 1 := rfl

def Rat.mk_ofNat : mk (OfNat.ofNat n) = OfNat.ofNat n := by
  unfold mk
  unfold OfNat.ofNat instOfNatFract
  dsimp
  congr
  apply Fract.reduce.of_is_reduced
  unfold Fract.is_reduced
  dsimp
  rw [nat.gcd.one_right]

def Fract.invert (a: Fract) : ¬a ≈ 0 -> Fract :=
  fun h => .mk (a.num.sign * a.den) a.num.abs <| by
    cases a with | mk n d d_pos =>
    cases n
    exfalso
    apply h
    rw [Equiv.def]
    dsimp
    rw [num_zero, den_ofNat, int.zero_mul, int.zero_eq, int.zero_mul]
    apply nat.zero_lt_succ
    apply nat.zero_lt_succ

instance : Invert Fract (¬· ≈ 0) := ⟨.invert⟩

def Fract.invert.def (a: Fract) (h: ¬a ≈ 0) : a⁻¹ = a.invert h := rfl

def Fract.sign.spec (a b: Fract) : a ≈ b -> a.num.sign = b.num.sign := by
  intro ab
  cases a <;> cases b <;> rename_i a ad _ b bd _
  cases a <;> cases b <;> cases ad <;> cases bd <;> trivial

def Fract.invert.spec (a b: Fract) : a ≈ b -> (_: ¬a ≈ 0) -> (h₀: ¬b ≈ 0) -> a⁻¹ ≈ b⁻¹ := by
  intro ab anz bnz
  rw [invert.def, invert.def, Equiv.def]; unfold invert
  dsimp only
  rw [int.sign_mul.mul_of_nat, nat.mul.comm, ←int.sign_mul.mul_of_nat,
    sign.spec _ _ ab, int.abs.sign]
  rw [int.sign_mul.mul_of_nat, nat.mul.comm, ←int.sign_mul.mul_of_nat,
    ←sign.spec _ _ ab, int.abs.sign]
  rw [ab]

def Rat.non_zero_of_non_zero₀ (a: Fract) : mk a ≠ 0 -> ¬a ≈ 0 := fun h => Rat.exact_ne _ _ h

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Rat.non_zero_of_non_zero₀; trivial)

def Rat.non_zero_of_non_zero₁ (a: Fract) : ¬a ≈ 0 -> mk a ≠ 0 := by
  intro h g
  apply h
  exact exact _ _ g

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Rat.non_zero_of_non_zero₁; invert_tactic)

def Rat.toFract_non_zero_of_non_zero (a: Rat) : a ≠ 0 -> ¬a.toFract ≈ 0 := by
  intro h g
  apply h
  induction a using ind with
  | mk a =>
  rw [←mk_ofNat]
  apply sound
  exact Fract.trans (Fract.Equiv.reduce a) g

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Rat.toFract_non_zero_of_non_zero; invert_tactic)

instance : Invert Rat (· ≠ 0) where
  invert a h := Rat.liftWith (P := (· ≠ 0)) (fun x h => Rat.mk x⁻¹) (by
    intro a b ab ha hb
    apply Rat.sound
    apply Fract.invert.spec
    assumption) a h

def Rat.mk_invert (a: Fract) (h: ¬a ≈ 0) : (mk a)⁻¹ = mk a⁻¹ := liftWith_mk

def Rat.mk_div (a b: Fract) (h: ¬b ≈ 0) : (mk a) /? mk b = mk a /? b := by
  unfold CheckedDiv.checked_div instCheckedDivOfMulOfInvert
  dsimp
  rw [mk_invert, mk_mul]

def Rat.mk_zero : 0 = mk 0 := rfl
def Rat.mk_one : 1 = mk 1 := rfl

def Fract.add.comm (a b: Fract) : a + b ≈ b + a := by
  cases a with | mk a ad ad_pos =>
  cases b with | mk b bd bd_pos =>
  rw [Equiv.def]
  repeat rw [add.def, add]
  dsimp
  rw [int.add.comm, nat.mul.comm bd]

def Rat.add.comm (a b: Rat) : a + b = b + a := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_add, mk_add]
  apply sound
  apply Fract.add.comm

def Fract.add.assoc (a b c: Fract) : a + b + c ≈ a + (b + c) := by
  cases a with | mk a ad ad_pos =>
  cases b with | mk b bd bd_pos =>
  cases c with | mk c cd cd_pos =>
  rw [Equiv.def]
  repeat rw [add.def, add]
  dsimp
  repeat rw [int.add_mul]
  repeat rw [←int.mul.lift_nat]
  rw [int.add.assoc]
  congr 1
  repeat rw [int.mul.assoc]
  congr 2
  rw [int.mul.comm_left]
  rw [int.mul.comm_left]

def Rat.add.assoc (a b c: Rat) : a + b + c = a + (b + c) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction c using ind with | mk c =>
  repeat rw [mk_add]
  apply sound
  apply Fract.add.assoc

def Fract.mul.comm (a b: Fract) : a * b ≈ b * a := by
  cases a with | mk a ad ad_pos =>
  cases b with | mk b bd bd_pos =>
  rw [Equiv.def]
  repeat rw [mul.def, mul]
  dsimp
  rw [int.mul.comm a, nat.mul.comm bd]

def Rat.mul.comm (a b: Rat) : a * b = b * a := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  rw [mk_mul, mk_mul]
  apply sound
  apply Fract.mul.comm

def Fract.mul.assoc (a b c: Fract) : a * b * c ≈ a * (b * c) := by
  cases a with | mk a ad ad_pos =>
  cases b with | mk b bd bd_pos =>
  cases c with | mk c cd cd_pos =>
  rw [Equiv.def]
  repeat rw [mul.def, mul]
  dsimp
  repeat rw [←int.mul.lift_nat]
  repeat rw [int.mul.assoc]

def Rat.mul.assoc (a b c: Rat) : a * b * c = a * (b * c) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction c using ind with | mk c =>
  repeat rw [mk_mul]
  apply sound
  apply Fract.mul.assoc

def Rat.add_zero (a: Rat) : a + 0 = a := by
  induction a using ind with | mk a =>
  rw [mk_zero, mk_add]
  apply sound
  rw [Fract.Equiv.def, Fract.add.def, Fract.add, Fract.num_zero]
  dsimp
  have : int.of_nat 1 = 1 := rfl
  rw [Fract.den_ofNat, int.zero_mul, int.add.zero_right, nat.mul_one, this, int.mul_one]

def Rat.zero_add (a: Rat) : 0 + a = a := by
  rw [add.comm, add_zero]

def Rat.mul_one (a: Rat) : a * 1 = a := by
  induction a using ind with | mk a =>
  rw [mk_one, mk_mul]
  apply sound
  rw [Fract.Equiv.def, Fract.mul.def, Fract.mul, Fract.num_one]
  dsimp
  have : int.of_nat 1 = 1 := rfl
  rw [Fract.den_ofNat, int.mul_one, nat.mul_one]

def Rat.one_mul (a: Rat) : 1 * a = a := by
  rw [mul.comm, mul_one]

def Rat.mul_zero (a: Rat) : a * 0 = 0 := by
  induction a using ind with | mk a =>
  rw [mk_zero, mk_mul]
  apply sound
  rw [Fract.Equiv.def, Fract.mul.def, Fract.mul, Fract.num_zero]
  dsimp
  have : int.of_nat 1 = 1 := rfl
  rw [Fract.den_ofNat, int.mul_zero, int.zero_mul, int.zero_mul]

def Rat.zero_mul (a: Rat) : 0 * a = 0 := by
  rw [mul.comm, mul_zero]

def Rat.neg_eq_neg_one_mul (a: Rat) : -a = -1 * a := by
  induction a using ind with | mk a =>
  rw [mk_one, mk_neg, mk_neg, mk_mul]
  apply sound
  rw [Fract.neg.def, Fract.neg.def, Fract.mul.def, Fract.mul]
  unfold Fract.neg
  rw [Fract.Equiv.def, Fract.num_one]
  dsimp
  rw [Fract.den_ofNat, nat.one_mul]
  conv in -a.num => {
    rw [←@int.one_mul a.num, ←int.neg_mul]
  }

def Fract.add_mul (a b k: Fract) : (a + b) * k ≈ a * k + b * k := by
  repeat first|rw [add.def, add]|rw [mul.def,mul]
  rw [Equiv.def]
  dsimp
  repeat first|rw [int.add_mul]|rw [←int.mul.lift_nat]
  repeat rw [int.mul.assoc]
  congr 2
  rw [int.mul.comm_left]
  congr 2
  rw [int.mul.comm_left]
  rw [int.mul.comm_left]
  congr 2
  rw [int.mul.comm_left]

def Rat.add_mul (a b k: Rat) : (a + b) * k = a * k + b * k := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  induction k using ind with | mk k =>
  repeat first|rw [mk_mul]|rw [mk_add]
  apply sound
  apply Fract.add_mul

def Rat.mul_add (a b k: Rat) : k * (a + b) = k * a + k * b := by
  repeat rw [mul.comm k]
  rw [add_mul]

def Rat.sub.eq_add_neg (a b: Rat) : a - b = a + -b := rfl

def Rat.mul_neg (a b: Rat) : a * -b = -(a * b) := by
  rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul (a * b),
    mul.comm, mul.assoc, mul.comm b]
def Rat.neg_mul (a b: Rat) : (-a) * b = -(a * b) := by
  rw [mul.comm, mul_neg, mul.comm]

def Rat.add.neg (a b: Rat) : -(a + b) = -a - b := by
  rw [sub.eq_add_neg, neg_eq_neg_one_mul, mul_add, ←neg_eq_neg_one_mul, ←neg_eq_neg_one_mul]
def Rat.neg_neg (a: Rat): - - a = a := by
  have : -1 * -1 = (1: Rat) := rfl
  rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul a, ←mul.assoc, this, one_mul]
def Rat.sub.neg (a b: Rat) : -(a - b) = b - a := by
  rw [sub.eq_add_neg, add.neg, sub.eq_add_neg, sub.eq_add_neg, neg_neg, add.comm]

def Rat.sub_mul (a b k: Rat) : (a - b) * k = a * k - b * k := by
  rw [sub.eq_add_neg, add_mul, neg_mul, sub.eq_add_neg]

def Rat.mul_sub (a b k: Rat) : k * (a + b) = k * a + k * b := by
  repeat rw [mul.comm k]
  rw [add_mul]

def Rat.sub.self (a: Rat) : a - a = 0 := by
  rw [←one_mul a, ←sub_mul]
  have : (1: Rat) - 1 = 0 := rfl
  rw [this, zero_mul]

def Rat.abs.neg (a: Rat) : (-a).abs = a.abs := by
  induction a using ind with | mk a =>
  rw [mk_neg, mk_abs, mk_abs]
  apply sound
  rw [Fract.Equiv.def, Fract.neg.def]
  unfold Fract.abs Fract.neg
  dsimp
  rw [int.abs.neg]

def Rat.abs.sub_comm (a b: Rat) : (a - b).abs = (b - a).abs := by
  rw [←abs.neg (a - b), sub.neg]

def Rat.div.self (a: Rat) (h: a ≠ 0) : a /? a = 1 := by
  suffices a * a⁻¹ = 1 from this
  induction a using ind with | mk a =>
  rw [mk_invert, mk_mul, mk_one]
  any_goals invert_tactic
  apply sound
  cases a with | mk n d d_pos =>
  cases d with
  | zero => contradiction
  | succ d =>
  rw [Fract.invert.def, Fract.mul.def, Fract.Equiv.def]
  unfold Fract.mul Fract.invert int.sign
  dsimp
  cases n with
  | zero =>
    exfalso
    apply h
    rw [mk_zero]
    apply sound
    rw [Fract.Equiv.def]
    rw [Fract.num_zero, int.zero_mul, int.zero_eq, int.zero_mul]
  | pos_succ n =>
    dsimp
    have : int.of_nat 1 = 1 := rfl
    rw [Fract.den_ofNat, Fract.num_one, int.one_mul, this, int.mul_one]
    rw [int.abs.pos_succ, int.of_nat.pos, int.of_nat.pos, int.mul.lift_nat, nat.mul.comm]
  | neg_succ n =>
    dsimp
    have : int.of_nat 1 = 1 := rfl
    rw [Fract.den_ofNat, Fract.num_one, int.one_mul, this, int.mul_one]
    rw [int.abs.neg_succ, ←int.neg.pos_succ, int.neg_mul, ←int.mul_neg,
      int.neg.neg_succ, int.of_nat.pos,int.of_nat.pos, int.mul.lift_nat, nat.mul.comm]

def Rat.div.pos (a: Rat) (h: a ≠ 0) : a /? a = 1 := by
  suffices a * a⁻¹ = 1 from this
  induction a using ind with | mk a =>
  rw [mk_invert, mk_mul, mk_one]
  any_goals invert_tactic
  apply sound
  cases a with | mk n d d_pos =>
  cases d with
  | zero => contradiction
  | succ d =>
  rw [Fract.invert.def, Fract.mul.def, Fract.Equiv.def]
  unfold Fract.mul Fract.invert int.sign
  dsimp
  cases n with
  | zero =>
    exfalso
    apply h
    rw [mk_zero]
    apply sound
    rw [Fract.Equiv.def]
    rw [Fract.num_zero, int.zero_mul, int.zero_eq, int.zero_mul]
  | pos_succ n =>
    dsimp
    have : int.of_nat 1 = 1 := rfl
    rw [Fract.den_ofNat, Fract.num_one, int.one_mul, this, int.mul_one]
    rw [int.abs.pos_succ, int.of_nat.pos, int.of_nat.pos, int.mul.lift_nat, nat.mul.comm]
  | neg_succ n =>
    dsimp
    have : int.of_nat 1 = 1 := rfl
    rw [Fract.den_ofNat, Fract.num_one, int.one_mul, this, int.mul_one]
    rw [int.abs.neg_succ, ←int.neg.pos_succ, int.neg_mul, ←int.mul_neg,
      int.neg.neg_succ, int.of_nat.pos,int.of_nat.pos, int.mul.lift_nat, nat.mul.comm]

def Rat.mul_div.assoc (a b c: Rat) (h: c ≠ 0) : a * (b /? c) = (a * b) /? c := by
  suffices a * (b * c⁻¹) = (a * b) /? c from this
  rw [←mul.assoc]
  rfl

def Rat.mul_div.comm_left (a b c: Rat) (h: c ≠ 0) : a * (b /? c) = b * (a /? c) := by
  suffices a * (b * c⁻¹) = b * (a * c⁻¹) from this
  rw [←mul.assoc, mul.comm a, mul.assoc]

def Rat.mul_div_cancel (a b: Rat) (h: a ≠ 0) : a * (b /? a) = b := by
  rw [Rat.mul_div.comm_left, div.self, mul_one]

instance : Div Rat where
  div a b := if h:b = 0 then 0 else a /? b

def Fract.le (a b: Fract) := a.num * int.of_nat b.den ≤ b.num * int.of_nat a.den
def Fract.lt (a b: Fract) := a.num * int.of_nat b.den < b.num * int.of_nat a.den

instance : LE Fract := ⟨Fract.le⟩
instance : LT Fract := ⟨Fract.lt⟩

def Fract.le.def (a b: Fract) : (a ≤ b) = a.le b := rfl
def Fract.lt.def (a b: Fract) : (a < b) = a.lt b := rfl

def Fract.le.spec (a b c d: Fract) :
  a ≈ c -> b ≈ d -> (a ≤ b ↔ c ≤ d) := by
  intro ac bd
  cases a with | mk a₀ a₁ a₁_pos =>
  cases b with | mk b₀ b₁ b₁_pos =>
  cases c with | mk c₀ c₁ c₁_pos =>
  cases d with | mk d₀ d₁ d₁_pos =>
  rw [Equiv.def] at ac bd
  rw [le.def, le.def]
  unfold le
  dsimp at *
  apply Iff.trans (int.mul.le_mul_pos (k := c₁ * d₁) _)
  rw [
    int.mul.assoc, int.mul.comm_left b₁, ←int.mul.assoc, ac,
    int.mul.assoc, int.mul.comm_right a₁, ←int.mul.assoc,
    int.mul.assoc b₀, int.mul.comm_right a₁, ←int.mul.assoc b₀, bd,
    int.mul.assoc d₀, int.mul.comm_left b₁, ←int.mul.assoc d₀]
  apply Iff.trans (int.mul.le_mul_pos _).symm
  rfl
  rw [int.mul.lift_nat]
  suffices 0 * 0 < b₁ * a₁ from int.lt.pos_nat _ this
  apply nat.mul.lt <;> assumption
  rw [int.mul.lift_nat]
  suffices 0 * 0 < c₁ * d₁ from int.lt.pos_nat _ this
  apply nat.mul.lt <;> assumption

def Fract.lt.spec (a b c d: Fract) :
  a ≈ c -> b ≈ d -> (a < b ↔ c < d) := by
  intro ac bd
  cases a with | mk a₀ a₁ a₁_pos =>
  cases b with | mk b₀ b₁ b₁_pos =>
  cases c with | mk c₀ c₁ c₁_pos =>
  cases d with | mk d₀ d₁ d₁_pos =>
  rw [Equiv.def] at ac bd
  rw [lt.def, lt.def]
  unfold lt
  dsimp at *
  apply Iff.trans (int.mul.lt_mul_pos (k := c₁ * d₁) _)
  rw [
    int.mul.assoc, int.mul.comm_left b₁, ←int.mul.assoc, ac,
    int.mul.assoc, int.mul.comm_right a₁, ←int.mul.assoc,
    int.mul.assoc b₀, int.mul.comm_right a₁, ←int.mul.assoc b₀, bd,
    int.mul.assoc d₀, int.mul.comm_left b₁, ←int.mul.assoc d₀]
  apply Iff.trans (int.mul.lt_mul_pos _).symm
  rfl
  rw [int.mul.lift_nat]
  suffices 0 * 0 < b₁ * a₁ from int.lt.pos_nat _ this
  apply nat.mul.lt <;> assumption
  rw [int.mul.lift_nat]
  suffices 0 * 0 < c₁ * d₁ from int.lt.pos_nat _ this
  apply nat.mul.lt <;> assumption

def Rat.le : Rat -> Rat -> Prop := by
  apply liftProp₂ Fract.le
  apply Fract.le.spec

def Rat.lt : Rat -> Rat -> Prop := by
  apply liftProp₂ Fract.lt
  apply Fract.lt.spec

instance : LE Rat := ⟨Rat.le⟩
instance : LT Rat := ⟨Rat.lt⟩

def Rat.mk_le {a b: Fract} : (mk a) ≤ (mk b) ↔ a ≤ b := by
  unfold LE.le
  exact liftProp₂_mk

def Rat.mk_lt {a b: Fract} : (mk a) < (mk b) ↔ a < b := by
  unfold LT.lt
  exact liftProp₂_mk

syntax "rw_rat_cmp" : tactic

macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply Rat.mk_le.mp (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply Rat.mk_le.mpr (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply Rat.mk_lt.mp (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply Rat.mk_lt.mpr (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply (not_iff_not Rat.mk_le).mp (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply (not_iff_not Rat.mk_le).mpr (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply (not_iff_not Rat.mk_lt).mp (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply (not_iff_not Rat.mk_lt).mpr (by assumption))
macro_rules
| `(tactic|rw_rat_cmp) => `(tactic|apply And.intro <;> rw_rat_cmp)

instance Rat.IsLinearOrderInst : IsLinearOrder Rat where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := int)
  le_antisymm := by
    intro a b ab ba
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    apply Rat.sound
    apply le_antisymm <;> rw_rat_cmp
  le_total := by
    intro a b
    apply le_total (α := int)
  le_complete := by
    intro a b
    apply le_complete (α := int)
  le_trans := by
    intro a b c ab bc
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    induction c using ind with | mk c =>
    replace ab := mk_le.mp ab
    replace bc := mk_le.mp bc
    apply mk_le.mpr
    rw [Fract.le.def] at *
    unfold Fract.le at *
    apply (int.mul.le_mul_pos (k := b.den) _).mpr
    rw [int.mul.right_comm]
    apply le_trans
    apply (int.mul.le_mul_pos _).mp
    assumption
    exact int.lt.pos_nat c.den c.den_pos
    rw [int.mul.right_comm,int.mul.right_comm _ a.den]
    apply (int.mul.le_mul_pos _).mp
    assumption
    exact int.lt.pos_nat a.den a.den_pos
    exact int.lt.pos_nat b.den b.den_pos

instance Rat.defLE (a b: Rat) : Decidable (a ≤ b) := by
  unfold LE.le instLERat le liftProp₂ Fract.le
  dsimp
  exact inferInstance

#print axioms Rat.IsLinearOrderInst

instance : Min Rat := minOfLe
instance : Max Rat := maxOfLe
instance : IsDecidableLinearOrder Rat where
