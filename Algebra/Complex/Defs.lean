import Algebra.Real.Defs

structure Complex where
  real: ℝ
  img: ℝ

notation "ℂ" => Complex

instance : OfNat ℂ n := ⟨.mk (OfNat.ofNat n) 0⟩

def Complex.add (a b: ℂ) : ℂ := .mk (a.real + b.real) (a.img + b.img)
def Complex.sub (a b: ℂ) : ℂ := .mk (a.real - b.real) (a.img - b.img)
def Complex.neg (a: ℂ) : ℂ := .mk (-a.real) (-a.img)
def Complex.conj (a: ℂ) : ℂ := .mk a.real (-a.img)
def Complex.mul (a b: ℂ) : ℂ := .mk (a.real * b.real - a.img * b.img) (a.real * b.img + a.img * b.real)
def Complex.norm (a: ℂ) : ℝ := a.real * a.real + a.img * a.img

instance : Add ℂ := ⟨.add⟩
instance : Sub ℂ := ⟨.sub⟩
instance : Neg ℂ := ⟨.neg⟩
instance : Mul ℂ := ⟨.mul⟩
instance : AbsoluteValue ℂ ℝ := ⟨Complex.norm⟩

def Complex.norm.eq_zero (a: ℂ) : a.norm = 0 -> a = 0 := by
  intro h
  unfold norm at h
  have real_nonneg := Real.square.nonneg a.real
  have img_nonneg := Real.square.nonneg a.img
  rcases lt_or_eq_of_le real_nonneg with real_pos | real_zero
  have : 0 < a.real * a.real + a.img * a.img := by
    apply lt_of_lt_of_le
    exact real_pos
    conv => { lhs; rw [←Real.add_zero (_ * _)] }
    apply Real.add.le
    rfl
    assumption
  rw [h] at this
  have := lt_irrefl this
  contradiction
  rcases lt_or_eq_of_le img_nonneg with img_pos | img_zero
  have : 0 < a.real * a.real + a.img * a.img := by
    apply lt_of_lt_of_le
    exact img_pos
    conv => { lhs; rw [←Real.zero_add (_ * _)] }
    apply Real.add.le
    assumption
    rfl
  rw [h] at this
  have := lt_irrefl this
  contradiction
  have := Real.square.of_eq_zero _ real_zero.symm
  have := Real.square.of_eq_zero _ img_zero.symm
  cases a
  congr

def Complex.norm.nonzero (a: ℂ) (h: a ≠ 0) : a.norm ≠ 0 := by
  intro g
  apply h
  apply norm.eq_zero
  assumption

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Complex.norm.nonzero <;> invert_tactic)

def Complex.ofNat.nonzero : OfNat.ofNat (n + 1) ≠ (0: ℂ) := by
  intro h
  have ⟨h,_⟩  := mk.inj h
  exact Real.non_zero_of_nat _ h

macro_rules | `(tactic|invert_tactic) => `(tactic|apply Complex.ofNat.nonzero)

def Complex.inverse (a: ℂ) (h: a ≠ 0) : ℂ := ⟨a.real /? a.norm, -a.img /? a.norm⟩
instance : Invert ℂ (· ≠ 0) := ⟨.inverse⟩

def Complex.div (a b: ℂ) (h: b ≠ 0) : ℂ := a * b⁻¹
instance : CheckedDiv ℂ (· ≠ 0) := ⟨.div⟩

def Complex.i : ℂ := ⟨0,1⟩

def Complex.i.spec : i * i = -1 := by
  show (mk 0 1).mul (mk 0 1) = -1
  unfold mul
  dsimp
  congr
  rw [Real.mul_zero, Real.zero_sub, Real.mul_one]
  rfl
  erw [Real.mul_zero, Real.zero_mul, Real.add_zero, Real.neg.zero]

def Complex.add.comm (a b: ℂ) : a + b = b + a := by
  show a.add b = b.add a
  unfold add
  rw [Real.add.comm a.real, Real.add.comm a.img]

def Complex.add.assoc (a b c: ℂ) : a + b + c = a + (b + c) := by
  show (a.add b).add c = a.add (b.add c)
  unfold add
  dsimp
  rw [Real.add.assoc, Real.add.assoc]

def Complex.mul.comm (a b: ℂ) : a * b = b * a := by
  show a.mul b = b.mul a
  unfold mul
  rw [Real.mul.comm a.real, Real.mul.comm a.real, Real.mul.comm a.img, Real.mul.comm a.img]
  congr 1
  rw [Real.add.comm]

def Complex.mul.assoc (a b c: ℂ) : a * b * c = a * (b * c) := by
  show (a.mul b).mul c = a.mul (b.mul c)
  unfold mul
  dsimp
  repeat first|
    rw [Real.sub_mul]|rw [Real.add_mul]|
    rw [Real.mul_sub]|rw [Real.mul_add]|
    rw [Real.sub.eq_add_neg]|rw [Real.add.neg]|
    rw [Real.mul.assoc]|rw [←Real.add.assoc]
  congr 1 <;> rw [Real.add.assoc, Real.add.right_comm, ←Real.add.assoc]

def Complex.sub.eq_add_neg (a b: ℂ) : a - b = a + -b := rfl
def Complex.div.eq_mul_inv (a b: ℂ) (h: b ≠ 0) : a /? b = a * b⁻¹ := rfl

def Complex.inv_self_mul (a: ℂ) (h: a ≠ 0) : a⁻¹ * a = 1 := by
  show (a.inverse h).mul a = 1
  unfold inverse mul
  dsimp
  rw [
    Real.div.eq_mul_inv,
    Real.div.eq_mul_inv,
    Real.neg_mul,
    Real.neg_mul,
    Real.neg_mul,
    Real.sub_neg,
    Real.mul.right_comm _ a.norm⁻¹,
    Real.mul.right_comm _ a.norm⁻¹,
    Real.mul.right_comm _ a.norm⁻¹,
    Real.mul.right_comm _ a.norm⁻¹,
    ←Real.add_mul,
    ←Real.neg_mul,
    ←Real.add_mul,
    Real.mul.comm a.real a.img,
    Real.add_neg_self,
    Real.zero_mul,
    ←Complex.norm,
    Real.mul_inv_self]
  rfl

def Complex.mul_inv_self (a: ℂ) (h: a ≠ 0) : a * a⁻¹ = 1 := by
  rw [mul.comm, inv_self_mul]

def Complex.add_neg_self (a: ℂ) : a + -a = 0 := by
  show a.add a.neg = 0
  unfold add neg
  dsimp
  rw [Real.add_neg_self, Real.add_neg_self]
  rfl

def Complex.neg_self_add (a: ℂ) : -a + a = 0 := by
  rw [add.comm, add_neg_self]

def Complex.div.self (a: ℂ) (h: a ≠ 0) : a /? a = 1 := by
  rw [div.eq_mul_inv, mul_inv_self]
def Complex.sub.self (a: ℂ) : a - a = 0 := by
  rw [sub.eq_add_neg, add_neg_self]

def Complex.neg_mul (a b: ℂ) : -a * b = -(a * b) := by
  show a.neg.mul b = (a.mul b).neg
  unfold mul neg
  dsimp
  repeat rw [Real.neg_mul]
  rw [Real.sub_neg, Real.sub.neg, Real.add.neg, Real.add.comm]
  rfl

def Complex.mul_neg (a b: ℂ) : a * -b = -(a * b) := by
  rw [mul.comm, neg_mul, mul.comm]

def Complex.add_mul (a b k: ℂ) : (a + b) * k = a * k + b * k := by
  show (a.add b).mul k = (a.mul k).add (b.mul k)
  unfold mul add
  dsimp
  repeat rw [Real.add_mul]
  congr 1
  rw [Real.sub.eq_add_neg, Real.add.neg, Real.add.assoc,
    Real.add.comm_left (b.real * _), ←Real.add.assoc]
  rfl
  rw [Real.add.assoc, Real.add.comm_left (b.real * _), ←Real.add.assoc]

def Complex.mul_add (a b k: ℂ) : k * (a + b) = k * a + k * b := by
  rw [mul.comm k, mul.comm k, mul.comm k, add_mul]

def Complex.sub_mul (a b k: ℂ) : (a - b) * k = a * k - b * k := by
  rw [sub.eq_add_neg, sub.eq_add_neg, add_mul, neg_mul]

def Complex.mul_sub (a b k: ℂ) : k * (a - b) = k * a - k * b := by
  rw [sub.eq_add_neg, sub.eq_add_neg, mul_add, mul_neg]

def Complex.norm.nonneg (a: ℂ) : 0 ≤ ‖a‖ := by
  rw [←Real.add_zero 0]
  apply Real.add.le
  apply Real.square.nonneg
  apply Real.square.nonneg

def Complex.norm.mul (a b: ℂ) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  show (a.mul b).norm = a.norm * b.norm
  unfold norm mul
  dsimp
  repeat first|rw [Real.mul_add]|rw [Real.add_mul]|rw [Real.mul_sub]|rw [Real.sub_mul]|rw [Real.sub.eq_add_neg]|rw [Real.add.neg]
  repeat rw [Real.add.assoc]
  rw [Real.neg_neg]
  congr  1
  rw [Real.mul.assoc, Real.mul.comm_left b.real, Real.mul.assoc]
  repeat first|rw [Real.add.comm _  (a.img * b.real * (a.real * b.img))]|rw [←Real.add.assoc]
  rw [Real.mul.assoc, Real.mul.comm_right b.real, ←Real.mul.assoc, Real.add_neg_self,Real.zero_add]
  repeat rw [Real.add.assoc]
  repeat first|rw [Real.add.comm _  (a.real * b.img * (a.img * b.real))]|rw [←Real.add.assoc]
  rw [Real.mul.assoc, Real.mul.comm_right b.img, ←Real.mul.assoc, Real.add_neg_self,Real.zero_add]
  repeat rw [Real.add.assoc]
  repeat first|rw [Real.add.comm _  (a.img * a.img * (b.img * b.img))]|rw [←Real.add.assoc]
  repeat rw [Real.add.assoc]
  congr 1
  rw [Real.mul.assoc, Real.mul.comm_left b.img, ←Real.mul.assoc]
  rw [Real.add.comm]
  repeat rw [Real.mul.assoc]
  congr 2
  rw [Real.mul.comm_left]
  rw [Real.mul.comm_left]
