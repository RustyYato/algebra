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

def Complex.inverse (a: ℂ) (h: a ≠ 0) : ℂ := ⟨a.real /? a.norm,-a.img /? a.norm⟩
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
