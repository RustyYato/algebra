import Algebra.Rat.Order

def is_cauchy (f: nat -> rat) : Prop :=
  ∀ε: rat, 0 < ε -> ∃n: nat, ∀m ≥ n, (f n - f m).abs < ε

def is_zero (f: nat -> rat) : Prop :=
  ∀ε: rat, 0 < ε -> ∃n: nat, ∀m ≥ n, (f m).abs < ε

structure CauchySeq where
  seq: nat -> rat
  seq_is_cauchy: is_cauchy seq

def CauchySeq.Equiv (a b: CauchySeq) : Prop :=
  is_zero (fun n => a.seq n - b.seq n)

def CauchySeq.Equivalence : Equivalence Equiv where
  refl := by
    intro x ε ε_pos
    exists 0
    intro m _
    dsimp
    rw [rat.sub.self, rat.abs.zero]
    assumption
  symm := by
    intro a b ab ε ε_pos
    have ⟨ n, prf ⟩  := ab ε ε_pos
    exists n
    intro m m_ge_n
    dsimp
    rw [rat.abs.sub_symm]
    apply prf m m_ge_n
  trans := by
    intro x y z xy yz
    intro ε ε_pos
    have ε_half_pos : 0 < ε / 2 := by
      rw [rat.div.def]
      apply rat.mul.pos_pos_is_pos
      assumption
      trivial
    have ⟨ nxy, prfxy ⟩  := xy (ε / 2) ε_half_pos
    have ⟨ nyz, prfyz ⟩  := yz (ε / 2) ε_half_pos
    exists max nxy nyz
    intro m m_ge_max
    dsimp
    rw [←rat.add.zero_right (_ - _)]
    rw [←rat.sub.self (y.seq m)]
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
    have : ε = ε / 2 + ε / 2 := by
      rw [←rat.mul_two (ε / 2)]
      rw [rat.div.def, rat.mul.assoc, rat.mul.comm _ 2, rat.mul.inv_right, rat.mul.one_right]
      trivial
    rw [this]
    dsimp at prfxy prfyz
    apply rat.add.lt_of_lt
    apply prfxy
    apply flip le_trans
    assumption
    apply max.ge_left
    apply prfyz
    apply flip le_trans
    assumption
    apply max.ge_right

instance CauchySeq.setoid : Setoid CauchySeq where
  r := Equiv
  iseqv := CauchySeq.Equivalence

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
