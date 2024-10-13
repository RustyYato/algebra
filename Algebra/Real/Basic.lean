import Algebra.Rat.Order

def is_cauchy (f: nat -> rat) : Prop :=
  ∀ε: rat, 0 < ε -> ∃n: nat, ∀m ≥ n, (f n - f m).abs < ε

def is_zero (f: nat -> rat) : Prop :=
  ∀ε: rat, 0 < ε -> ∃n: nat, ∀m ≥ n, (f n).abs < ε

structure CauchySeq where
  seq: nat -> rat
  seq_is_cauchy: is_cauchy seq

def CauchySeq.Equiv (a b: CauchySeq) : Prop :=
  is_zero (fun n => a.seq n - b.seq n)

def CauchySeq.Equivalence : Equivalence Equiv where
  refl := by
    intro x ε ε_pos
    exists 0
    intro m m_ge
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
    sorry
