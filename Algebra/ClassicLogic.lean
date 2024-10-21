def not_iff_not (a: P ↔ Q) : ¬P ↔ ¬Q := by
  apply Iff.intro
  intro p q
  apply p
  apply a.mpr q
  intro p q
  apply p
  apply a.mp q

namespace ClassicLogic

axiom propDecide (P: Prop) : Decidable P

def em P : P ∨ ¬P := by
  cases propDecide P
  apply Or.inr; assumption
  apply Or.inl; assumption

def byContradiction (h: ¬P -> False) : P := by
  cases propDecide P <;> rename_i g
  have := h g
  contradiction
  assumption

def not_not : ¬¬P ↔ P := by
  apply Iff.intro
  exact byContradiction
  intro p notp; contradiction

def byCases P {Q: Prop} : (P -> Q) -> (¬P -> Q) -> Q := by
  intro p notp
  cases propDecide P <;> rename_i h
  apply notp; assumption
  apply p; assumption

def not_and {P Q} : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  apply Iff.intro
  intro h
  apply byCases P
  intro p
  apply byCases Q
  intro q
  have := h ⟨p,q⟩
  contradiction
  exact Or.inr
  exact Or.inl
  intro h g
  cases g; cases h <;> contradiction

def or_iff_not_imp_right : P ∨ Q ↔ (¬Q → P) := by
  apply Iff.intro
  intro or not_b
  cases or <;> trivial
  intro h
  apply byCases Q
  exact Or.inr
  intro not_q
  exact .inl (h not_q)

def not_forall { P: α -> Prop } : (¬∀x: α, P x) ↔ ∃x: α, ¬P x := by
  apply flip Iff.intro
  intro ⟨x,h⟩ g
  exact h (g x)
  intro h
  apply byContradiction
  intro g
  apply h
  intro x
  exact byContradiction (not_exists.mp g x)

def iff_iff_and_or_not_and_not : (P ↔ Q) ↔ (P ∧ Q ∨ ¬P ∧ ¬Q) := by
  apply flip Iff.intro
  intro h
  cases h <;> rename_i h <;> cases h
  apply Iff.intro <;> (intros; assumption)
  apply Iff.intro <;> (intros; contradiction)
  intro h
  have h' := not_iff_not h
  apply byCases P
  intro p
  exact Or.inl ⟨ p, h.mp p ⟩
  intro p
  exact Or.inr ⟨ p, h'.mp p ⟩

def not_iff : ¬(P ↔ Q) ↔ (¬P ↔ Q) := by
  apply flip Iff.intro
  intro h g
  have g' := not_iff_not g
  have h' := not_iff_not h
  apply byCases Q
  intro q
  have := h.mpr q
  have := g.mpr q
  contradiction
  intro q
  have := h'.mpr q
  have := g'.mpr q
  contradiction
  intro h
  rw [iff_iff_and_or_not_and_not,
    not_or, not_and, not_and, not_not, not_not, And.comm] at h
  cases h with
  | intro l r =>
  cases l <;> cases r
  any_goals contradiction
  apply Iff.intro <;> intro <;> trivial
  apply Iff.intro <;> intro <;> trivial

theorem not_imp : ¬(a → b) ↔ a ∧ ¬b :=
  have := propDecide
  Decidable.not_imp_iff_and_not
