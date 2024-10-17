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

end ClassicLogic
