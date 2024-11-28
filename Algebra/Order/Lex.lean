import Algebra.Order.Defs

variable [alt: LT α] [ale: LE α] [blt: LT β] [ble: LE β] [IsLinearOrder' α] [IsLinearOrder' β]

instance : LT (α × β) where
  lt := Prod.Lex alt.lt blt.lt
instance : LE (α × β) where
  le a b := a < b ∨ a = b

instance : IsLinearOrder' (α × β) where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    · intro h
      cases h with
      | left b₁ b₂ =>
        rename_i a₁ a₂ r
        apply And.intro
        left
        apply Prod.Lex.left
        assumption
        intro h
        cases h <;> rename_i h
        cases h <;> rename_i h
        exact lt_irrefl (lt_trans r h)
        exact lt_irrefl r
        cases h
        exact lt_irrefl r
      | right a r =>
        rename_i b₁ b₂
        apply And.intro
        left
        apply Prod.Lex.right
        assumption
        intro h
        cases h <;> rename_i h
        cases h <;> rename_i h
        exact lt_irrefl h
        exact lt_irrefl (lt_trans r h)
        cases h
        exact lt_irrefl r
    · intro ⟨h,g⟩
      cases h <;> rename_i h
      assumption
      subst b
      have := g (.inr rfl)
      contradiction
  le_antisymm := by
    intro a b ab ba
    cases ab <;> rename_i ab
    cases ba <;> rename_i ba
    · exfalso
      cases ab <;> rename_i ab <;> cases ba <;> rename_i ba
      exact lt_asymm ab ba
      exact lt_irrefl ab
      exact lt_irrefl ba
      exact lt_asymm ab ba
    symm; assumption
    assumption
  le_complete := by
    intro a b
    rcases le_complete a.fst b.fst with ab₁ | ba₁
    rcases lt_or_eq_of_le ab₁ with ab₁ | ab₁
    left; left
    apply Prod.Lex.left
    assumption
    rcases le_complete a.snd b.snd with ab₂ | ba₂
    left
    rcases lt_or_eq_of_le ab₂ with ab₂ | ab₂
    left
    cases a
    cases ab₁
    apply Prod.Lex.right
    assumption
    right
    cases a; cases b; congr
    right
    intro h
    cases h <;> rename_i h
    cases h <;> rename_i h₀ h₁
    subst ab₁
    exact lt_irrefl h₀
    apply ba₂
    apply le_of_lt
    assumption
    subst b
    apply ba₂
    rfl
    right
    intro h
    cases h <;> rename_i h
    cases h <;> rename_i h
    apply ba₁
    apply le_of_lt
    assumption
    apply ba₁
    rfl
    subst b
    apply ba₁
    rfl
  le_total := by
    intro a b
    rcases lt_or_le b.fst a.fst with ba₁ | ab₁
    right; left; apply Prod.Lex.left
    assumption
    rcases lt_or_eq_of_le ab₁ with ab₁ | ab₁
    left; left; apply Prod.Lex.left
    assumption
    cases a; cases b
    subst ab₁
    rename_i a b
    rcases lt_or_le b a with ba₂ | ab₂
    right; left; apply Prod.Lex.right
    assumption
    left
    rcases lt_or_eq_of_le ab₂ with ab₂ | ab₂
    left; apply Prod.Lex.right
    assumption
    right
    congr
  le_trans := by
    intro a b c ab bc
    rcases ab with ab | ab
    rcases bc with bc | bc
    left
    rcases ab with ⟨b₀, b₁, ab⟩ | ⟨a, ab⟩
    rcases bc with ⟨c₀, c₁, bc⟩ | ⟨b, bc⟩
    apply Prod.Lex.left
    apply lt_trans <;> assumption
    apply Prod.Lex.left
    assumption
    rcases bc with ⟨c₀, c₁, bc⟩ | ⟨b, bc⟩
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.right
    apply lt_trans <;> assumption
    subst c
    left; assumption
    subst b
    assumption

variable [Min α] [Max α] [Min β] [Max β]

variable [IsDecidableLinearOrder α] [IsDecidableLinearOrder β]

instance (a b: α × β) : Decidable (a ≤ b) :=
  if h:a.fst < b.fst then
    .isTrue (.inl (Prod.Lex.left _ _ h))
  else if g:a.fst = b.fst ∧ a.snd ≤ b.snd then
    .isTrue (by
      cases a; cases b; cases g.left
      cases lt_or_eq_of_le g.right <;> rename_i g
      left; apply Prod.Lex.right; assumption
      right; congr)
  else
    .isFalse <| by
      intro h
      cases h <;> rename_i h
      cases h
      contradiction
      dsimp at h g
      rename_i h₀
      exact not_and.mp g rfl (le_of_lt h₀)
      subst b
      exact not_and.mp g rfl (le_refl _)

instance : Min (α × β) := minOfLe
instance : Max (α × β) := maxOfLe

instance : IsLinearOrder (α × β) where
instance : IsDecidableLinearOrder (α × β) where
