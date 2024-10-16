
structure Prod' (α β: Type _) where
  left: α
  right: β

inductive Prod'.LexAny (arel: α -> α -> Prop) (brel: β -> β -> Prop) :
  Prod' α β -> Prod' α β -> Prop where
| left (a₀ a₁: α) (b: β) : arel a₀ a₁ -> LexAny arel brel ⟨ a₀, b ⟩ ⟨ a₁, b ⟩
| both (a₀ a₁: α) (b₀ b₁: β) : arel a₀ a₁ -> brel b₀ b₁ -> LexAny arel brel ⟨ a₀, b₀ ⟩ ⟨ a₁, b₁ ⟩
| right (a: α) (b₀ b₁: β) : brel b₀ b₁ -> LexAny arel brel ⟨ a, b₀ ⟩ ⟨ a, b₁ ⟩

def Prod'.lex_any_wf
  { arel: α -> α -> Prop }
  { brel: β -> β -> Prop }
  (arel_wf: WellFounded arel)
  (brel_wf: WellFounded brel) : WellFounded (Prod'.LexAny arel brel) := by
  apply WellFounded.intro
  intro ⟨a₀,b₀⟩
  induction a₀ using arel_wf.induction generalizing b₀ with | h a₀ aih =>
  induction b₀ using brel_wf.induction with | h b₀ bih =>
  apply Acc.intro
  intro ⟨a₁,b₁⟩ r
  cases r <;> rename_i r
  apply aih
  assumption
  apply Acc.inv _ (LexAny.right _ _ _ r)
  apply aih
  assumption
  clear aih
  apply bih
  assumption

instance [awf: WellFoundedRelation α] [bwf: WellFoundedRelation β] : WellFoundedRelation (Prod' α β) where
  rel := Prod'.LexAny awf.rel bwf.rel
  wf := Prod'.lex_any_wf awf.wf bwf.wf
