import Algebra.Function.Basic
import Algebra.ClassicLogic

class IsLinearOrder' (α: Type _) [LT α] [LE α] [Min α] [Max α]: Prop where
  lt_iff_le_and_not_le: ∀{a b: α}, a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_antisymm: ∀{a b: α}, a ≤ b -> b ≤ a -> a = b
  le_total: ∀a b: α, a ≤ b ∨ b ≤ a
  le_complete: ∀a b: α, a ≤ b ∨ ¬(a ≤ b)
  le_trans: ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c

variable [LT α] [LE α] [Min α] [Max α] [IsLinearOrder' α] { a b c d k: α }

def lt_iff_le_and_not_le: ∀{a b: α}, a < b ↔ a ≤ b ∧ ¬b ≤ a := IsLinearOrder'.lt_iff_le_and_not_le
def le_antisymm: a ≤ b -> b ≤ a -> a = b := IsLinearOrder'.le_antisymm
def le_total: ∀a b: α, a ≤ b ∨ b ≤ a := IsLinearOrder'.le_total
def le_complete: ∀a b: α, a ≤ b ∨ ¬(a ≤ b) := IsLinearOrder'.le_complete
def le_trans: a ≤ b -> b ≤ c -> a ≤ c := IsLinearOrder'.le_trans

def le_of_lt: a < b -> a ≤ b := fun h => (lt_iff_le_and_not_le.mp h).left
def lt_of_le_of_not_le : a ≤ b -> ¬(b ≤ a) -> a < b := (lt_iff_le_and_not_le.mpr ⟨·, ·⟩)

def le_of_eq: a = b -> a ≤ b := fun h => h ▸ match le_total a a with | .inl h | .inr h => h
def not_le_of_lt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_and_not_le.1 hab).2
def not_lt_of_le (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_lt hab
@[refl]
def le_refl (a: α): a ≤ a := le_of_eq rfl
def lt_irrefl: ¬a < a := fun h => (lt_iff_le_and_not_le.mp h).right (le_refl _)
def ne_of_lt: a < b -> a ≠ b := fun h g => lt_irrefl (g ▸ h)
def lt_or_eq_of_le: a ≤ b -> a < b ∨ a = b := by
  intro h
  cases le_complete b a <;> rename_i h
  apply Or.inr
  apply le_antisymm <;> assumption
  apply Or.inl
  apply lt_iff_le_and_not_le.mpr
  apply And.intro <;> assumption
def lt_of_le_of_ne: a ≤ b -> a ≠ b -> a < b := by
  intro h g
  cases lt_or_eq_of_le h
  assumption
  contradiction
def lt_trans : a < b -> b < c -> a < c := by
  intro ab bc
  apply lt_of_le_of_ne
  apply le_trans <;> (apply le_of_lt; assumption)
  intro h
  subst c
  have ⟨_,nba⟩ := lt_iff_le_and_not_le.mp ab
  have ⟨ba,_⟩ := lt_iff_le_and_not_le.mp bc
  contradiction
def lt_of_lt_of_le : a < b -> b ≤ c -> a < c := by
  intro ab bc
  cases lt_or_eq_of_le bc <;> rename_i bc
  apply lt_trans <;> assumption
  subst c
  assumption
def lt_of_le_of_lt : a ≤ b -> b < c -> a < c := by
  intro ab bc
  cases lt_or_eq_of_le ab <;> rename_i ab
  apply lt_trans <;> assumption
  subst a
  assumption
def lt_of_not_le : ¬(a ≤ b) -> b < a := by
  intro h
  cases le_total a b
  contradiction
  apply lt_of_le_of_not_le <;> assumption
def le_of_not_lt : ¬(a < b) -> b ≤ a := by
  intro h
  cases le_total b a
  assumption
  rename_i h
  apply le_of_eq; symm
  cases lt_or_eq_of_le h <;> trivial
def le_of_not_le : ¬(a ≤ b) -> b ≤ a := le_of_lt ∘ lt_of_not_le

def lt_asymm : a < b -> b < a -> False := (lt_irrefl <| lt_trans · ·)

def lt_or_gt_of_ne : a ≠ b -> a < b ∨ b < a := by
  intro h
  cases le_total a b <;> rename_i h
  cases lt_or_eq_of_le h
  apply Or.inl
  assumption
  contradiction
  apply Or.inr
  apply lt_of_le_of_ne
  assumption
  symm
  assumption

def lt_iff_not_le : a < b ↔ ¬b ≤ a := ⟨not_le_of_lt,lt_of_not_le⟩
def le_iff_not_lt : a ≤ b ↔ ¬b < a := ⟨not_lt_of_le,le_of_not_lt⟩

def lt_iff_of_le_iff : (a ≤ b ↔ c ≤ d) -> (b < a ↔ d < c) := by
  intro h
  apply Iff.trans lt_iff_not_le
  apply Iff.trans _ lt_iff_not_le.symm
  apply not_iff_not
  assumption

def le_iff_of_lt_iff : (a < b ↔ c < d) -> (b ≤ a ↔ d ≤ c) := by
  intro h
  apply Iff.trans le_iff_not_lt
  apply Iff.trans _ le_iff_not_lt.symm
  apply not_iff_not
  assumption

def lt_or_le (a b: α) : a < b ∨ b ≤ a := by
  rcases le_total b a with ba | ab
  exact .inr ba
  rcases lt_or_eq_of_le ab with ab | ab
  exact .inl ab
  exact .inr (le_of_eq ab.symm)

class IsLinearOrder (α: Type _) [LT α] [LE α] [Min α] [Max α] extends IsLinearOrder' α: Prop where
  min_iff_le_left: ∀{a b: α}, a ≤ b ↔ min a b = a := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then a else b) = a from this
    rw [if_pos h]
    intro h
    have h : (if a ≤ b then a else b) = a := h
    split at h
    assumption
    subst h
    apply le_refl
  min_iff_le_right: ∀{a b: α}, b ≤ a ↔ min a b = b := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then a else b) = b from this
    split
    apply le_antisymm <;> assumption
    rfl
    intro h
    have h : (if a ≤ b then a else b) = b := h
    split at h
    subst h
    apply le_refl
    apply le_of_lt
    apply lt_of_not_le
    assumption
  max_iff_le_left: ∀{a b: α}, a ≤ b ↔ max a b = b := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then b else a) = b from this
    rw [if_pos]
    assumption
    intro h
    have h : (if a ≤ b then b else a) = b := h
    split at h
    assumption
    subst h
    apply le_refl
  max_iff_le_right: ∀{a b: α}, b ≤ a ↔ max a b = a := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then b else a) = a from this
    split
    apply le_antisymm <;> assumption
    rfl
    intro h
    have h : (if a ≤ b then b else a) = a := h
    split at h
    subst h
    apply le_refl
    apply le_of_lt
    apply lt_of_not_le
    assumption

variable [IsLinearOrder α]

def min_iff_le_left: a ≤ b ↔ min a b = a := IsLinearOrder.min_iff_le_left
def min_iff_le_right: b ≤ a ↔ min a b = b := IsLinearOrder.min_iff_le_right
def max_iff_le_left: a ≤ b ↔ max a b = b := IsLinearOrder.max_iff_le_left
def max_iff_le_right: b ≤ a ↔ max a b = a := IsLinearOrder.max_iff_le_right

def IsLinearOrder.transfer (α β)
  [LT α] [LT β] [LE α] [LE β] [Min α] [Max α] [Min β] [Max β]
  [IsLinearOrder α]
  (f: β -> α)
  (finj: Function.Injective f)
  (lt_iff: ∀{x y: β}, x < y ↔ f x < f y)
  (le_iff: ∀{x y: β}, x ≤ y ↔ f x ≤ f y)
  (min_def: ∀{x y: β}, f (min x y) = min (f x) (f y))
  (max_def: ∀{x y: β}, f (max x y) = max (f x) (f y)):
  IsLinearOrder β where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.trans lt_iff
    apply Iff.trans (lt_iff_le_and_not_le (α := α))
    apply Iff.intro
    intro ⟨h₀,h₁⟩
    apply And.intro
    apply le_iff.mpr
    assumption
    intro g
    apply h₁
    apply le_iff.mp
    assumption
    intro ⟨h₀,h₁⟩
    apply And.intro
    apply le_iff.mp
    assumption
    intro g
    apply h₁
    apply le_iff.mpr
    assumption
  le_antisymm := by
    intro a b ab ba
    apply finj
    apply le_antisymm
    apply le_iff.mp
    assumption
    apply le_iff.mp
    assumption
  le_total := by
    intro a b
    cases le_total (f a) (f b)
    apply Or.inl; apply le_iff.mpr; assumption
    apply Or.inr; apply le_iff.mpr; assumption
  le_complete := by
    intro a b
    cases le_complete (f a) (f b)
    apply Or.inl; apply le_iff.mpr; assumption
    apply Or.inr; intro g; have := le_iff.mp g; contradiction
  le_trans := by
    intro a b c ab bc
    apply le_iff.mpr
    apply le_trans
    apply le_iff.mp
    assumption
    apply le_iff.mp
    assumption
  min_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply finj
    rw [min_def]
    apply min_iff_le_left.mp
    apply le_iff.mp h
    intro h
    apply le_iff.mpr
    apply min_iff_le_left.mpr
    rw [←min_def]
    congr
  min_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply finj
    rw [min_def]
    apply min_iff_le_right.mp
    apply le_iff.mp h
    intro h
    apply le_iff.mpr
    apply min_iff_le_right.mpr
    rw [←min_def]
    congr
  max_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply finj
    rw [max_def]
    apply max_iff_le_left.mp
    apply le_iff.mp h
    intro h
    apply le_iff.mpr
    apply max_iff_le_left.mpr
    rw [←max_def]
    congr
  max_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply finj
    rw [max_def]
    apply max_iff_le_right.mp
    apply le_iff.mp h
    intro h
    apply le_iff.mpr
    apply max_iff_le_right.mpr
    rw [←max_def]
    congr

def min_le_iff : min a b ≤ k ↔ a ≤ k ∨ b ≤ k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply Or.inl
  assumption
  rw [min_iff_le_right.mp ba] at h
  apply Or.inr
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [min_iff_le_left.mp ab]
  any_goals try rw [min_iff_le_right.mp ba]
  any_goals assumption
  apply le_trans <;> assumption
  apply le_trans <;> assumption

def le_min_iff : k ≤ min a b ↔ k ≤ a ∧ k ≤ b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply And.intro
  assumption
  apply le_trans <;> assumption
  rw [min_iff_le_right.mp ba] at h
  apply And.intro
  apply le_trans <;> assumption
  assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab]
  assumption
  rw [min_iff_le_right.mp ba]
  assumption

def max_le_iff : max a b ≤ k ↔ a ≤ k ∧ b ≤ k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply And.intro
  apply le_trans <;> assumption
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply And.intro
  assumption
  apply le_trans <;> assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab]
  assumption
  rw [max_iff_le_right.mp ba]
  assumption

def le_max_iff : k ≤ max a b ↔ k ≤ a ∨ k ≤ b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply Or.inr
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply Or.inl
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [max_iff_le_left.mp ab]
  any_goals try rw [max_iff_le_right.mp ba]
  any_goals assumption
  apply le_trans <;> assumption
  apply le_trans <;> assumption

def min_lt_iff : min a b < k ↔ a < k ∨ b < k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply Or.inl
  assumption
  rw [min_iff_le_right.mp ba] at h
  apply Or.inr
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [min_iff_le_left.mp ab]
  any_goals try rw [min_iff_le_right.mp ba]
  any_goals assumption
  apply lt_of_le_of_lt <;> assumption
  apply lt_of_le_of_lt <;> assumption

def lt_min_iff : k < min a b ↔ k < a ∧ k < b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply And.intro
  assumption
  apply lt_of_lt_of_le <;> assumption
  rw [min_iff_le_right.mp ba] at h
  apply And.intro
  apply lt_of_lt_of_le <;> assumption
  assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab]
  assumption
  rw [min_iff_le_right.mp ba]
  assumption

def max_lt_iff : max a b < k ↔ a < k ∧ b < k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply And.intro
  apply lt_of_le_of_lt <;> assumption
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply And.intro
  assumption
  apply lt_of_le_of_lt <;> assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab]
  assumption
  rw [max_iff_le_right.mp ba]
  assumption

def lt_max_iff : k < max a b ↔ k < a ∨ k < b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply Or.inr
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply Or.inl
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [max_iff_le_left.mp ab]
  any_goals try rw [max_iff_le_right.mp ba]
  any_goals assumption
  apply lt_of_lt_of_le <;> assumption
  apply lt_of_lt_of_le <;> assumption

def min_le_max (a b: α) : min a b ≤ max a b := by
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab, max_iff_le_left.mp ab]
  assumption
  rw [min_iff_le_right.mp ba, max_iff_le_right.mp ba]
  assumption

def min_le_left (a b: α) : min a b ≤ a := by
  apply min_le_iff.mpr
  apply Or.inl
  rfl

def min_le_right (a b: α) : min a b ≤ b := by
  apply min_le_iff.mpr
  apply Or.inr
  rfl

def le_max_left (a b: α) : a ≤ max a b := by
  apply le_max_iff.mpr
  apply Or.inl
  rfl

def le_max_right (a b: α) : b ≤ max a b := by
  apply le_max_iff.mpr
  apply Or.inr
  rfl

def min_of_le (a b: α) : a ≤ b -> min a b = a := min_iff_le_left.mp
def max_of_le (a b: α) : a ≤ b -> max a b = b := max_iff_le_left.mp

def min_le_comm (a b: α) : min a b ≤ min b a := by
  apply le_min_iff.mpr
  apply And.intro
  apply min_le_right
  apply min_le_left

def min_comm (a b: α) : min a b = min b a := by
  apply le_antisymm
  apply min_le_comm
  apply min_le_comm

def max_le_comm (a b: α) : max a b ≤ max b a := by
  apply max_le_iff.mpr
  apply And.intro
  apply le_max_right
  apply le_max_left

def max_comm (a b: α) : max a b = max b a := by
  apply le_antisymm
  apply max_le_comm
  apply max_le_comm

def min_assoc (a b c: α) : min a (min b c) = min (min a b) c := by
  apply le_antisymm
  · repeat any_goals apply le_min_iff.mpr; apply And.intro
    apply min_le_left
    apply min_le_iff.mpr
    apply Or.inr
    apply min_le_left
    apply min_le_iff.mpr
    apply Or.inr
    apply min_le_right
  · repeat any_goals apply le_min_iff.mpr; apply And.intro
    apply min_le_iff.mpr
    apply Or.inl
    apply min_le_left
    apply min_le_iff.mpr
    apply Or.inl
    apply min_le_right
    apply min_le_right

def max_assoc (a b c: α) : max a (max b c) = max (max a b) c := by
  apply le_antisymm
  · repeat any_goals apply max_le_iff.mpr; apply And.intro
    apply le_max_iff.mpr
    apply Or.inl
    apply le_max_left
    apply le_max_iff.mpr
    apply Or.inl
    apply le_max_right
    apply le_max_right
  · repeat any_goals apply max_le_iff.mpr; apply And.intro
    apply le_max_left
    apply le_max_iff.mpr
    apply Or.inr
    apply le_max_left
    apply le_max_iff.mpr
    apply Or.inr
    apply le_max_right

class IsDecidableLinearOrder (α: Type _) [LE α] [LT α] [Min α] [Max α] extends IsLinearOrder α where
  decLE (a b: α): Decidable (a ≤ b) := by intros; exact inferInstance
  decLT (a b: α): Decidable (a < b) := decidable_of_iff _ (lt_iff_le_and_not_le (a := a) (b := b)).symm
  decEQ (a b: α): Decidable (a = b) := decidable_of_iff (a ≤ b ∧ b ≤ a) (by
  apply Iff.intro
  · rintro ⟨ab,ba⟩
    apply le_antisymm ab ba
  · intro h
    subst h
    apply And.intro <;> rfl)
  min_def (a b: α): min a b = if a ≤ b then a else b := by intros; rfl
  max_def (a b: α): max a b = if a ≤ b then b else a := by intros; rfl

instance : Subsingleton (IsDecidableLinearOrder α) where
  allEq a b := by
    cases a <;> cases b
    congr <;> apply Subsingleton.allEq

instance (priority := 100) [IsDecidableLinearOrder α] : Decidable (a ≤ b) := IsDecidableLinearOrder.decLE _ _
instance (priority := 100) [IsDecidableLinearOrder α] : Decidable (a < b) := IsDecidableLinearOrder.decLT _ _
instance (priority := 100) [IsDecidableLinearOrder α] : Decidable (a = b) := IsDecidableLinearOrder.decEQ _ _

variable [IsDecidableLinearOrder α] [@DecidableRel α (· ≤ ·)]

def min_def [IsDecidableLinearOrder α] : ∀a b: α, min a b = if a ≤ b then a else b := by
  intro a b
  rw [IsDecidableLinearOrder.min_def]
  congr
def max_def [IsDecidableLinearOrder α] : ∀a b: α, max a b = if a ≤ b then b else a := by
  intro a b
  rw [IsDecidableLinearOrder.max_def]
  congr

instance : IsDecidableLinearOrder Bool where
  decLE := by intros; exact inferInstance
  lt_iff_le_and_not_le := by decide
  le_antisymm := by decide
  le_total := by decide
  le_complete := by decide
  le_trans := by decide
  min_def := by decide
  max_def := by decide
  min_iff_le_left := by decide
  min_iff_le_right := by decide
  max_iff_le_left := by decide
  max_iff_le_right := by decide
