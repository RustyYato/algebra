import Algebra.ClassicLogic

namespace Function

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

def Injective (f: α -> β) : Prop :=
  ∀{a b}, f a = f b -> a = b

def Bijective (f: α -> β) : Prop :=
  Injective f ∧ Surjective f

variable {f: α -> β}

def Bijective.Injective : Bijective f -> Injective f := And.left
def Bijective.Surjective : Bijective f -> Surjective f := And.right

attribute [irreducible] Bijective

def Surjective.exists_inv : Surjective f -> ∃g: β -> α, ∀x, f (g x) = x :=
  Classical.axiomOfChoice

namespace Function
