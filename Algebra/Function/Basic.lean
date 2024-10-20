namespace Function

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

def Injective (f: α -> β) : Prop :=
  ∀{a b}, f a = f b -> a = b

namespace Function
