inductive list (α: Type _) where
| nil
| cons (a: α) (as: list α)
deriving DecidableEq

def list.toList : list α -> List α
| .nil => .nil
| .cons a as => .cons a as.toList

instance [Repr α] : Repr (list α) where
  reprPrec l n := Repr.reprPrec (l.toList) n
