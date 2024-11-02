import Algebra.Ty.Notation
import Algebra.Function.Basic

class DFunLike (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α → Sort*) where
  coe : F → ∀ a : α, β a
  coe_inj : Function.Injective coe

instance [dfl: DFunLike F α β] : CoeFun F (fun _ => ∀x: α, β x) := ⟨dfl.coe⟩

abbrev FunLike F α β := DFunLike F α (fun _ => β)

instance (priority := 100) : DFunLike (∀x: α, B x) α B where
  coe := id
  coe_inj := id

def coe_inj [fl: FunLike F α β] (f g: F) : (f: α -> β) = g -> f = g := fl.coe_inj
