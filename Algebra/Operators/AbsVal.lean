import Lean

class AbsoluteValue (α: Sort _) (β: outParam (Sort u)) where
  abs: α -> β

syntax "‖" term "‖"  : term
syntax "‖" term ":" term "‖"  : term

macro_rules
| `(‖$x‖) => `(AbsoluteValue.abs $x)
| `(‖$x : $ty‖) => `(AbsoluteValue.abs ($x : $ty))

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.AbsoluteValue.abs]
def delab_abs_val : Delab := do
  let expr ← getExpr
  let #[_, _, _, x] := expr.getAppArgs | failure
  let x ← delab x
  `(‖$x‖)
