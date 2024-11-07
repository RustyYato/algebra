import Lean

class Invert (α: Sort u) (P: outParam (α -> Prop)) where
  invert: ∀a: α, P a -> α

class CheckedDiv (α: Sort u) (P: outParam (α -> Prop)) where
  checked_div: α -> ∀den: α, P den -> α

syntax "invert_tactic" : tactic

macro_rules | `(tactic|invert_tactic) => `(tactic|trivial)

syntax:max term noWs "⁻¹" : term
macro_rules | `($x⁻¹) => `(Invert.invert $x (by invert_tactic))

syntax:70 (name := checked_div) term:70 " /? " term:71 : term
macro_rules | `($x /? $y) => `(CheckedDiv.checked_div $x $y (by invert_tactic))

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedDiv.checked_div]
def delab_checked_div : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x /? $y)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.Invert.invert]
def delab_checked_invert : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, _] := expr.getAppArgs | failure
  let x ← delab x
  `($x⁻¹)
