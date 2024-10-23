import Init.Data.Nat.Div
import Algebra.List.Defs

open Lean

syntax ".[" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(.[ $elems,* ]) => do
    -- NOTE: we do not have `TSepArray.getElems` yet at this point
    let rec expandListLit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(list.cons $(⟨elems.elemsAndSeps.get! i⟩) $result))
    let size := elems.elemsAndSeps.size
    if size < 64 then
      expandListLit size (size % 2 == 0) (← ``(list.nil))
    else
      `(%[ $elems,* | list.nil ])
