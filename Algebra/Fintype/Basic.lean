import Algebra.Fintype.Finset

class Fintype (α: Type _) where
  all: Finset α
  all_spec: ∀x, x ∈ all

instance : Fintype Bool where
  all := .ofList .[true, false] (by decide)
  all_spec := by decide

instance : Subsingleton (Fintype α) where
  allEq := by
    intro a b
    cases a with | mk all_a all_a_spec =>
    cases b with | mk all_b all_b_spec =>
    congr
    ext a
    apply Iff.intro <;> intro
    apply all_b_spec
    apply all_a_spec

def Fintype.card (f: Fintype α) := f.all.card
