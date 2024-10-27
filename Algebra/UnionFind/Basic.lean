import Algebra.AxiomBlame

namespace UnionFind

variable { items: List Nat }

structure IsRoot (items: List Nat) (a: Nat) : Prop where
  in_bounds: a < items.length
  spec: items[a] = a

instance : Decidable (IsRoot items a) :=
  if h:a < items.length then
  if g:items[a] = a then
    Decidable.isTrue (IsRoot.mk h g)
  else
    Decidable.isFalse fun r => g r.spec
  else
    Decidable.isFalse fun r => h r.in_bounds

structure IsParentOf (items: List Nat) (a b: Nat) : Prop where
  in_bounds_left: a < items.length
  in_bounds_right: b < items.length
  spec: items[a] = b
  different: a ≠ b

-- `RootPath items a` is the node on the path from a to b
inductive RootPath (items: List Nat) : Nat -> Type where
| IsRoot a : IsRoot items a -> RootPath items a
| IsParentOf a b : IsParentOf items a b -> RootPath items b -> RootPath items a

-- `IsAncestorOf items a b` means that...
-- * `a` and `b` share the same root node
-- * `a` is strictly farther away from the root node than `b`
inductive IsAncestorOf (items: List Nat) : Nat -> Nat -> Prop where
| single : IsParentOf items a b -> RootPath items b -> IsAncestorOf items a b
| next : IsParentOf items a b -> IsAncestorOf items b c -> IsAncestorOf items a c

inductive Equiv (items: List Nat) : Nat -> Nat -> Prop where
| refl (a: Nat) : a < items.length -> Equiv items a a
| next (a b c: Nat): IsParentOf items a b -> Equiv items b c -> Equiv items a c
| prev (a b c: Nat): IsParentOf items b a -> Equiv items b c -> Equiv items a c

def IsParentOf.notIsRoot : IsParentOf items a b -> ¬IsRoot items a := by
  intro ⟨_,_,spec,ne⟩  ⟨_,root⟩
  apply ne
  rw [←spec, root]

def IsAncestorOf.notIsRoot : IsAncestorOf items a b -> ¬IsRoot items a := by
  intro r
  cases r with
  | single parent _ => exact parent.notIsRoot
  | next parent => exact parent.notIsRoot

def IsParentOf.determine : IsParentOf items a b -> IsParentOf items a c -> b = c := by
  intro ⟨_,_,spec₀,_⟩ ⟨_,_,spec₁,_⟩
  rw [←spec₀, ←spec₁]

-- there is at most one way to get to a given root
instance : Subsingleton (RootPath items x) where
  allEq := by
    intro a b
    induction a with
    | IsRoot root root_spec =>
      cases b with
      | IsRoot root' root'_spec => rfl
      | IsParentOf _ _ parent  =>
        have := parent.notIsRoot
        contradiction
    | IsParentOf a b' a_parent_b' _ ih  =>
      cases b with
      | IsRoot root' root'_spec =>
        have := a_parent_b'.notIsRoot
        contradiction
      | IsParentOf _ c a_parent_c =>
        cases a_parent_b'.determine a_parent_c
        rw [ih]

def IsAncestorOf.wf (items: List Nat) : WellFounded (flip (IsAncestorOf items)) := by
  apply WellFounded.intro
  intro a
  apply Acc.intro
  intro b path
  induction path with
  | next _ _ => assumption
  | single parent root =>
    clear parent
    induction root with
    | IsRoot root root_spec =>
      apply Acc.intro
      intro c r
      unfold flip at r
      have := r.notIsRoot
      contradiction
    | IsParentOf a' b' a'_parent_b _ ih  =>
      apply Acc.intro
      intro c r
      unfold flip at r
      cases r with
      | single a'_parent_c =>
        cases a'_parent_b.determine a'_parent_c
        assumption
      | next a'_parent_c=>
        cases a'_parent_b.determine a'_parent_c
        apply Acc.inv
        assumption
        assumption

structure RootedNode (items: List Nat) where
  value: Nat

instance : WellFoundedRelation (RootedNode items) where
  rel a b := flip (IsAncestorOf items) a.value b.value
  wf := by
    apply WellFounded.intro
    intro a
    cases a with | mk a =>
    induction a using (IsAncestorOf.wf items).induction with
    | h aval ih =>
      apply Acc.intro
      intro b r
      cases b with | mk b =>
      apply ih
      assumption

def IsAncestorOf.in_bounds_left : IsAncestorOf items a b -> a < items.length := by
  intro h
  cases h with
  | single parent => exact parent.in_bounds_left
  | next parent => exact parent.in_bounds_left

def IsAncestorOf.in_bounds_right : IsAncestorOf items a b -> b < items.length := by
  intro h
  induction h with
  | single parent => exact parent.in_bounds_right
  | next _ _ ih => exact ih

def Equiv.in_bounds : Equiv items a b -> a < items.length ∧ b < items.length := by
  intro eq
  induction eq with
  | refl _ h => exact ⟨h,h⟩
  | next _ _ _ parent _ ih => exact ⟨parent.in_bounds_left,ih.right⟩
  | prev _ _ _ parent _ ih => exact ⟨parent.in_bounds_right,ih.right⟩

def Equiv.in_bounds_left : Equiv items a b -> a < items.length := And.left ∘ in_bounds
def Equiv.in_bounds_right : Equiv items a b -> b < items.length := And.right ∘ in_bounds

def Equiv.trans : Equiv items a b -> Equiv items b c -> Equiv items a c := by
  intro ab bc
  induction ab with
  | refl => exact bc
  | next _ _ _ ab _ ih =>
    apply Equiv.next
    assumption
    apply ih
    assumption
  | prev _ _ _ ab _ ih =>
    apply Equiv.prev
    assumption
    apply ih
    assumption

@[symm]
def Equiv.symm : Equiv items a b -> Equiv items b a := by
  intro ab
  induction ab with
  | refl => apply Equiv.refl; assumption
  | next _ _ _ ab _ ih =>
    apply ih.trans
    apply Equiv.prev
    assumption
    apply Equiv.refl
    apply ab.in_bounds_left
  | prev _ _ _ ab _ ih =>
    apply ih.trans
    apply Equiv.next
    assumption
    apply Equiv.refl
    apply ab.in_bounds_right

def RootPath.pop_head : UnionFind.IsParentOf items a b -> RootPath items a -> RootPath items b := by
  intro ab roota
  cases roota
  have := ab.notIsRoot
  contradiction
  rename_i _ parent
  cases ab.determine parent
  assumption

structure _root_.UnionFind where
  items: List Nat
  -- all items point to some item in the list
  items_inbounds: ∀x ∈ items, x < items.length
  -- all items eventually reach some root node
  -- this is a Prop to ensure that it's not code-gened
  items_rooted: ∀x < items.length, Nonempty (RootPath items x)

def parent_of_next (uf: UnionFind) (n: Nat) (h: n < uf.items.length) (not_root: ¬IsRoot uf.items n) :
  IsParentOf uf.items n uf.items[n] where
  in_bounds_left := h
  in_bounds_right := uf.items_inbounds _ (List.getElem_mem uf.items n h)
  spec := rfl
  different := (not_root <| IsRoot.mk _ ·.symm)

def items.inj  : ∀(a b: UnionFind), a.items = b.items -> a = b
| .mk as _ _, .mk bs _ _, h => by congr

def find (uf: UnionFind) (n: Nat) (nLt: n < uf.items.length) : Nat :=
  if IsRoot uf.items n then
    n
  else
    uf.find uf.items[n] <| by
      apply uf.items_inbounds
      exact List.getElem_mem uf.items n nLt

termination_by (RootedNode.mk n: RootedNode uf.items)
decreasing_by
  have : IsParentOf uf.items n uf.items[n] := by
    apply IsParentOf.mk
    apply uf.items_inbounds
    exact List.getElem_mem uf.items n nLt
    rfl
    rename_i g
    intro h
    apply g
    apply IsRoot.mk
    symm
    assumption
  cases uf.items_rooted n nLt
  apply IsAncestorOf.single
  assumption
  apply RootPath.pop_head
  assumption
  assumption

def find_is_root (uf: UnionFind) (n: Nat) nLt : IsRoot uf.items (uf.find n nLt) := by
  have ⟨rooted⟩ := uf.items_rooted n nLt
  induction rooted with
  | IsRoot a root =>
    unfold find
    rw [if_pos]
    assumption
    exact root
  | IsParentOf a b parent  root ih =>
    unfold find
    rw [if_neg]
    have := parent_of_next uf a nLt parent.notIsRoot
    cases this.determine parent
    apply ih
    exact parent.notIsRoot

def find_of_is_root {uf: UnionFind} {n: Nat} : (h: IsRoot uf.items n) -> uf.find n h.in_bounds = n := by
  intro root
  unfold find
  rw [if_pos]
  assumption

def find_of_is_parent {uf: UnionFind} {a b: Nat} : (h: IsParentOf uf.items a b) -> uf.find a h.in_bounds_left = uf.find b h.in_bounds_right := by
  intro parent
  rw [find, if_neg]
  congr
  exact (parent_of_next uf a parent.in_bounds_left parent.notIsRoot).determine parent
  exact parent.notIsRoot

def find_of_ancestor {uf: UnionFind} {a b: Nat} : (h: IsAncestorOf uf.items a b) -> uf.find a h.in_bounds_left = uf.find b h.in_bounds_right := by
  intro h
  induction h with
  | single parent => rw [find_of_is_parent parent]
  | next parent _ ih => rw [find_of_is_parent parent, ih]

def find_of_equiv {uf: UnionFind} {a b: Nat} : (h: Equiv uf.items a b) -> uf.find a h.in_bounds_left = uf.find b h.in_bounds_right := by
  intro eq
  induction eq with
  | refl => rfl
  | next a b c ab bc ih => rw [←ih, find_of_is_parent ab]
  | prev a b c ba bc ih => rw [←ih, find_of_is_parent ba]

def Equiv.ofIsParent : IsParentOf items b a -> Equiv items a b := by
  intro h
  apply Equiv.prev
  assumption
  apply Equiv.refl
  exact h.in_bounds_left

def Equiv.find_left (uf: UnionFind) (a: Nat) (aLt) : Equiv uf.items (uf.find a aLt) a := by
  have ⟨rooteda⟩ := uf.items_rooted a aLt
  induction rooteda with
  | IsRoot a roota =>
    rw [find_of_is_root roota]
    apply Equiv.refl
    assumption
  | IsParentOf a b ab _ ih =>
    apply Equiv.trans _ (Equiv.trans (ih _) _)
    exact ab.in_bounds_right
    rw [find_of_is_parent ab]
    apply Equiv.refl
    have := find_is_root uf b ab.in_bounds_right
    exact this.in_bounds
    exact Equiv.ofIsParent ab

def Equiv.find_right (uf: UnionFind) (a: Nat) (aLt) : Equiv uf.items a (uf.find a aLt) := by
  symm
  apply find_left

def find_eq_iff_equiv (uf: UnionFind) (a b: Nat) aLt bLt : Equiv uf.items a b ↔ uf.find a aLt = uf.find b bLt := by
  apply Iff.intro
  · exact find_of_equiv
  · intro eq
    have ⟨rooteda⟩ := uf.items_rooted a aLt
    induction rooteda with
    | IsRoot a roota =>
      rw [find_of_is_root roota] at eq
      rw [eq]
      apply Equiv.find_left
    | IsParentOf a c ac _ ih =>
      apply Equiv.trans
      symm
      exact Equiv.ofIsParent ac
      apply ih
      rw [←eq, find_of_is_parent ac]

def set_root_self.helper : (h: a < items.length) -> items[a] = b -> items.set a b = items := by
  intro h root
  induction items generalizing a with
  | nil => rfl
  | cons x xs ih =>
    cases a with
    | zero =>
      unfold List.set
      rw [←root]
      rfl
    | succ a =>
      unfold List.set
      rw [ih]
      apply Nat.lt_of_succ_lt_succ
      assumption
      assumption

def set_root_self : IsRoot items a -> items.set a a = items := by
  intro root
  rw [set_root_self.helper]
  exact root.in_bounds
  exact root.spec

def merge_left (uf: UnionFind) (a b: Nat) (aLt: a < uf.items.length) (bLt: b < uf.items.length) : UnionFind where
  items := uf.items.set (uf.find b bLt) (uf.find a aLt)
  items_inbounds := by
    intro x mem
    rw [List.length_set]
    cases List.mem_or_eq_of_mem_set mem
    apply uf.items_inbounds
    assumption
    subst x
    have := find_is_root uf a aLt
    exact this.in_bounds
  items_rooted := by
    intro n nLt
    have ⟨rootedn⟩ := uf.items_rooted n (by
      rw [List.length_set] at nLt
      exact nLt)
    if find_eq:uf.find a aLt = uf.find b bLt then
      rw [←find_eq]
      rw [set_root_self]
      apply uf.items_rooted
      rw [List.length_set] at nLt
      assumption
      exact find_is_root uf a aLt
    else
      induction rootedn with
      | IsRoot r rootr =>
        if h₀:uf.find r rootr.in_bounds = uf.find b bLt then
          -- if this is the root that was just merged
          have := find_is_root uf a aLt
          apply Nonempty.intro
          apply RootPath.IsParentOf
          · apply IsParentOf.mk
            rw [List.length_set]
            exact this.in_bounds
            rw [List.getElem_set, if_pos]
            rw [find_of_is_root rootr] at h₀
            exact h₀.symm
            assumption
            rw [find_of_is_root rootr] at h₀
            subst r
            exact Ne.symm find_eq
          · apply RootPath.IsRoot
            apply IsRoot.mk
            rw [List.getElem_set, if_neg]
            exact this.spec
            exact Ne.symm find_eq
            rw [List.length_set]
            exact this.in_bounds
        else
          -- if this is a different root from the one that was just merged
          have := find_is_root uf a aLt
          apply Nonempty.intro
          apply RootPath.IsRoot
          apply IsRoot.mk
          rw [List.getElem_set, if_neg, rootr.spec]
          rw [find_of_is_root rootr] at h₀
          exact Ne.symm h₀
          assumption
      | IsParentOf a b ab _ ih =>
        replace ⟨ih⟩ := ih (by
          rw [List.length_set]
          exact ab.in_bounds_right)
        apply Nonempty.intro
        apply RootPath.IsParentOf
        · apply IsParentOf.mk
          rw [List.length_set]
          exact ab.in_bounds_right
          rw [List.getElem_set, if_neg, ab.spec]
          intro h
          subst a
          exact ab.notIsRoot (find_is_root _ _ _)
          assumption
          exact ab.different
        exact ih

def merge_length : (merge_left uf a b aLt bLt).items.length = uf.items.length := by
  unfold merge_left
  rw [List.length_set]

def RootPath.of_equiv_and_root : Equiv items a b -> UnionFind.IsRoot items b -> Nonempty (RootPath items a) := sorry

end UnionFind
