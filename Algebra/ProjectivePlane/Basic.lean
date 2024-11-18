import Algebra.Ty.Notation

instance Nat.decidableExistsFin (P: Fin n -> Prop) [d: DecidablePred P] : Decidable (∃x, P x) := by
  match n, P, d with
  | 0, P, d => exact .isFalse fun ⟨x, _⟩ => x.elim0
  | n + 1, P, d =>
    exact match d ⟨_, Nat.zero_lt_succ _⟩  with
    | .isTrue h => .isTrue ⟨_, h⟩
    | .isFalse g =>
    match decidableExistsFin (fun x => P x.succ) with
    | .isTrue h => .isTrue (
        have ⟨x, Px⟩ := h
        ⟨_, Px⟩)
    | .isFalse h => .isFalse <| by
      intro ⟨x,Px⟩
      cases x with | mk val valLt =>
      cases val with
      | zero => contradiction
      | succ val =>
      apply h
      exact ⟨⟨val, Nat.lt_of_succ_lt_succ valLt⟩, Px⟩

abbrev IsProjectivePlane.is_nondegen (incident: P -> L -> Prop) (l: L) (a b c: P) :=
  incident a l -> incident b l -> incident c l -> False

open IsProjectivePlane in
class IsProjectivePlane {P L: Type*} (incident: P -> L -> Prop): Prop where
  unique_line: ∀a b: P, a ≠ b ->
    ∃l, incident a l ∧ incident b l ∧ ∀l', incident a l' -> incident b l' -> l = l'
  unique_point: ∀a b: L, a ≠ b ->
    ∃p, incident p a ∧ incident p b ∧ ∀p', incident p' a -> incident p' b -> p = p'
  nondegen: ∃a b c d: P, [a, b, c, d].Nodup ∧
    ∀l, is_nondegen incident l a b c
      ∧ is_nondegen incident l a b d
      ∧ is_nondegen incident l a c d
      ∧ is_nondegen incident l b c d

open IsProjectivePlane in
structure ProjectivePlane (P L: Type*) where
  -- is a point on a line
  incident: P -> L -> Prop
  unique_line: ∀a b: P, a ≠ b ->
    ∃l, incident a l ∧ incident b l ∧ ∀l', incident a l' -> incident b l' -> l = l'
  unique_point: ∀a b: L, a ≠ b ->
    ∃p, incident p a ∧ incident p b ∧ ∀p', incident p' a -> incident p' b -> p = p'
  nondegen: ∃a b c d: P, [a, b, c, d].Nodup ∧
    ∀l, is_nondegen incident l a b c
      ∧ is_nondegen incident l a b d
      ∧ is_nondegen incident l a c d
      ∧ is_nondegen incident l b c d

def ProjectivePlane.IsProjectivePlane (p: ProjectivePlane P L) :
  IsProjectivePlane p.incident where
  unique_line := p.unique_line
  unique_point := p.unique_point
  nondegen := p.nondegen

def ProjectivePlane.fano_incident (a b: Fin 7) : Prop :=
  (a, b) ∈
 [(0, 0), (1, 0), (2, 0),
  (2, 1), (3, 1), (4, 1),
  (4, 2), (5, 2), (0, 2),
  (0, 3), (6, 3), (3, 3),
  (1, 4), (6, 4), (4, 4),
  (2, 5), (6, 5), (5, 5),
  (1, 6), (3, 6), (5, 6)]

instance ProjectivePlane.dec_fano_incident : Decidable (ProjectivePlane.fano_incident a b) := by
  unfold fano_incident
  exact inferInstance

def ProjectivePlane.FanoPlane : ProjectivePlane (Fin 7) (Fin 7) where
  incident := fano_incident
  unique_line := by decide +kernel
  unique_point := by decide +kernel
  nondegen := by decide +kernel

def ProjectivePlane.fineq (p: ProjectivePlane (Fin P) (Fin L)) : P = L := by
  have ⟨a,b,c,d,nodop,nondegen⟩  := p.nondegen
  sorry

def ProjectivePlane.BruckRyserChowla (p: ProjectivePlane (Fin P) (Fin L)) :
  P % 4 = 1 ∨ P % 4 = 2 -> ∃x y, P = x * x + y * y := by
  intro h
  sorry
