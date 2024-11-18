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

class IsProjectivePlane {P L: Type*} (incident: P -> L -> Prop): Prop where
  unique_line: ∀a b: P, a ≠ b ->
    ∃l, incident a l ∧ incident b l ∧ ∀l', incident a l' -> incident b l' -> l = l'
  unique_point: ∀a b: L, a ≠ b ->
    ∃p, incident p a ∧ incident p b ∧ ∀p', incident p' a -> incident p' b -> p = p'
  nondegen: ∃a b c d: P, [a, b, c, d].Nodup ∧
    ∀l a' b' c', [a', b', c'].Sublist [a, b, c, d] -> incident a' l -> incident b' l -> incident c' l -> False

structure ProjectivePlane (P L: Type*) where
  -- is a point on a line
  incident: P -> L -> Prop
  unique_line: ∀a b: P, a ≠ b ->
    ∃l, incident a l ∧ incident b l ∧ ∀l', incident a l' -> incident b l' -> l = l'
  unique_point: ∀a b: L, a ≠ b ->
    ∃p, incident p a ∧ incident p b ∧ ∀p', incident p' a -> incident p' b -> p = p'
  nondegen: ∃a b c d: P, [a, b, c, d].Nodup ∧
    ∀l a' b' c', [a', b', c'].Sublist [a, b, c, d] -> incident a' l -> incident b' l -> incident c' l -> False

def ProjectivePlane.fano_incident (a b: Fin 7) : Prop :=
  (a, b) ∈
 [(0, 0),
  (1, 0),
  (2, 0),
  (2, 1),
  (3, 1),
  (4, 1),
  (4, 2),
  (5, 2),
  (0, 2),
  (0, 3),
  (6, 3),
  (3, 3),
  (1, 4),
  (6, 4),
  (4, 4),
  (2, 5),
  (6, 5),
  (5, 5),
  (1, 6),
  (3, 6),
  (5, 6)]

instance ProjectivePlane.dec_fano_incident : Decidable (ProjectivePlane.fano_incident a b) := by
  unfold fano_incident
  exact inferInstance

def ProjectivePlane.FanoPlane : ProjectivePlane (Fin 7) (Fin 7) where
  incident := fano_incident
  unique_line := by decide
  unique_point := by decide
  nondegen := by decide
