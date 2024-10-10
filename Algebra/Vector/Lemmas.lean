import Algebra.Vector.Ops

def Vector.nil_append
  (vs: Vector α n):
  (nil: Vector α 0) ++ vs = vs := rfl

#print axioms Vector.nil_append

def Vector.append_nil
  (vs: Vector α n):
  vs ++ (nil: Vector α 0) =v vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    apply cons.congrEq
    apply And.intro rfl
    exact ih

#print axioms Vector.nil_append

def Vector.cons_append
  (v: α)
  (vs: Vector α n) (ws: Vector α m):
  (cons v vs) ++ ws = cons v (vs ++ ws) := rfl

#print axioms Vector.cons_append

def Vector.mem_append { vs: Vector α n } { ws: Vector α m }:
  ∀{x}, x ∈ vs ++ ws ↔ x ∈ vs ∨ x ∈ ws := by
  intro x
  apply Iff.intro
  case mp =>
    intro x_in_app
    induction vs with
    | nil => exact Or.inr x_in_app
    | cons v vs ih =>
      cases Vector.mem_cons x_in_app with
      | inl =>
        subst x
        apply Or.inl
        apply Mem.head
      | inr mem_app =>
        cases ih mem_app with
        | inr h => exact Or.inr h
        | inl h =>
          apply Or.inl
          apply Mem.tail
          assumption
  case mpr =>
    intro h
    induction vs with
    | nil =>
      cases h
      contradiction
      assumption
    | cons v vs ih =>
      rw [Vector.cons_append]
      cases h with
      | inl h =>
        cases h with
        | head _ _ => apply Mem.head
        | tail v vs x x_in_vs =>
          apply Mem.tail
          apply ih
          apply Or.inl
          assumption
      | inr h =>
        apply Mem.tail
        apply ih
        apply Or.inr
        assumption

#print axioms Vector.mem_append

def Vector.nil_flatten:
  (nil: Vector (Vector α m) 0).flatten = .nil := rfl

#print axioms Vector.nil_flatten

def Vector.flatten_nil (vs: Vector (Vector α 0) m):
  vs.flatten =v .nil := by
  apply Vector.eq_nil_of_zero_len
  rw [nat.mul_zero]

#print axioms Vector.flatten_nil

def Vector.cons_flatten
  (v: (Vector α n))
  (vs: Vector (Vector α n) m):
  (cons v vs).flatten = v ++ vs.flatten := rfl

#print axioms Vector.cons_flatten

def Vector.mem_flatten { vs: Vector (Vector α m) n }:
  ∀{x}, x ∈ vs.flatten ↔ ∃ws, x ∈ ws ∧ ws ∈ vs := by
  induction vs with
  | nil =>
    intro x
    apply Iff.intro
    intro; contradiction
    intro h
    have ⟨ _, _, _ ⟩ := h
    contradiction
  | cons v vs ih =>
    intro x
    apply Iff.intro
    case mp =>
      rw [Vector.cons_flatten]
      intro in_flatten
      cases Vector.mem_append.mp in_flatten with
      | inl h =>
        exists  v
        refine ⟨ h, ?A ⟩
        apply Mem.head
      | inr h =>
        have ⟨ ws, h, g ⟩  := ih.mp h
        exists ws
        refine ⟨ h, ?B ⟩
        apply Mem.tail
        assumption
    case mpr =>
      intro ex
      rw [Vector.cons_flatten]
      apply Vector.mem_append.mpr
      have ⟨ ws, h, g ⟩ := ex
      clear ex
      cases g with
      | head v vs =>
        apply Or.inl
        assumption
      | tail v vs ws ws_mem =>
        exact Or.inr (ih.mpr ⟨ ws, h, ws_mem ⟩)

#print axioms Vector.mem_flatten

def Vector.mem_from_list {list: List α} :
  ∀{x}, x ∈ list ↔ x ∈ Vector.from_list list := by
  intro k
  induction list with
  | nil => apply Iff.intro <;> (intro; contradiction)
  | cons x xs ih =>
    apply Iff.intro
    case mp =>
      intro k_in_cons
      cases k_in_cons
      apply Mem.head
      apply Mem.tail
      apply ih.mp
      assumption
    case mpr =>
      intro k_in_cons
      cases Vector.mem_cons k_in_cons
      subst x
      apply List.Mem.head
      apply List.Mem.tail
      apply ih.mpr
      assumption

#print axioms Vector.mem_from_list

def Vector.cons_to_list { v: α } { vs: Vector α n } :
  (cons v vs).to_list = v::vs.to_list := rfl

#print axioms Vector.cons_to_list

def Vector.mem_to_list {vs: Vector α n} :
  ∀{x}, x ∈ vs ↔ x ∈ vs.to_list := by
  intro k
  induction vs with
  | nil => apply Iff.intro <;> (intro; contradiction)
  | cons x xs ih =>
    apply Iff.intro
    case mp =>
      intro k_in_cons
      cases Vector.mem_cons k_in_cons
      subst x
      apply List.Mem.head
      apply List.Mem.tail
      apply ih.mp
      assumption
    case mpr =>
      intro k_in_cons
      cases k_in_cons
      apply Mem.head
      apply Mem.tail
      apply ih.mpr
      assumption

#print axioms Vector.mem_to_list

def Vector.from_list_to_list { list: List α }
  : (Vector.from_list list).to_list = list := by
  induction list with
  | nil => rfl
  | cons v vs ih =>
    unfold Vector.from_list Vector.to_list
    congr

#print axioms Vector.from_list_to_list

def Vector.to_list_from_list { vs: Vector α n }
  : Vector.from_list vs.to_list =v vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [Vector.cons_to_list]
    unfold Vector.from_list
    apply Vector.cons.congrEq
    apply And.intro rfl
    exact ih

#print axioms Vector.from_list_to_list

def Vector.to_list_of_veq
  { vs: Vector α n }
  { ws: Vector α m }:
  vs =v ws -> vs.to_list = ws.to_list := by
  intro eq
  cases eq
  rfl

#print axioms Vector.from_list_to_list

-- def Vector.get_append_left
--   (vs: Vector α n) (ws: Vector α m) (idx: { x: nat // x < n }):
--   (vs ++ ws).get ⟨ idx.val, by
--     apply TotalOrder.lt_of_lt_of_le
--     exact idx.property
--     exact nat.add.le_left n m ⟩ = vs.get idx := by
--     cases idx with
--     | mk idx idxLt =>
--     induction vs generalizing idx with
--     | nil =>
--       have := nat.not_lt_zero idxLt
--       contradiction
--     | cons v vs ih =>
--       cases idx with
--       | zero => rfl
--       | succ idx =>
--         unfold Vector.get
--         dsimp
--         rename_i n
--         split
--         rw [nat.succ_add n m] at *
--         contradiction
--         rename_i n' _ vs' _ _ h₀ h _ _
--         rw [nat.succ_add n m] at *
--         injection h₀
--         subst n'
--         cases h
--         apply ih

-- #print axioms Vector.get_append_left

-- def Vector.get_append_right
--   (vs: Vector α n) (ws: Vector α m) (idx: { x: nat // n ≤ x ∧ x < n + m }):
--   (vs ++ ws).get ⟨ idx.val, idx.property.right ⟩ = ws.get ⟨ idx.val - n, by
--     cases idx with
--     | mk idx idxLt =>
--     dsimp
--     apply @nat.add.lt_cancel_right _ _ n
--     rw [nat.sub_add_inv, nat.add.comm]
--     exact idxLt.right
--     exact idxLt.left ⟩  := by
--     cases idx with
--     | mk idx idxLt =>
--     induction vs generalizing idx with
--     | nil => rfl
--     | cons v vs ih =>
--       cases idx with
--       | zero =>
--         have := nat.le_zero idxLt.left
--         contradiction
--       | succ idx =>
--         dsimp
--         rename_i n'
--         conv in idx.succ - n'.succ => {
--           rw [nat.succ_sub_succ]
--         }
--         apply ih
--         exact idxLt

-- #print axioms Vector.get_append_right

def Vector.append_veq
  { vs: Vector α n }
  { vs': Vector α m }
  { ws: Vector α o }
  { ws': Vector α p }:
  vs =v vs' -> ws =v ws' -> vs ++ ws =v vs' ++ ws' := by
  intro veq weq
  cases veq
  cases weq
  rfl

#print axioms Vector.append_veq

def Vector.append_left_veq
  { vs: Vector α n }
  { vs': Vector α m }
  { ws: Vector α o }:
  vs =v vs' -> vs ++ ws =v vs' ++ ws := by
  intro veq
  cases veq
  rfl

#print axioms Vector.append_left_veq

def Vector.append_right_veq
  { vs: Vector α n }
  { ws: Vector α m }
  { ws': Vector α o }:
  ws =v ws' -> vs ++ ws =v vs ++ ws' := by
  intro veq
  cases veq
  rfl

#print axioms Vector.append_right_veq

def Vector.flatten_veq
  { vs: Vector (Vector α m) n }
  { ws: Vector (Vector α m) o }:
  vs =v ws -> vs.flatten =v ws.flatten := by
  intro veq
  cases veq
  rfl

#print axioms Vector.flatten_veq

def Vector.nil_reverse : (Vector.nil : Vector α 0).reverse = .nil := rfl

def Vector.append_assoc (as: Vector α n) (bs: Vector α m) (cs: Vector α o) :
  as ++ bs ++ cs =v as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as =>
    repeat rw [cons_append]
    apply cons.congrEq
    apply And.intro
    rfl
    assumption

-- reverse vs then append ws to it
def Vector.reverse_append (vs: Vector α n) (ws: Vector α m) :
  Vector α (n + m) :=
  match vs with
  | nil => ws
  | cons v vs =>
    Vector.cast (vs.reverse_append (cons v ws)) (by
      rw [nat.add_succ, nat.succ_add])

def Vector.reverseAux_cons (vs: Vector α n) (ws: Vector α m) :
  vs.reverseAux ws =v vs.reverse ++ ws := by
  induction vs generalizing m with
  | nil => apply Vector.cast_eqv
  | cons v vs ih =>
  unfold reverseAux
  apply NatEq.trans (Vector.cast_eqv _ _)
  apply NatEq.trans (ih (cons v ws))
  conv => {
    rhs
    unfold reverse reverseAux
  }
  apply NatEq.trans _ (Vector.append_veq (Vector.cast_eqv _ _).symm (NatEq.refl _))
  apply NatEq.trans _ (Vector.append_veq (ih (cons v nil)).symm (NatEq.refl _))
  apply NatEq.trans _  (append_assoc _ _ _).symm
  rfl

def Vector.reverse_cons (v: α) (vs: Vector α n) :
  (Vector.cons v vs).reverse =v vs.reverse ++ (Vector.cons v .nil) := by
  apply NatEq.trans _ (Vector.reverseAux_cons vs (cons v nil))
  rfl
