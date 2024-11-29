import Algebra.Fintype.StdFin
import Algebra.AxiomBlame

variable {a: Sort u} {β: α -> Type v} {F: ∀x: α, β x}

inductive Mapping : ∀ (as: Nat), (Fin as -> Type _) -> Type _ where
| nil : Mapping 0 f
| cons {f: Fin n.succ -> Type _} : f ⟨0, Nat.zero_lt_succ _⟩  -> Mapping n (fun x => f x.succ) -> Mapping n.succ f

-- structure Mapping (as: Nat) (bs: Fin as -> Type v) where
--   indices: List Nat
--   indices_len: indices.length = as
--   spec: ∀(x: Fin indices.length), indices[x]'x.isLt < bs (x.cast indices_len)

def Mapping.toFn (m: Mapping as bs) : ∀a: Fin as, (bs a) := by
  intro a
  match as with
  | 0 => exact a.elim0
  | as + 1 =>
    match m with
    | .cons val m =>
    match a with
    | ⟨0, _⟩ => exact val
    | ⟨a'+1, isLt⟩ =>
      apply m.toFn ⟨_, _⟩
      apply Nat.lt_of_succ_lt_succ
      assumption

def Mapping.ofFn (h: ∀a: Fin as, (bs a)) : Mapping as bs :=
  match as with
  | 0 => Mapping.nil
  | _ + 1 => Mapping.cons (h ⟨0, Nat.zero_lt_succ _⟩) (Mapping.ofFn (fun x => h x.succ))

def Mapping.ofFn_toFn {bs: ∀a: Fin as, Type _} (h: ∀a: Fin as, (bs a)) : (Mapping.ofFn h).toFn = h :=
  sorry

def List.ext_getElem' (as bs: List α) (h: as.length = bs.length) :
  (∀(x: Nat) (h₀: x < as.length) (h₁: x < bs.length), as[x] = bs[x]) ->
  as = bs := by
  intro g
  induction as generalizing bs with
  | nil => cases bs <;> trivial
  | cons a as ih =>
    cases bs
    trivial
    congr
    rename_i b bs
    exact g 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    apply ih
    apply Nat.succ.inj
    assumption
    intro x h₁ h₂
    apply g x.succ
    apply Nat.succ_lt_succ
    assumption
    apply Nat.succ_lt_succ
    assumption

-- def Mapping.toFn.inj : Function.Injective (Mapping.toFn (as := as) (bs := bs)) := by
--   intro x y h
--   have : ∀z, x.toFn z = y.toFn z := by
--     intro; rw [h]
--   unfold toFn at this
--   dsimp at this
--   apply Mapping.indices.inj
--   apply List.ext_getElem'
--   rw [x.indices_len, y.indices_len]
--   intro n h₁ h₂
--   rw [Fin.mk.inj (this ⟨n, x.indices_len ▸ h₁⟩)]

def mappings.{v₀} (as: Nat) (bs: Fin as -> Type v₀) [fbs: ∀a, Fintype (bs a)] :
  List (Mapping as bs) :=
  have fbs := fbs
  match as with
  | 0 => [Mapping.nil]
  | as + 1 =>
    have prev_mappings := mappings as (fun x => bs x.succ)
    (fbs ⟨0, Nat.zero_lt_succ _⟩).all.flatMap
      fun b => prev_mappings.map (Mapping.cons b ·)

def mappings.mem (as: Nat) (bs: Fin as -> Type _) [fbs: ∀a, Fintype (bs a)] : ∀{x: Mapping as bs}, x ∈ mappings as bs := by
  sorry

def mappings.Nodup (as: Nat) (bs: Fin as -> Type _) [fbs: ∀a, Fintype (bs a)] : (mappings as bs).Nodup := by
  sorry

def eqRec_eq_of_heq {α β : Sort u} {a : α} {b : β} (h₁ : α = β) : HEq a b -> Eq.rec (motive := fun α _ => α) a h₁ = b := by
  intro h₂
  subst h₁
  cases h₂
  rfl

instance instFintypePi [DecidableEq α] [∀x, DecidableEq (β x)] [as: Fintype α] [bs: ∀x, Fintype (β x)] : Fintype (∀x, β x) where
  all := by
    have := mappings as.card (fun a => β as[a])
    apply this.map
    intro m a
    have := m.toFn (as.indexOf a)
    rw [Fintype.getElem_indexOf] at this
    exact this
  all_nodups := by
    dsimp
    apply List.nodup_map
    apply mappings.Nodup
    intro x y eq
    dsimp at eq

    sorry
  all_spec := by
    intro x
    dsimp
    apply List.mem_map'.mpr
    refine ⟨?_, ?_⟩
    apply Mapping.ofFn
    intro a
    apply x
    apply And.intro
    apply mappings.mem
    rw [Mapping.ofFn_toFn]
    funext z
    show cast _ (x as[as.indexOf z]) = _
    apply eqRec_eq_of_heq
    rw [Fintype.getElem_indexOf]
