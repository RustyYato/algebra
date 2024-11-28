import Algebra.Ty.Basic

class Fintype (α: Type _) where
  all: List α
  all_nodups: all.Nodup
  all_spec: ∀x, x ∈ all

instance : Fintype Bool where
  all := [true, false]
  all_nodups := by decide
  all_spec := by decide

def List.pull_to_head (x: α) (as: List α) (mem: x ∈ as) : ∃as', as ≈ x::as' := by
  induction mem with
  | head _ => exact ⟨_, List.Perm.refl _⟩
  | tail a _ ih =>
    obtain ⟨as', prf⟩ := ih
    exists (a::as')
    apply List.Perm.trans
    apply List.Perm.cons
    assumption
    apply List.Perm.trans
    apply List.Perm.swap
    apply List.Perm.cons
    apply List.Perm.symm
    apply List.Perm.refl

def Fintype.perm (a b: Fintype α) : a.all ≈ b.all := by
  cases a with | mk as as_nodup as_spec =>
  cases b with | mk bs bs_nodup bs_spec =>
  dsimp

  have mem_iff : ∀{x}, x ∈ as ↔ x ∈ bs := by
    intro x
    apply Iff.intro <;> intro _
    apply bs_spec
    apply as_spec
  clear bs_spec as_spec

  induction as_nodup generalizing bs with
  | nil =>
    cases bs with
    | nil => apply List.Perm.refl
    | cons b bs =>
      have := mem_iff.mpr (List.Mem.head _)
      contradiction
  | cons a_not_in_as _ ih =>
    rename_i a as _
    have ⟨bs', bs_perm⟩ := List.pull_to_head a bs (mem_iff.mp (List.Mem.head _))
    replace a_not_in_as : a ∉ as := by
      intro h
      apply a_not_in_as
      assumption
      rfl
    replace a_not_in_bs' : a ∉ bs' := by
      cases (bs_nodup.perm bs_perm) with | cons a_notin_bs' _ =>
      intro h
      apply a_notin_bs'
      assumption
      rfl
    apply List.Perm.trans _ bs_perm.symm
    apply List.Perm.cons
    apply ih
    exact (bs_nodup.perm bs_perm).tail
    intro x
    apply Iff.intro
    · intro x_in_as
      cases bs_perm.mem_iff.mp <| mem_iff.mp (List.Mem.tail _ x_in_as)
      contradiction
      assumption
    · intro h
      cases mem_iff.mpr <| bs_perm.mem_iff.mpr (List.Mem.tail _ h)
      contradiction
      assumption

def Fintype.card (f: Fintype α) := f.all.length

def Fintype.card_eq (f g: Fintype α) :
  f.card = g.card := by
  unfold card
  rw [List.Perm.length_eq]
  apply perm

def List.nodup_map (f: α -> β) (l: List α) : l.Nodup -> Function.Injective f -> (l.map f).Nodup := by
  intro nodup inj
  induction nodup with
  | nil => apply List.Pairwise.nil
  | cons a_notin_as _ ih =>
    apply List.Pairwise.cons
    intro x mem h
    replace ⟨y, y_in_as, mem⟩ := List.mem_map.mp mem
    have := a_notin_as _ y_in_as
    subst h
    apply this
    symm
    apply inj
    assumption
    assumption

def List.nodup_append (as bs: List α) : as.Nodup -> bs.Nodup -> (∀x, ¬(x ∈ as ∧ x ∈ bs)) -> (as ++ bs).Nodup := by
  intro as_nodup bs_nodup no_common_elems
  induction as_nodup with
  | nil => exact bs_nodup
  | cons a_notin_as _ ih =>
    rename_i a as _
    apply List.Pairwise.cons
    intro x mem
    replace mem := List.mem_append.mp mem
    rcases mem with x_in_as | x_in_bs
    intro h
    apply a_notin_as
    assumption
    assumption
    intro h
    subst h
    apply no_common_elems
    apply And.intro
    apply List.Mem.head
    assumption
    apply ih
    intro x ⟨_, _⟩
    apply no_common_elems
    apply And.intro
    apply List.Mem.tail
    assumption
    assumption

def Fintype.of_equiv [f: Fintype α] (eq: Ty.EmbedIso α β) : Fintype β where
  all := f.all.map eq.fwd
  all_nodups := by
    apply List.nodup_map
    exact f.all_nodups
    exact eq.fwd_inj
  all_spec := by
    intro x
    apply List.mem_map.mpr
    exists eq.rev x
    apply And.intro
    apply f.all_spec
    rw [eq.rev_fwd]

def Fintype.card_of_equiv (f: Fintype α) (g: Fintype β) (eq: Ty.EmbedIso α β) : f.card = g.card := by
  rw [card_eq _ (@of_equiv α β f eq)]
  unfold of_equiv card
  erw [List.length_map]

instance [as: Fintype α] (P: α -> Prop) [p: DecidablePred P] : Decidable (∃x: α, P x) :=
  match h:as.all.find? (fun x => match p x with | .isTrue _ => true | .isFalse _ => false) with
  | .some x => Decidable.isTrue <| by
    have ⟨px, _⟩  := List.find?_eq_some_iff_append.mp h
    split at px
    exists x
    contradiction
  | .none => Decidable.isFalse <| by
    intro ⟨x, Px⟩
    have := List.find?_eq_none.mp h x (as.all_spec _)
    split at this <;> contradiction

instance [as: Fintype α] (P: α -> Prop) [p: DecidablePred P] : Decidable (∀x: α, P x) :=
  decidable_of_iff (¬∃x: α, ¬P x) Decidable.not_exists_not
