import Algebra.Fintype.Multiset

structure Finset (α: Type _) where
  set: Multiset α
  set_nodup: set.Nodup

def Finset.ofList (as: list α) (h: as.nodup) :=
  Finset.mk (.mk as) ((Multiset.mk_nodup as).mpr h)

@[simp]
instance : Membership α (Finset α) := ⟨fun a s => a ∈ s.set⟩

def Finset.ext.proof1 (as bs: list α) :
  as.nodup -> bs.nodup -> (∀x, x ∈ as ↔ x ∈ bs) ->
  ∀x n, as.min_count x n -> bs.min_count x n := by
  intro asnodup bsnodup h x n min_count
  induction min_count generalizing bs with
    | nil =>
      cases bs with
      | nil => apply list.min_count.nil
      | cons b bs => nomatch (h b).mpr (.head _)
    | cons _ ih =>
      rename_i as n a _
      have ⟨bs',perm⟩ := list.cons_perm_of_mem _ _ ((h a).mp (.head _))
      have bs'nodup := perm.nodup bsnodup
      apply perm.symm.min_count
      apply list.min_count.cons
      apply ih bs' asnodup.tail bs'nodup.tail
      intro x
      apply Iff.intro
      · intro mem
        cases (perm.mem _).mp ((h _).mp (.tail _ _ mem))
        have := asnodup.head _ mem
        contradiction
        assumption
      · intro mem
        cases (h _).mpr ((perm.mem _).mpr (list.mem.tail _ _ mem))
        have := bs'nodup.head _ mem
        contradiction
        assumption
    | head _ ih =>
      rename_i as n _
      have ⟨bs',perm⟩ := list.cons_perm_of_mem _ _ ((h x).mp (.head _))
      have bs'nodup := perm.nodup bsnodup
      apply perm.symm.min_count
      apply list.min_count.head
      apply ih bs' asnodup.tail bs'nodup.tail
      intro y
      apply Iff.intro
      · intro mem
        cases (perm.mem _).mp ((h _).mp (.tail _ _ mem))
        have := asnodup.head _ mem
        contradiction
        assumption
      · intro mem
        cases (h _).mpr ((perm.mem _).mpr (list.mem.tail _ _ mem))
        have := bs'nodup.head _ mem
        contradiction
        assumption

@[ext]
def Finset.ext (as bs:Finset α) : (∀x, x ∈ as ↔ x ∈ bs) -> as = bs := by
  intro h
  cases as with | mk as asnodup =>
  cases bs with | mk bs bsnodup =>
  congr
  dsimp at h
  induction as using Multiset.ind with | mk as =>
  induction bs using Multiset.ind with | mk bs =>
  replace asnodup := (Multiset.mk_nodup _).mp asnodup
  replace bsnodup := (Multiset.mk_nodup _).mp bsnodup
  replace h : ∀x, x ∈ as ↔ x ∈ bs := by
    intro x
    apply Iff.trans
    symm
    apply Multiset.mk_mem
    apply flip Iff.trans
    apply Multiset.mk_mem
    apply h
  apply Multiset.sound
  apply list.perm_iff_forall_min_count.mpr
  intro x n
  apply Iff.intro
  · apply ext.proof1
    assumption
    assumption
    assumption
  · apply ext.proof1
    assumption
    assumption
    intro x
    symm
    apply h

instance (priority := 100) [DecidableEq α] (as: Finset α) : Decidable (x ∈ as) := by
  dsimp
  exact inferInstance

instance [DecidableEq α] (as: list α) (h: as.nodup) : Decidable (x ∈ Finset.ofList as h) := by
  dsimp
  unfold Finset.ofList
  dsimp
  exact inferInstance

def Finset.ofList_mem (x: α) (as: list α) (h: as.nodup) :
  x ∈ ofList as h ↔ x ∈ as := Multiset.mk_mem as x

def Finset.card (as: Finset α) : nat := as.set.length

def Finset.ofList_card (as: list α) (h: as.nodup) : (ofList as h).card = as.length := Multiset.mk_length _
