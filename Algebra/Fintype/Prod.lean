import Algebra.Fintype.Basic

instance (α: Sort _) (β: α -> Sort _) [as: Fintype α] [bs: ∀x, Fintype (β x)] : Fintype ((x: α) × β x) where
  all := as.all.flatMap <| fun x => (bs x).all.map <| fun b => ⟨x, b⟩
  all_nodups := by
    cases as with | mk as as_nodup spec =>
    dsimp
    clear spec
    induction as_nodup with
    | nil => apply List.Pairwise.nil
    | cons a_notin_as _ ih =>
      rename_i a as _
      replace a_notin_as : a ∉ as := by
        intro h
        apply a_notin_as
        assumption
        rfl
      rw [List.flatMap_cons]
      apply List.nodup_append
      · apply List.nodup_map
        exact (bs _).all_nodups
        intro x y f
        cases f
        rfl
      apply ih
      · intro ⟨a₀, b₀⟩ ⟨mem, mem'⟩
        replace ⟨a', a'_in_as, mem'⟩ := List.mem_flatMap.mp mem'
        replace ⟨b', b'_in_bs, mem'⟩ := List.mem_map.mp mem'
        cases mem'
        replace ⟨a', a'_in_bs, mem⟩ := List.mem_map.mp mem
        cases mem
        contradiction
  all_spec := by
    intro ⟨a, b⟩
    apply List.mem_flatMap.mpr
    exists a
    apply And.intro
    apply as.all_spec
    apply List.mem_map.mpr
    exists b
    apply And.intro
    apply (bs _).all_spec
    rfl

instance Prod.EquivSigma α β : Ty.EmbedIso (Prod α β) (Sigma (fun (_: α) => β)) where
  fwd a := ⟨a.fst, a.snd⟩
  rev a := ⟨a.fst, a.snd⟩
  fwd_rev _ := rfl
  rev_fwd _ := rfl

instance (α: Sort _) (β: Sort _) [Fintype α] [Fintype β] : Fintype (α × β) :=
  Fintype.of_equiv (Prod.EquivSigma α β).symm
