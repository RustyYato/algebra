inductive Regex (α: Type _) where
| empty
| value (value: α)
| alt (a b: Regex α)
| concat (a b: Regex α)
| star (a: Regex α)

inductive Regex.Matches : Regex α -> List α -> Prop where
| empty : Matches .empty []
| value (a: α) : Matches (.value a) [a]
| alt_left l r text : Matches l text -> Matches (.alt l r) text
| alt_right l r text : Matches r text -> Matches (.alt l r) text
| concat l r text_left text_right :
  Matches l text_left -> Matches r text_right -> Matches (.concat l r) (text_left ++ text_right)
| star_nil a : Matches (.star a) []
| star_cons a text next_text : Matches a text -> Matches (.star a) next_text -> Matches (.star a) (text ++ next_text)

structure NfaState (α: Type _) where
  -- the transition table from to the next state
  -- none means epsilon transition
  trans: Option α -> List Nat
  is_accepting: Bool

structure Nfa (α: Type _) where
  states: List (NfaState α)

structure DfaState (α: Type _) where
  trans: α -> Nat
  is_accepting: Bool

structure Dfa (α: Type _) where
  states: List (DfaState α)

inductive Nfa.MatchesAt (nfa: Nfa α) : Nat -> List α -> Prop where
| nil (state: Nat) (state_in_bounds: state < nfa.states.length) :
  nfa.states[state].is_accepting -> MatchesAt nfa state []
| cons (state next_state: Nat) (state_in_bounds: state < nfa.states.length) :
  next_state ∈ (nfa.states[state].trans (.some a)) ->
  MatchesAt nfa next_state as ->
  MatchesAt nfa state (a::as)
| eps (state next_state: Nat) (state_in_bounds: state < nfa.states.length) :
  next_state ∈ (nfa.states[state].trans .none) ->
  MatchesAt nfa next_state as ->
  MatchesAt nfa state as

def Nfa.MatchesPrefixAt (nfa: Nfa α) (n: Nat) (xs: List α): Prop := ∃xs': List α, Nfa.MatchesAt nfa n xs' ∧ xs' <+: xs

inductive Dfa.MatchesAt (dfa: Dfa α) : Nat -> List α -> Prop where
| nil (state: Nat) (state_in_bounds: state < dfa.states.length) :
  dfa.states[state].is_accepting -> MatchesAt dfa state []
| cons (state: Nat) (state_in_bounds: state < dfa.states.length) :
  MatchesAt dfa (dfa.states[state].trans a) as ->
  MatchesAt dfa state (a::as)

def Nfa.MatchesAt.state_in_bounds : Nfa.MatchesAt nfa state as -> state < nfa.states.length := by
  intro h
  cases h <;> assumption

def Dfa.MatchesAt.state_in_bounds : Dfa.MatchesAt dfa state as -> state < dfa.states.length := by
  intro h
  cases h <;> assumption

variable [DecidableEq α]

def NfaState.shift (a: NfaState α) (n: Nat) : NfaState α where
  trans x := (a.trans x).map (· + n)
  is_accepting := a.is_accepting
def NfaState.unshift (a: NfaState α) (n: Nat) : NfaState α where
  trans x := (a.trans x).map (· - n)
  is_accepting := a.is_accepting
def Nfa.append (a b: Nfa α) : Nfa α where
  states := a.states ++ (b.states.map (·.shift a.states.length))
def Nfa.empty α : Nfa α where
  states := [
    { trans := fun _ => [], is_accepting := true }
  ]
def Nfa.value (value: α) : Nfa α where
  states := [
    { trans := fun x => if x = value then [1] else [], is_accepting := false },
    { trans := fun _ => [], is_accepting := true }
  ]
def Nfa.alt (a b: Nfa α) : Nfa α :=
  let pre: Nfa α := {
    states := [
      {
        is_accepting := false
        trans := fun x => if x.isNone then [1, 1 + a.states.length] else []
      }
    ]
  }
  pre.append (a.append b)
def Nfa.concat (a b: Nfa α) : Nfa α :=
  let a': Nfa α := {
    states := a.states.map (fun state => { is_accepting := false, trans := fun h => state.trans h ++ if state.is_accepting && h.isNone then [a.states.length] else [] })
  }
  a'.append b

def List.update (f: α -> α) : Nat -> List α -> List α
| _, [] => []
| 0, x::xs => (f x)::xs
| n + 1,x::xs => x::xs.update f n

def List.length_update (f: α -> α) (n: Nat) (as: List α) : (as.update f n).length = as.length := by
  induction n generalizing as with
  | zero => cases as <;> rfl
  | succ n ih =>
    cases as
    rfl
    unfold update List.length
    rw [ih]

macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic| rw [List.length_update]; get_elem_tactic_trivial)

def List.getElem_update (f: α -> α) (n x: Nat) (as: List α) (h: x < as.length) : (as.update f n)[x] = if n = x then f as[x] else as[x] := by
  induction n generalizing as x with
  | zero =>
    cases as
    contradiction
    cases x <;> rfl
  | succ n ih =>
    cases as
    contradiction
    cases x
    rw [if_neg]
    rfl
    exact Nat.noConfusion
    rename_i x
    rename_i a as
    have := ih x as (Nat.lt_of_succ_lt_succ h)
    unfold update
    rw [List.getElem_cons_succ, this]
    split
    rw [if_pos]
    rfl
    subst x
    rfl
    rw [if_neg]
    rfl
    intro h
    have := Nat.succ.inj h
    contradiction

def Nfa.star (a: Nfa α) : Nfa α where
  states :=
  let states' := a.states.map (fun state => { is_accepting := state.is_accepting, trans := fun h => state.trans h ++ if state.is_accepting && h.isNone then [0] else [] })
  states'.update (fun state => {
    trans := state.trans
    is_accepting := true
  }) 0

def Nfa.ofRegex : Regex α -> Nfa α
| .empty => .empty α
| .value a => .value a
| .star a => .star (Nfa.ofRegex a)
| .alt a b => .alt (Nfa.ofRegex a) (Nfa.ofRegex b)
| .concat a b => .concat (Nfa.ofRegex a) (Nfa.ofRegex b)

def Nfa.length_append (a b: Nfa α): (a.append b).states.length = a.states.length + b.states.length := by
  unfold append
  rw [List.length_append, List.length_map]

def Nfa.length_alt (a b: Nfa α): (a.alt b).states.length = 1 + a.states.length + b.states.length := by
  unfold alt
  rw [length_append, length_append, Nat.add_assoc]
  rfl

def Nfa.length_concat (a b: Nfa α): (a.concat b).states.length = a.states.length + b.states.length := by
  unfold concat
  rw [length_append, List.length_map]

def Nfa.length_star (a: Nfa α): a.star.states.length = a.states.length := by
  unfold star
  rw [List.length_update, List.length_map]

-- every index in the transition table points to some other state
def Nfa.WellFormed (a: Nfa α) : Prop :=
  0 < a.states.length ∧
  ∀state ∈ a.states, ∀x next_state, next_state ∈ state.trans x -> next_state < a.states.length

def Nfa.WellFormed.empty α: WellFormed (empty α) := by
  apply And.intro
  apply Nat.zero_lt_succ
  intro state state_mem x next_state next_state_mem
  cases state_mem
  any_goals contradiction

def Nfa.WellFormed.value (a: α): WellFormed (value a) := by
  apply And.intro
  apply Nat.zero_lt_succ
  intro state state_mem x next_state next_state_mem
  cases state_mem
  dsimp at next_state_mem
  split at next_state_mem
  any_goals contradiction
  cases next_state_mem
  show 1 < 2
  trivial
  contradiction
  rename_i h
  cases h <;> contradiction

def Nfa.WellFormed.append {a b: Nfa α} : a.WellFormed -> b.WellFormed -> (a.append b).WellFormed := by
  intro awf bwf
  apply And.intro
  apply Nat.lt_of_lt_of_le
  apply awf.left
  erw [List.length_append]
  apply Nat.le_add_right
  intro state state_mem x next_state next_state_mem
  unfold append
  rw [List.length_append, List.length_map]
  rcases List.mem_append.mp state_mem with state_in_a | state_in_b
  apply Nat.lt_of_lt_of_le
  exact awf.right state state_in_a x next_state next_state_mem
  apply Nat.le_add_right
  replace ⟨nfa_state,nfa_state_in_b,state_in_b⟩  := List.mem_map.mp state_in_b
  subst state
  replace ⟨next_state,next_state_mem,next_state_def⟩  := List.mem_map.mp next_state_mem
  subst next_state_def
  rw [Nat.add_comm]
  apply Nat.add_lt_add_of_le_of_lt
  apply Nat.le_refl
  apply bwf.right nfa_state
  assumption
  assumption

def Nfa.WellFormed.alt {a b: Nfa α}: WellFormed a -> WellFormed b -> WellFormed (alt a b) := by
  intro awf bwf
  apply And.intro
  apply Nat.zero_lt_succ
  intro state state_mem x next_state next_state_mem
  rw [length_alt]
  replace state_mem := List.mem_append.mp state_mem
  cases state_mem
  rename_i h
  cases h
  dsimp at *
  cases x
  dsimp at next_state_mem
  cases next_state_mem
  rw [Nat.add_assoc, Nat.one_add]
  apply Nat.succ_lt_succ
  apply Nat.lt_of_lt_of_le
  exact awf.left
  apply Nat.le_add_right
  rename_i h
  cases h
  conv => { lhs; rw [←Nat.add_zero (1 + _)] }
  apply Nat.add_lt_add_of_le_of_lt
  apply Nat.le_refl
  exact bwf.left
  any_goals contradiction
  rename_i state_mem
  replace ⟨next_nfa_state,next_nfa_state_mem,state_mem⟩  := List.mem_map.mp state_mem
  subst state_mem
  dsimp at next_state_mem
  replace ⟨next_state,next_state_mem,state_mem⟩  := List.mem_map.mp next_state_mem
  subst state_mem
  have := (awf.append bwf).right next_nfa_state next_nfa_state_mem x
    next_state next_state_mem
  rw [Nat.add_comm, Nat.add_assoc]
  apply Nat.add_lt_add_of_le_of_lt
  apply Nat.le_refl
  rw [length_append] at this
  exact this

def Nfa.WellFormed.concat {a b: Nfa α}: WellFormed a -> WellFormed b -> WellFormed (concat a b) := by
  intro awf bwf
  apply And.intro
  apply Nat.lt_of_lt_of_le
  exact awf.left
  unfold concat Nfa.append
  dsimp
  rw [List.length_append, List.length_map]
  apply Nat.le_add_right
  intro state state_mem x next_state next_state_mem
  rw [length_concat]
  replace state_mem := List.mem_append.mp state_mem
  cases state_mem
  rename_i h
  replace ⟨next_nfa_state, next_nfa_state_mem, mem⟩ := List.mem_map.mp h
  clear h
  subst mem
  replace next_state_mem := List.mem_append.mp next_state_mem
  rcases next_state_mem with mema | memconcat
  apply Nat.lt_of_lt_of_le
  exact awf.right next_nfa_state next_nfa_state_mem x next_state mema
  apply Nat.le_add_right
  split at memconcat
  cases memconcat
  conv => { lhs; rw [←Nat.add_zero a.states.length] }
  apply Nat.add_lt_add_of_le_of_lt
  apply Nat.le_refl
  exact bwf.left
  contradiction
  contradiction
  rename_i h
  replace ⟨next_nfa_state,next_nfa_state_mem,h⟩ := List.mem_map.mp h
  subst h
  replace ⟨next_state,next_state_mem,h⟩ := List.mem_map.mp next_state_mem
  subst h
  rw [List.length_map]
  rw [Nat.add_comm]
  apply Nat.add_lt_add_of_le_of_lt
  apply Nat.le_refl
  apply bwf.right
  assumption
  assumption

def Nfa.WellFormed.star {a: Nfa α}: WellFormed a -> WellFormed (star a) := by
  intro awf
  apply And.intro
  apply Nat.lt_of_lt_of_le
  exact awf.left
  rw [length_star]
  apply Nat.le_refl
  intro state state_mem x next_state next_state_mem
  rw [length_star]
  unfold star at state_mem
  dsimp at state_mem
  cases a with | mk states =>
  cases states with
  | nil => contradiction
  | cons a as =>
  unfold List.update at state_mem
  dsimp at *
  cases state_mem <;> rename_i state_mem
  replace next_state_mem := List.mem_append.mp next_state_mem
  · cases next_state_mem <;> rename_i h
    apply awf.right
    apply List.Mem.head
    assumption
    split at h
    cases h
    apply Nat.zero_lt_succ
    repeat contradiction
  replace ⟨next_nfa_state,next_nfa_state_mem,state_mem⟩ := List.mem_map.mp state_mem
  rw [←state_mem] at next_state_mem
  dsimp at next_state_mem
  replace next_state_mem := List.mem_append.mp next_state_mem
  cases next_state_mem <;> rename_i next_state_mem
  apply awf.right
  apply List.Mem.tail
  assumption
  assumption
  split at next_state_mem
  cases next_state_mem
  apply Nat.zero_lt_succ
  repeat contradiction

def Nfa.WellFormed.ofRegex (r: Regex α) : WellFormed (ofRegex r) := by
  induction r with
  | empty => exact WellFormed.empty _
  | value a => exact WellFormed.value _
  | alt a b aih bih => exact aih.alt bih
  | concat a b aih bih => exact aih.concat bih
  | star a aih => exact aih.star

def Nfa.MatchesAt.append_left (a b: Nfa α) (n: Nat) : a.WellFormed -> n < a.states.length -> ∀text, Nfa.MatchesAt (a.append b) n text ↔ Nfa.MatchesAt a n text := by
  intro awf n_lt_a text
  apply Iff.intro
  · intro h
    induction h with
    | nil state state_in_bounds h =>
      have getElem_spec : (append a b).states[state] = a.states[state] := @List.getElem_append_left _ _ a.states (List.map
        (fun state =>
          { trans := fun x => List.map (fun x => x + a.states.length) (state.trans x),
            is_accepting := state.is_accepting })
        b.states) n_lt_a (by
          rw [List.length_append, List.length_map]
          rw [length_append] at state_in_bounds
          assumption)

      apply MatchesAt.nil
      any_goals assumption
      rw [←getElem_spec]
      exact h
    | cons state next_state state_in_bounds next_state_def mathces ih =>
      have getElem_spec : (append a b).states[state] = a.states[state] := @List.getElem_append_left _ _ a.states (List.map
        (fun state =>
          { trans := fun x => List.map (fun x => x + a.states.length) (state.trans x),
            is_accepting := state.is_accepting })
        b.states) n_lt_a (by
          rw [List.length_append, List.length_map]
          rw [length_append] at state_in_bounds
          assumption)
      rename_i x xs
      apply MatchesAt.cons state next_state
      rw[ ←getElem_spec]
      exact next_state_def
      apply ih
      apply awf.right
      exact List.getElem_mem a.states state n_lt_a
      rw [getElem_spec] at next_state_def
      assumption
    | eps state next_state state_in_bounds next_state_def _ ih =>
      have getElem_spec : (append a b).states[state] = a.states[state] := @List.getElem_append_left _ _ a.states (List.map
        (fun state =>
          { trans := fun x => List.map (fun x => x + a.states.length) (state.trans x),
            is_accepting := state.is_accepting })
        b.states) n_lt_a (by
          rw [List.length_append, List.length_map]
          rw [length_append] at state_in_bounds
          assumption)
      rename_i xs _
      apply MatchesAt.eps
      rw [←getElem_spec]
      assumption
      apply ih
      apply awf.right
      exact List.getElem_mem a.states state n_lt_a
      rw [←getElem_spec]
      assumption
  · intro h
    induction h with
    | nil state _ h =>
      have : state < (append a b).states.length := by
        rw [length_append]
        apply Nat.lt_of_lt_of_le n_lt_a
        apply Nat.le_add_right
      have getElem_spec : (append a b).states[state] = a.states[state] := @List.getElem_append_left _ _ a.states (List.map
          (fun state =>
            { trans := fun x => List.map (fun x => x + a.states.length) (state.trans x),
              is_accepting := state.is_accepting })
          b.states) n_lt_a (by
            rw [List.length_append, List.length_map]
            rw [length_append] at *
            assumption)
      apply MatchesAt.nil
      rw [getElem_spec]
      assumption
    | cons state next_state _ next_state_def h ih  =>
      have : state < (append a b).states.length := by
        rw [length_append]
        apply Nat.lt_of_lt_of_le n_lt_a
        apply Nat.le_add_right
      have getElem_spec : (append a b).states[state] = a.states[state] := @List.getElem_append_left _ _ a.states (List.map
          (fun state =>
            { trans := fun x => List.map (fun x => x + a.states.length) (state.trans x),
              is_accepting := state.is_accepting })
          b.states) n_lt_a (by
            rw [List.length_append, List.length_map]
            rw [length_append] at *
            assumption)
      apply MatchesAt.cons
      rw [getElem_spec]
      assumption
      apply ih
      exact h.state_in_bounds
    | eps state next_state _ next_state_def h ih  =>
      have : state < (append a b).states.length := by
        rw [length_append]
        apply Nat.lt_of_lt_of_le n_lt_a
        apply Nat.le_add_right
      have getElem_spec : (append a b).states[state] = a.states[state] := @List.getElem_append_left _ _ a.states (List.map
          (fun state =>
            { trans := fun x => List.map (fun x => x + a.states.length) (state.trans x),
              is_accepting := state.is_accepting })
          b.states) n_lt_a (by
            rw [List.length_append, List.length_map]
            rw [length_append] at *
            assumption)
      apply MatchesAt.eps
      rw [getElem_spec]
      assumption
      apply ih
      exact h.state_in_bounds

def Nfa.MatchesAt.append_right (a b: Nfa α) (n: Nat) : a.states.length ≤ n -> ∀text, Nfa.MatchesAt (a.append b) n text ↔ Nfa.MatchesAt b (n - a.states.length) text := by
  intro a_le_n text
  apply Iff.intro
  · intro h
    induction h with
    | nil state state_in_bounds h =>
      have state_in_b : state - a.states.length < b.states.length := by
        apply Nat.lt_of_add_lt_add_right
        rw [Nat.sub_add_cancel, Nat.add_comm]
        rw [length_append] at state_in_bounds
        assumption
        assumption
      have getElem_spec : (append a b).states[state] = b.states[state - a.states.length].shift a.states.length := by
        unfold append
        dsimp
        apply Eq.trans
        apply List.getElem_append_right
        apply Nat.not_lt_of_le
        assumption
        rw [List.length_map]
        assumption
        rw [List.getElem_map]
      apply MatchesAt.nil _ state_in_b
      rw [getElem_spec] at h
      exact h
    | cons state next_state state_in_bounds next_state_mem h ih =>
      have state_in_b : state - a.states.length < b.states.length := by
        apply Nat.lt_of_add_lt_add_right
        rw [Nat.sub_add_cancel, Nat.add_comm]
        rw [length_append] at state_in_bounds
        assumption
        assumption
      have getElem_spec : (append a b).states[state] = b.states[state - a.states.length].shift a.states.length := by
        unfold append
        dsimp
        apply Eq.trans
        apply List.getElem_append_right
        apply Nat.not_lt_of_le
        assumption
        rw [List.length_map]
        assumption
        rw [List.getElem_map]
      rw [getElem_spec] at next_state_mem
      replace ⟨next_state,next_state_mem,h⟩ := List.mem_map.mp next_state_mem
      subst h
      apply MatchesAt.cons
      show next_state ∈ _
      assumption
      rw [Nat.add_sub_cancel] at ih
      apply ih
      apply Nat.le_add_left
    | eps state next_state state_in_bounds next_state_mem h ih =>
      have state_in_b : state - a.states.length < b.states.length := by
        apply Nat.lt_of_add_lt_add_right
        rw [Nat.sub_add_cancel, Nat.add_comm]
        rw [length_append] at state_in_bounds
        assumption
        assumption
      have getElem_spec : (append a b).states[state] = b.states[state - a.states.length].shift a.states.length := by
        unfold append
        dsimp
        apply Eq.trans
        apply List.getElem_append_right
        apply Nat.not_lt_of_le
        assumption
        rw [List.length_map]
        assumption
        rw [List.getElem_map]
      rw [getElem_spec] at next_state_mem
      replace ⟨next_state,next_state_mem,h⟩ := List.mem_map.mp next_state_mem
      subst h
      apply MatchesAt.eps
      show next_state ∈ _
      assumption
      rw [Nat.add_sub_cancel] at ih
      apply ih
      apply Nat.le_add_left
  · intro h
    have ⟨k,prf⟩  := Nat.exists_eq_add_of_le a_le_n
    subst n
    rw[Nat.add_sub_cancel_left] at h
    clear a_le_n
    induction h with
    | nil state state_in_bounds h =>
      have state_in_b : a.states.length + state  < (append a b).states.length := by
        rw [length_append]
        apply Nat.add_lt_add_of_le_of_lt
        apply Nat.le_refl
        exact state_in_bounds
      have getElem_spec : (append a b).states[a.states.length + state] = b.states[state].shift a.states.length := by
        unfold append
        dsimp
        apply Eq.trans
        apply List.getElem_append_right
        apply Nat.not_lt_of_le
        apply Nat.le_add_right
        rw [List.length_map]
        rw [Nat.add_sub_cancel_left]
        assumption
        rw [List.getElem_map]
        congr
        rw [Nat.add_sub_cancel_left]
      apply MatchesAt.nil
      rw [getElem_spec]
      assumption
    | cons state next_state state_in_bounds state_next_mem _ ih =>
      have state_in_b : a.states.length + state  < (append a b).states.length := by
        rw [length_append]
        apply Nat.add_lt_add_of_le_of_lt
        apply Nat.le_refl
        exact state_in_bounds
      have getElem_spec : (append a b).states[a.states.length + state] = b.states[state].shift a.states.length := by
        unfold append
        dsimp
        apply Eq.trans
        apply List.getElem_append_right
        apply Nat.not_lt_of_le
        apply Nat.le_add_right
        rw [List.length_map]
        rw [Nat.add_sub_cancel_left]
        assumption
        rw [List.getElem_map]
        congr
        rw [Nat.add_sub_cancel_left]
      apply MatchesAt.cons
      rw [getElem_spec]
      show next_state + a.states.length ∈ _
      apply List.mem_map.mpr
      exists next_state
      rw [Nat.add_comm]
      apply ih
    | eps state next_state state_in_bounds state_next_mem _ ih =>
      have state_in_b : a.states.length + state  < (append a b).states.length := by
        rw [length_append]
        apply Nat.add_lt_add_of_le_of_lt
        apply Nat.le_refl
        exact state_in_bounds
      have getElem_spec : (append a b).states[a.states.length + state] = b.states[state].shift a.states.length := by
        unfold append
        dsimp
        apply Eq.trans
        apply List.getElem_append_right
        apply Nat.not_lt_of_le
        apply Nat.le_add_right
        rw [List.length_map]
        rw [Nat.add_sub_cancel_left]
        assumption
        rw [List.getElem_map]
        congr
        rw [Nat.add_sub_cancel_left]
      apply MatchesAt.eps
      rw [getElem_spec]
      show next_state + a.states.length ∈ _
      apply List.mem_map.mpr
      exists next_state
      rw [Nat.add_comm]
      apply ih

def Nfa.MatchesAt.toMatchesPrefix (nfa: Nfa α) : ∀text, nfa.MatchesAt n text -> ∀text', nfa.MatchesPrefixAt n (text ++ text') := by
  intro text m text'
  exists text
  apply And.intro
  assumption
  apply List.prefix_append

def Nfa.ofRegex.spec (a: Regex α) : ∀text, a.Matches text ↔  (ofRegex a).MatchesAt 0 text := by
  intro text
  apply Iff.intro
  intro h
  induction h with
  | empty =>
    apply Nfa.MatchesAt.nil
    rfl
    apply Nat.zero_lt_succ
  | value a =>
    apply Nfa.MatchesAt.cons _ 1
    show 1 ∈ if some a = some a then [1] else []
    rw [if_pos rfl]
    apply List.Mem.head
    apply Nfa.MatchesAt.nil
    rfl
    show 1 < 2
    decide
    show 0 < 2
    decide
  | alt_left l r text h ih =>
    apply Nfa.MatchesAt.eps _ 1
    apply List.Mem.head
    unfold ofRegex alt
    apply (MatchesAt.append_right _ _ _ _ _).mpr
    apply (MatchesAt.append_left _ _ _ _ _ _).mpr
    exact ih
    apply WellFormed.ofRegex
    apply And.left
    apply WellFormed.ofRegex
    apply Nat.le_refl
    apply Nat.zero_lt_succ
  | alt_right l r text h ih =>
    apply Nfa.MatchesAt.eps _ (1 + (ofRegex l).states.length)
    apply List.Mem.tail
    apply List.Mem.head
    apply (MatchesAt.append_right _ _ _ _ _).mpr
    dsimp
    apply (MatchesAt.append_right _ _ _ _ _).mpr
    erw [Nat.sub_sub, Nat.sub_self]
    exact ih
    dsimp
    rw [Nat.add_sub_cancel_left]
    apply Nat.le_refl
    dsimp
    rw [Nat.add_comm]
    apply Nat.succ_le_succ
    apply Nat.zero_le
    apply And.left
    apply WellFormed.ofRegex
  | star_nil a =>
    apply MatchesAt.nil
    unfold ofRegex star
    dsimp
    rw [List.getElem_update, if_pos rfl]
    all_goals
      rw [List.length_map]
    apply And.left
    apply WellFormed.ofRegex
  | star_cons a text next_text h₀ h₁ ih₀ ih₁ =>
    sorry
  | concat a b text next_text h₀ h₁ ih₀ ih₁ => sorry
