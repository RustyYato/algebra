import Algebra.Zf.Basic
import Algebra.Nat.Mul

-- a transitive set is one where every member is a subset
structure Zf.IsTransitive (a: Zf) : Prop where
  mem_is_sub: ∀x ∈ a, x ⊆ a

structure Zf.IsOrdinal (a: Zf) extends IsTransitive a: Prop where
  mem_is_tri: ∀x y, x ∈ a -> y ∈ a -> x ∈ y ∨ x = y ∨ y ∈ x

def Zf.Pre.succ (a: Zf.Pre) := Insert.insert a a
def Zf.succ (a: Zf) := Insert.insert a a

def Zf.mem_succ {a: Zf} : ∀{x}, x ∈ a.succ ↔ x = a ∨ x ∈ a := Zf.mem_insert

def Zf.mk_succ (a: Zf.Pre) : (mk a).succ = mk a.succ := by
  cases a with | intro a amem =>
  apply ext
  intro x
  induction x using ind with | mk x =>
  cases x with | intro x xmem =>
  apply Iff.intro
  · intro h
    cases mem_union.mp h <;> rename_i h
    rw [mem_singleton.mp h]
    apply mk_mem.mpr
    apply Pre.mem_iff.mpr
    exists Sum.inl ⟨⟩
    have ⟨a₀,prf⟩ := mk_mem.mp h
    apply mk_mem.mpr
    exists .inr a₀
  · intro h
    apply mem_union.mpr
    have ⟨a₀,prf⟩ := mk_mem.mp h
    cases a₀
    dsimp at prf
    apply Or.inl
    apply mem_singleton.mpr
    apply sound
    assumption
    apply Or.inr
    apply mk_mem.mpr
    exists (by assumption)

def Zf.Pre.of_nat : nat -> Zf.Pre
| .zero => ∅
| .succ n => (Zf.Pre.of_nat n).succ

def Zf.of_nat : nat -> Zf
| .zero => ∅
| .succ n => (Zf.of_nat n).succ

def Zf.ofNat : Nat -> Zf
| .zero => ∅
| .succ n => (Zf.ofNat n).succ

instance : OfNat Zf n := ⟨Zf.ofNat n⟩

def Zf.of_nat_eq_ofNat : Zf.of_nat n = Zf.ofNat n.toNat := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold of_nat nat.toNat ofNat
    erw [ih]
def Zf.ofNat_eq_of_nat : Zf.ofNat n = Zf.of_nat (nat.ofNat n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold of_nat nat.ofNat ofNat
    erw [ih]
def Zf.mk_of_nat (n: nat) : .of_nat n = mk (.of_nat n) := by
  induction n with
  | zero =>
    symm
    apply ext_empty
    intro x h
    induction x using ind with | mk x =>
    have := mk_mem.mp h
    have ⟨⟨_⟩,_⟩ := (mk_mem.mp h)
    contradiction
  | succ n ih =>
    unfold of_nat
    rw [ih, mk_succ]
    rfl


def Zf.mem_ofNat {n:Nat} : ∀{x}, x ∈ Zf.ofNat n ↔ ∃m < n, x = Zf.ofNat m := by
  intro x
  induction n with
  | zero =>
    apply Iff.intro
    intro h
    have := not_mem_empty _ h
    contradiction
    intro ⟨_,_,_⟩
    contradiction
  | succ n ih =>
    apply Iff.intro
    intro h
    cases mem_succ.mp h
    subst x
    exists n
    apply And.intro _ rfl
    apply Nat.lt_succ_self
    have ⟨m,m_lt_n,prf⟩ := ih.mp (by assumption)
    exists m
    apply And.intro _ prf
    apply Nat.lt_trans m_lt_n
    apply Nat.lt_succ_self
    intro ⟨m,m_lt_n,x_eq_m⟩
    subst x
    apply mem_succ.mpr
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ m_lt_n)
    apply Or.inr; apply ih.mpr; exists m
    subst n
    apply Or.inl; rfl

def Zf.mem_of_nat {n:nat} : ∀{x}, x ∈ Zf.of_nat n ↔ ∃m < n, x = Zf.of_nat m := by
  intro x
  rw [Zf.of_nat_eq_ofNat]
  apply Iff.intro
  intro h
  have ⟨m,m_lt_n,x_eq⟩ := mem_ofNat.mp h
  exists nat.ofNat m
  apply And.intro
  apply lt_of_lt_of_le
  apply nat.ofNat_lt
  assumption
  rw [nat.toNat_ofNat]
  subst x
  rw [ofNat_eq_of_nat]
  intro ⟨m,m_lt_n,x_eq_of_nat⟩
  rw [x_eq_of_nat]
  apply mem_ofNat.mpr
  exists nat.toNat m
  apply And.intro
  apply nat.toNat_lt
  assumption
  rw [of_nat_eq_ofNat]

def Zf.Pre.omega : Zf.Pre := .intro nat Zf.Pre.of_nat
def Zf.omega : Zf := mk .omega

notation "ω₀" => Zf.omega

def Zf.mem_ω₀ : ∀{x}, x ∈ ω₀ ↔ ∃m, x = Zf.of_nat m := by
  intro x
  induction x using ind with | mk x =>
  rw [omega]
  apply Iff.trans
  apply mk_mem
  apply Iff.intro
  intro ⟨n,mem⟩
  exists n
  rw [sound mem]
  rw [Zf.mk_of_nat]
  intro ⟨w,h⟩
  exists w
  rw [mk_of_nat] at h
  exact exact h

def Zf.IsOrdinal.zero : Zf.IsOrdinal 0 where
  mem_is_sub := fun _ mem => (not_mem_empty _ mem).elim
  mem_is_tri := fun _ _ mem => (not_mem_empty _ mem).elim

def Zf.IsTransitive.succ (ordx: Zf.IsTransitive x) : Zf.IsTransitive x.succ where
  mem_is_sub := by
    intro a a_in_xsucc b b_in_a
    apply Zf.mem_succ.mpr
    cases Zf.mem_succ.mp a_in_xsucc <;> rename_i h
    subst x
    exact Or.inr b_in_a
    exact Or.inr (ordx.mem_is_sub _ h _ b_in_a)

def Zf.IsOrdinal.succ (ordx: Zf.IsOrdinal x) : Zf.IsOrdinal x.succ where
  mem_is_sub := ordx.toIsTransitive.succ.mem_is_sub
  mem_is_tri := by
    intro a b a_in_xsucc b_in_xsucc
    cases mem_succ.mp a_in_xsucc <;> cases mem_succ.mp b_in_xsucc
    subst x; subst b
    apply Or.inr (Or.inl rfl)
    subst x
    apply Or.inr (Or.inr _)
    assumption
    subst x
    apply Or.inl; assumption
    apply ordx.mem_is_tri
    assumption
    assumption
