import Algebra.Zf.Basic
import Algebra.Nat.Mul
import Algebra.ClassicLogic
import Algebra.WellFounded

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

def Zf.IsTransitive.succ (transx: Zf.IsTransitive x) : Zf.IsTransitive x.succ where
  mem_is_sub := by
    intro a a_in_xsucc b b_in_a
    apply Zf.mem_succ.mpr
    cases Zf.mem_succ.mp a_in_xsucc <;> rename_i h
    subst x
    exact Or.inr b_in_a
    exact Or.inr (transx.mem_is_sub _ h _ b_in_a)

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

def Zf.IsTransitive.inter
  (transx: Zf.IsTransitive x)
  (transy: Zf.IsTransitive y) : Zf.IsTransitive (x ∩ y) where
  mem_is_sub := by
    intro a mem b b_in_a
    apply mem_inter.mpr
    have ⟨l,r⟩ := mem_inter.mp mem
    apply And.intro
    exact transx.mem_is_sub _ l _ b_in_a
    exact transy.mem_is_sub _ r _ b_in_a

def Zf.IsTransitive.union
  (transx: Zf.IsTransitive x)
  (transy: Zf.IsTransitive y) : Zf.IsTransitive (x ∪ y) where
  mem_is_sub := by
    intro a mem b b_in_a
    apply mem_union.mpr
    cases mem_union.mp mem <;> rename_i mem
    exact Or.inl <| transx.mem_is_sub _ mem _ b_in_a
    exact Or.inr <| transy.mem_is_sub _ mem _ b_in_a

def Zf.IsOrdinal.inter
  (ordx: Zf.IsOrdinal x)
  (ordy: Zf.IsOrdinal y) : Zf.IsOrdinal (x ∩ y) where
  mem_is_sub := by
    apply Zf.IsTransitive.mem_is_sub
    apply Zf.IsTransitive.inter
    exact ordx.toIsTransitive
    exact ordy.toIsTransitive
  mem_is_tri := by
    intro a b a_in_xy b_in_xy
    have ⟨a_in_x,_⟩ := mem_inter.mp a_in_xy
    have ⟨b_in_x,_⟩ := mem_inter.mp b_in_xy
    apply ordx.mem_is_tri <;> assumption

def Zf.mem_inductionOn (X: Zf)
  (motive: Zf -> Prop) :
  (mem: ∀x ∈ X, (∀y ∈ X, y ∈ x -> motive y) -> (motive x)) ->
  ∀x ∈ X, motive x := by
  intro mem x x_in_X
  induction x using mem_wf.induction with
  | h x ih =>
  apply mem
  assumption
  intro y y_in_X y_in_x
  apply ih
  assumption
  assumption

def Zf.exists_min_element (Y: Zf):
  Nonempty Y ->
  ∃x ∈ Y, ∀y ∈ Y, y ∉ x :=by
  intro nonempty_Y
  apply ClassicLogic.byContradiction
  intro h
  have := Zf.mem_inductionOn Y (fun x => x ∉ Y) (by
    intro x _ ih x_in_Y
    dsimp at ih
    have := not_and.mp <| not_exists.mp h x
    have ⟨ w, h ⟩ := ClassicLogic.not_forall.mp (this x_in_Y)
    have ⟨ w_in_Y, w_in_x ⟩ := not_imp.mp h
    have := ClassicLogic.not_not.mp w_in_x
    have := ih w w_in_Y this
    contradiction)
  clear h
  dsimp at this
  have ⟨y₀,y₀_in_Y⟩ := nonempty_Y
  have := this y₀ y₀_in_Y
  contradiction

def Zf.IsOrdinal.mem_or_eq_of_sub
  (ordx: Zf.IsOrdinal x)
  (ordy: Zf.IsOrdinal y) :
  x ⊆ y -> x ∈ y ∨ x = y := by
  intro x_sub_y
  apply ClassicLogic.byCases (x = y)
  exact .inr
  intro x_ne_y
  apply Or.inl
  have : y \ x ≠ ∅ := by
    intro h
    have := sdiff_eq_empty_iff_sub.mp h
    have := Zf.ext_sub _ _ x_sub_y this
    contradiction
  have ⟨s,s_in_sdiff,s_is_min⟩ := Zf.exists_min_element (y \ x) (by
    apply ClassicLogic.byContradiction
    intro h
    have := Zf.ext_empty _ (not_exists.mp h)
    contradiction)
  replace s_is_min := fun z => s_is_min z
  have ⟨s_in_y,s_not_in_x⟩ := mem_sdiff.mp s_in_sdiff
  have s_sub_x : s ⊆ x := by
    intro k k_in_s
    apply ClassicLogic.byContradiction
    intro k_not_in_x
    have k_in_y := ordy.mem_is_sub s s_in_y k k_in_s
    have := s_is_min _ (mem_sdiff.mpr ⟨k_in_y,k_not_in_x⟩)
    contradiction
  have x_sub_s : x ⊆ s := by
    intro k k_in_x
    apply ClassicLogic.byContradiction
    intro k_not_in_s
    cases ordy.mem_is_tri s k s_in_y (x_sub_y _ k_in_x) <;> rename_i h
    have := ordx.mem_is_sub k k_in_x _ h
    contradiction
    cases h
    subst k
    contradiction
    contradiction
  have x_eq_s := ext_sub _ _ x_sub_s s_sub_x
  subst x
  assumption

def Zf.IsOrdinal.mem_total
  (ordx: Zf.IsOrdinal x)
  (ordy: Zf.IsOrdinal y) : x ∈ y ∨ x = y ∨ y ∈ x := by
  have inter_sub_x := inter_sub_left x y
  have inter_sub_y := inter_sub_right x y
  cases mem_or_eq_of_sub (ordx.inter ordy) ordx inter_sub_x <;> rename_i hx
  <;> cases mem_or_eq_of_sub (ordx.inter ordy) ordy inter_sub_y <;> rename_i hy
  have := mem_wf.irrefl (mem_inter.mpr ⟨hx,hy⟩)
  contradiction
  rw [hy] at hx
  exact .inr (.inr hx)
  rw [hx] at hy
  exact .inl hy
  rw [hx] at hy
  exact .inr (.inl hy)

def Zf.IsOrdinal.mem (ordx: Zf.IsOrdinal x): y ∈ x -> Zf.IsOrdinal y := by
  intro y_in_x
  apply Zf.IsOrdinal.mk _
  intros a b a_in_y b_in_y
  apply ordx.mem_is_tri
  apply ordx.mem_is_sub <;> assumption
  apply ordx.mem_is_sub <;> assumption
  apply Zf.IsTransitive.mk
  intro a a_in_y b b_in_a
  have := ordx.mem_is_sub
  have a_in_x := this y y_in_x a a_in_y
  have b_in_x := this a a_in_x b b_in_a
  cases ordx.mem_is_tri b y b_in_x y_in_x
  assumption
  rename_i h
  cases h
  subst b
  have := mem_wf.transGen.irrefl (.tail (.single a_in_y) b_in_a)
  contradiction
  rename_i y_in_b
  have := mem_wf.transGen.irrefl (.tail (.tail (.single y_in_b) b_in_a) a_in_y)
  contradiction

def Zf.IsOrdinal.union (ordx: Zf.IsOrdinal x) (ordy: Zf.IsOrdinal y) : Zf.IsOrdinal (x ∪ y) where
  mem_is_sub := Zf.IsTransitive.mem_is_sub (ordx.toIsTransitive.union ordy.toIsTransitive)
  mem_is_tri := by
    intro a b a_in_union b_in_union
    cases mem_union.mp a_in_union <;> rename_i ha <;>
    cases mem_union.mp b_in_union <;> rename_i hb
    all_goals apply Zf.IsOrdinal.mem_total
    all_goals try (apply Zf.IsOrdinal.mem ordx; assumption; done)
    all_goals (apply Zf.IsOrdinal.mem ordy; assumption; done)

def Zf.IsOrdinal.sUnion (ordx: ∀x₀ ∈ x, Zf.IsOrdinal x₀) : Zf.IsOrdinal (⋃₀ x) where
  mem_is_sub := by
    intro a a_in_sunionx b b_in_a
    have ⟨c,c_in_x,a_in_c⟩ := mem_sUnion.mp a_in_sunionx
    have ordc := ordx c c_in_x
    apply mem_sUnion.mpr
    exists c
    apply And.intro c_in_x
    apply ordc.mem_is_sub <;> assumption
  mem_is_tri := by
    intro a b a_in_sunion b_in_sunion
    have ⟨c,c_in_x,a_in_c⟩ := mem_sUnion.mp a_in_sunion
    have ⟨d,d_in_x,b_in_d⟩ := mem_sUnion.mp b_in_sunion
    have ordc := ordx c c_in_x
    have ordd := ordx d d_in_x
    have orda := ordc.mem a_in_c
    have ordb := ordd.mem b_in_d
    apply Zf.IsOrdinal.mem_total <;> assumption

def Zf.IsOrdinal.sInter (ordx: ∀x₀ ∈ x, Zf.IsOrdinal x₀) (h: x.Nonempty) : Zf.IsOrdinal (⋂₀ x) where
  mem_is_sub := by
    intro a a_in_sunionx b b_in_a
    have mem := (mem_sInter h).mp a_in_sunionx
    apply (mem_sInter h).mpr
    intro a₀ a₀_in_x
    have := mem a₀ a₀_in_x
    apply (ordx a₀ a₀_in_x).mem_is_sub <;> assumption
  mem_is_tri := by
    intro a b a_in_sinter b_in_sinter
    have mema := (mem_sInter h).mp a_in_sinter
    have memb := (mem_sInter h).mp b_in_sinter
    have ⟨x₀,x₀_in_x⟩ := h
    have ordx₀ := ordx x₀ x₀_in_x
    have orda := ordx₀.mem (mema x₀ x₀_in_x)
    have ordb := ordx₀.mem (memb x₀ x₀_in_x)
    apply Zf.IsOrdinal.mem_total <;> assumption
