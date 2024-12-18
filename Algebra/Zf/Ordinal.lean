import Algebra.Zf.Basic
import Algebra.Nat.Mul
import Algebra.ClassicLogic
import Algebra.WellFounded
import Algebra.AxiomBlame

local notation "⟦" a "⟧" => (QuotLike.mk (a: Zf.Pre): Zf)

-- a transitive set is one where every member is a subset
class Zf.IsTransitive (a: Zf) : Prop where
  mem_is_sub: ∀x ∈ a, x ⊆ a

class Zf.IsOrdinal (a: Zf) extends IsTransitive a: Prop where
  mem_is_tri: ∀x y, x ∈ a -> y ∈ a -> x ∈ y ∨ x = y ∨ y ∈ x

def Zf.Pre.succ (a: Zf.Pre) := Insert.insert a a
def Zf.succ (a: Zf) := Insert.insert a a

def Zf.mem_succ {a: Zf} : ∀{x}, x ∈ a.succ ↔ x = a ∨ x ∈ a := Zf.mem_insert

def Zf.mk_succ (a: Zf.Pre) : ⟦a⟧.succ = ⟦a.succ⟧ := by
  cases a with | intro a amem =>
  apply ext
  intro x
  induction x using quot.ind with | mk x =>
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
    apply quot.sound
    assumption
    apply Or.inr
    apply mk_mem.mpr
    exists (by assumption)

def Zf.succ_eq_insert (a: Zf) : a.succ = insert a a := rfl

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
def Zf.mk_of_nat (n: nat) : Zf.of_nat n = ⟦.of_nat n⟧ := by
  induction n with
  | zero =>
    symm
    apply ext_empty
    intro x h
    induction x using quot.ind with | mk x =>
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
def Zf.omega : Zf := ⟦.omega⟧

notation "ω₀" => Zf.omega

def Zf.mem_ω₀ : ∀{x}, x ∈ ω₀ ↔ ∃m, x = Zf.of_nat m := by
  intro x
  induction x using quot.ind with | mk x =>
  rw [omega]
  apply Iff.trans
  apply mk_mem
  apply Iff.intro
  intro ⟨n,mem⟩
  exists n
  rw [quot.sound mem]
  rw [Zf.mk_of_nat]
  intro ⟨w,h⟩
  exists w
  rw [mk_of_nat] at h
  exact quot.exact h

instance Zf.IsTransitive.zero : Zf.IsTransitive 0 where
  mem_is_sub := fun _ mem => (not_mem_empty _ mem).elim

instance Zf.IsOrdinal.zero : Zf.IsOrdinal 0 where
  mem_is_tri := fun _ _ mem => (not_mem_empty _ mem).elim

instance Zf.IsTransitive.succ (transx: Zf.IsTransitive x) : Zf.IsTransitive x.succ where
  mem_is_sub := by
    intro a a_in_xsucc b b_in_a
    apply Zf.mem_succ.mpr
    cases Zf.mem_succ.mp a_in_xsucc <;> rename_i h
    subst x
    exact Or.inr b_in_a
    exact Or.inr (transx.mem_is_sub _ h _ b_in_a)

instance Zf.IsOrdinal.succ [ordx: Zf.IsOrdinal x] : Zf.IsOrdinal x.succ where
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

instance Zf.IsOrdinal.ofNat : Zf.IsOrdinal (OfNat.ofNat n) := by
  induction n with
  | zero => apply Zf.IsOrdinal.zero
  | succ => apply Zf.IsOrdinal.succ

instance Zf.IsTransitive.inter
  [transx: Zf.IsTransitive x]
  [transy: Zf.IsTransitive y] : Zf.IsTransitive (x ∩ y) where
  mem_is_sub := by
    intro a mem b b_in_a
    apply mem_inter.mpr
    have ⟨l,r⟩ := mem_inter.mp mem
    apply And.intro
    exact transx.mem_is_sub _ l _ b_in_a
    exact transy.mem_is_sub _ r _ b_in_a

instance Zf.IsTransitive.union
  [transx: Zf.IsTransitive x]
  [transy: Zf.IsTransitive y] : Zf.IsTransitive (x ∪ y) where
  mem_is_sub := by
    intro a mem b b_in_a
    apply mem_union.mpr
    cases mem_union.mp mem <;> rename_i mem
    exact Or.inl <| transx.mem_is_sub _ mem _ b_in_a
    exact Or.inr <| transy.mem_is_sub _ mem _ b_in_a

instance Zf.IsOrdinal.inter
  [ordx: Zf.IsOrdinal x]
  [Zf.IsOrdinal y] : Zf.IsOrdinal (x ∩ y) where
  mem_is_tri := by
    intro a b a_in_xy b_in_xy
    have ⟨a_in_x,_⟩ := mem_inter.mp a_in_xy
    have ⟨b_in_x,_⟩ := mem_inter.mp b_in_xy
    apply ordx.mem_is_tri <;> assumption

def Zf.IsOrdinal.mem_or_eq_of_sub
  [ordx: Zf.IsOrdinal x]
  [ordy: Zf.IsOrdinal y] :
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
  cases mem_or_eq_of_sub inter_sub_x <;> rename_i hx
  <;> cases mem_or_eq_of_sub inter_sub_y <;> rename_i hy
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
  apply (fun a b => @Zf.IsOrdinal.mk a b) _ _
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

instance Zf.IsOrdinal.union [ordx: Zf.IsOrdinal x] [ordy: Zf.IsOrdinal y] : Zf.IsOrdinal (x ∪ y) where
  mem_is_tri := by
    intro a b a_in_union b_in_union
    cases mem_union.mp a_in_union <;> rename_i ha <;>
    cases mem_union.mp b_in_union <;> rename_i hb
    all_goals apply Zf.IsOrdinal.mem_total
    all_goals try (apply Zf.IsOrdinal.mem ordx; assumption; done)
    all_goals (apply Zf.IsOrdinal.mem ordy; assumption; done)

instance Zf.IsOrdinal.sUnion (ordx: ∀x₀ ∈ x, Zf.IsOrdinal x₀) : Zf.IsOrdinal (⋃₀ x) where
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

def Zf.IsOrdinal.sInter {x: Zf} (ordx: ∀x₀ ∈ x, Zf.IsOrdinal x₀) (h: x.Nonempty) : Zf.IsOrdinal (⋂₀ x) where
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

class Zf.IsLimitOrdinal (x: Zf) extends Zf.IsOrdinal x : Prop where
  not_succ: ∀y, Zf.IsOrdinal y -> Zf.succ y ≠ x

instance Zf.IsLimitOrdinal.zero : Zf.IsLimitOrdinal 0 where
  not_succ := by
    intro x _ h
    have not_mem := not_mem_empty x
    have : (0: Zf) = ∅ := rfl
    erw [←this, ←h] at not_mem
    apply not_mem
    apply mem_succ.mpr
    exact Or.inl rfl

instance Zf.IsLimitOrdinal.ω₀ : Zf.IsLimitOrdinal ω₀ where
  mem_is_sub := by
    intro x x_in_omega k k_in_x
    apply mem_ω₀.mpr
    have ⟨ n,prf ⟩ := mem_ω₀.mp x_in_omega
    subst prf
    have ⟨m,_,_⟩ := mem_of_nat.mp k_in_x
    exists m
  mem_is_tri := by
    intro a b a_in_omega b_in_omega
    have ⟨n,prf⟩ := mem_ω₀.mp a_in_omega
    have ⟨m,prf⟩ := mem_ω₀.mp b_in_omega
    subst a; subst b;
    rcases compare_linear n m with n_lt_m | n_eq_m | m_lt_n
    left
    apply mem_of_nat.mpr
    exists n
    right; left
    rw [n_eq_m]
    right; right
    apply mem_of_nat.mpr
    exists m
  not_succ := by
    intro x _ h
    have := (@mem_ω₀ x).mp
    rw [←h] at this
    have ⟨m,prf⟩ := this (mem_succ.mpr (.inl rfl))
    subst x
    have := mem_ω₀.mpr ⟨m.succ,rfl⟩
    rw [←h] at this
    exact mem_wf.irrefl this

def Zf.IsOrdinal.succ_sub_of_mem [ordx: Zf.IsOrdinal x] : ∀y, y ∈ x -> y.succ ⊆ x := by
  intro y y_in_x z z_in_succ
  cases mem_succ.mp z_in_succ
  subst y
  assumption
  apply ordx.mem_is_sub <;> assumption

def Zf.IsLimitOrdinal.succ_mem_of_mem [ordx: Zf.IsLimitOrdinal x] : ∀y ∈ x, y.succ ∈ x := by
  intro y y_in_x
  have yord : Zf.IsOrdinal y := ordx.mem y_in_x
  have := Zf.IsOrdinal.succ_sub_of_mem _ y_in_x
  cases IsOrdinal.mem_or_eq_of_sub this
  assumption
  rename_i h
  have := ordx.not_succ y yord h
  contradiction

def Zf.IsOrdinal.succ_mem_succ [ordb: Zf.IsOrdinal b] : a ∈ b -> a.succ ∈ b.succ := by
  intro r
  have := ordb.mem r
  apply mem_succ.mpr
  exact Or.comm.mp <| mem_or_eq_of_sub (succ_sub_of_mem _ r)

def Zf.IsOrdinal.succ_sUnion [ordx: Zf.IsOrdinal x] : ⋃₀ x.succ = x := by
  apply ext_sub
  apply (Zf.sUnion_least_upper_bound _ _).mpr
  intro a a_in_xsucc
  cases mem_succ.mp a_in_xsucc
  subst x
  rfl
  apply ordx.mem_is_sub
  assumption
  intro a a_in_x
  apply mem_sUnion.mpr
  exists a.succ
  apply And.intro
  apply succ_mem_succ
  assumption
  exact mem_succ.mpr (.inl rfl)

def Zf.IsLimitOrdinal.sUnion [ordx: Zf.IsLimitOrdinal x] : ⋃₀ x = x := by
  apply ext_sub
  apply (Zf.sUnion_least_upper_bound _ _).mpr
  exact ordx.mem_is_sub
  intro a a_in_x
  apply mem_sUnion.mpr
  exists a.succ
  apply And.intro
  apply succ_mem_of_mem
  assumption
  exact mem_succ.mpr (.inl rfl)

def Zf.IsOrdinal.empty_mem [ordx: Zf.IsOrdinal x] (h: x.Nonempty) : ∅ ∈ x := by
  obtain ⟨x₀, mem⟩ := h
  apply ClassicLogic.byCases x₀.Nonempty
  intro h
  have ordx₀ := ordx.mem mem
  exact ordx.mem_is_sub _ mem _ (empty_mem h)
  intro h
  cases Zf.not_nonempty _ h
  assumption
termination_by x

def Zf.IsOrdinal.sInter_eq_empty [ordx: Zf.IsOrdinal x] : ⋂₀ x = ∅ := by
  apply ext_empty
  intro a h
  apply ClassicLogic.byCases x.Nonempty
  intro xnonempty
  have := Zf.not_mem_empty _ <| (Zf.mem_sInter xnonempty).mp h ∅ (empty_mem xnonempty)
  contradiction
  intro notnonempty
  cases Zf.not_nonempty _ notnonempty
  rw [Zf.sInter_empty] at h
  exact Zf.not_mem_empty _ h

def Ordinal := { x: Zf // x.IsOrdinal }
def Ordinal.mk (x: Zf) [h: x.IsOrdinal] : Ordinal := ⟨x, h⟩

instance : OfNat Ordinal n := ⟨OfNat.ofNat n, Zf.IsOrdinal.ofNat⟩

instance (o: Ordinal) : Zf.IsOrdinal o.val := o.property

instance : LE Ordinal := ⟨(·.val ⊆ ·.val)⟩
instance : LT Ordinal := ⟨(·.val ∈ ·.val)⟩

def Ordinal.le_of_lt {a b: Ordinal} : a < b -> a ≤ b := (b.property.toIsTransitive.mem_is_sub _ ·)
def Ordinal.le_of_eq {a b: Ordinal} : a = b -> a ≤ b
| .refl _ => (Zf.sub.refl _)

def Ordinal.val.inj {a b: Ordinal} : a.val = b.val -> a = b := by
  intro h
  cases a; cases b
  congr

def Ordinal.lt_or_eq_of_le' {a b: Ordinal} : a ≤ b -> a < b ∨ a = b := by
  intro h
  rcases Zf.IsOrdinal.mem_or_eq_of_sub h with a_lt_b | a_eq_b
  left; assumption
  right; apply val.inj; assumption

def Ordinal.succ (a: Ordinal) : Ordinal where
  val := a.val.succ
  property := inferInstance

def Ordinal.le_of_lt_succ {a b: Ordinal} : a < b.succ -> a ≤ b := by
  intro h
  cases Zf.mem_succ.mp h
  apply le_of_eq
  apply val.inj
  assumption
  apply le_of_lt
  assumption

def Ordinal.IsLimit (o: Ordinal) := ∀x: Ordinal, x.succ ≠ o

def Ordinal.IsLimit.IsLimitOrdinal {o: Ordinal} :
  o.IsLimit ↔ o.val.IsLimitOrdinal := by
  apply Iff.intro
  · intro h
    apply Zf.IsLimitOrdinal.mk
    intro x h₀ h₁
    replace h := fun x => h x
    cases o with | mk o ord =>
    apply h ⟨x, h₀⟩
    unfold succ
    congr
  · intro h
    intro x h₀
    apply h.not_succ x.val
    exact x.property
    subst o
    rfl

def Ordinal.min (a b: Ordinal) : Ordinal where
  val := a.val ∩ b.val
  property := inferInstance

def Ordinal.max (a b: Ordinal) : Ordinal where
  val := a.val ∪ b.val
  property := inferInstance

instance : Min Ordinal where
  min := Ordinal.min
instance : Max Ordinal where
  max := Ordinal.max

instance : IsLinearOrder Ordinal where
  le_antisymm := by
    intro a b ab ba
    apply Ordinal.val.inj
    apply Zf.ext_sub <;> assumption
  le_total := by
    intro a b
    rcases Zf.IsOrdinal.mem_total a.property b.property with a_lt_b | a_eq_b | b_lt_a
    left
    apply Ordinal.le_of_lt; assumption
    left
    apply Ordinal.le_of_eq; apply Ordinal.val.inj; assumption
    right
    apply Ordinal.le_of_lt; assumption
  le_complete := by
    intro a b
    rcases Zf.IsOrdinal.mem_total a.property b.property with a_lt_b | a_eq_b | b_lt_a
    left
    apply Ordinal.le_of_lt; assumption
    left
    apply Ordinal.le_of_eq; apply Ordinal.val.inj; assumption
    right
    intro a_le_b
    exact Zf.mem_wf.irrefl (a_le_b _ b_lt_a)
  le_trans := by
    intro a b c
    apply Zf.sub.trans
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro a_lt_b
    apply And.intro
    apply Ordinal.le_of_lt
    assumption
    intro g
    exact Zf.mem_wf.irrefl (g _ a_lt_b)
    intro ⟨h, g⟩
    cases Ordinal.lt_or_eq_of_le' h
    assumption
    subst b
    have := g (Zf.sub.refl _)
    contradiction
  min_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply Ordinal.val.inj
    show a.val ∩ b.val = a.val
    apply Zf.ext_sub
    apply Zf.inter_sub_left
    intro x mem
    apply Zf.mem_inter.mpr
    apply And.intro
    assumption
    apply h
    assumption
    intro h
    rw [←h]
    apply Zf.inter_sub_right
  min_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply Ordinal.val.inj
    show a.val ∩ b.val = b.val
    apply Zf.ext_sub
    apply Zf.inter_sub_right
    intro x mem
    apply Zf.mem_inter.mpr
    apply And.intro
    apply h
    assumption
    assumption
    intro h
    rw [←h]
    apply Zf.inter_sub_left
  max_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply Ordinal.val.inj
    show a.val ∪ b.val = b.val
    apply Zf.ext_sub
    intro x mem
    cases Zf.mem_union.mp mem
    apply h
    assumption
    assumption
    apply Zf.sub_union_right
    intro h
    rw [←h]
    apply Zf.sub_union_left
  max_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply Ordinal.val.inj
    show a.val ∪ b.val = a.val
    apply Zf.ext_sub
    intro x mem
    cases Zf.mem_union.mp mem
    assumption
    apply h
    assumption
    apply Zf.sub_union_left
    intro h
    rw [←h]
    apply Zf.sub_union_right

@[ext]
def Ordinal.ext (a b: Ordinal) : (∀x, x < a ↔ x < b) -> a = b := by
  intro h
  cases a with | mk a aord =>
  cases b with | mk b bord =>
  congr
  ext x
  apply Iff.intro
  intro m
  apply (h ⟨x, _⟩).mp
  assumption
  apply Zf.IsOrdinal.mem
  exact aord
  assumption
  intro m
  apply (h ⟨x, _⟩).mpr
  assumption
  apply Zf.IsOrdinal.mem
  exact bord
  assumption

def Ordinal.lt_succ_self {a: Ordinal}: a < a.succ := by
  apply Zf.mem_succ.mpr
  left; rfl

def Ordinal.lt_of_succ_lt_succ {a b: Ordinal}: a.succ < b.succ -> a < b := by
  show a.succ.val ∈ b.succ.val -> a.val ∈ b.val
  intro h
  cases Zf.mem_succ.mp h <;> rename_i h
  rw [←h]
  apply lt_succ_self
  show a < b
  apply lt_trans _ h
  apply lt_succ_self

def Ordinal.lt_of_succ_le {a b: Ordinal}: a.succ ≤ b -> a < b := by
  intro h
  cases lt_or_eq_of_le h
  apply lt_trans
  apply lt_succ_self
  assumption
  subst b
  apply lt_succ_self

def Ordinal.squeeze {a b: Ordinal} : a < b -> b < a.succ -> False := by
  intro h g
  cases Zf.mem_succ.mp g <;> rename_i g
  have : a = b := by
    cases a; cases b
    congr
    symm
    assumption
  cases this
  exact lt_irrefl h
  exact lt_asymm h g

def Ordinal.succ_le_of_lt {a b: Ordinal}: a < b -> a.succ ≤ b := by
  intro g
  apply ClassicLogic.byCases (a.succ < b) <;> intro h
  apply le_of_lt
  assumption
  apply le_of_eq
  replace h := le_of_not_lt h
  cases Or.symm (lt_or_eq_of_le h) <;> rename_i h
  symm; assumption
  have := squeeze g h
  contradiction

def Ordinal.lt_succ_of_le {a b: Ordinal} : a ≤ b -> a < b.succ := by
  intro h
  cases lt_or_eq_of_le h
  apply lt_trans
  assumption
  apply lt_succ_self
  subst a
  apply lt_succ_self

def Ordinal.succ_lt_succ {a b: Ordinal}: a < b -> a.succ < b.succ := by
  intro h
  apply lt_succ_of_le
  apply succ_le_of_lt
  assumption

def Ordinal.succ_le_succ {a b: Ordinal}: a ≤ b -> a.succ ≤ b.succ := by
  intro h
  apply le_of_lt_succ
  apply succ_lt_succ
  apply lt_succ_of_le
  assumption

def Ordinal.le_succ_self {a: Ordinal}: a ≤ a.succ := by
  apply le_of_lt
  apply lt_succ_self

def Ordinal.le_of_succ_le_succ {a b: Ordinal}: a.succ ≤ b.succ -> a ≤ b := by
  intro h
  apply le_of_lt_succ
  apply lt_of_succ_lt_succ
  apply lt_succ_of_le
  assumption

def Ordinal.inf (a: Zf) (mem: ∀x ∈ a, x.IsOrdinal) : Ordinal where
  val := ⋂₀ a
  property := by
    if h:a.Nonempty then
      exact Zf.IsOrdinal.sInter mem h
    else
      rw [Zf.not_nonempty _ h, Zf.sInter_empty]
      exact Zf.IsOrdinal.zero

def Ordinal.sup (a: Zf) (mem: ∀x ∈ a, x.IsOrdinal) : Ordinal where
  val := ⋃₀ a
  property := Zf.IsOrdinal.sUnion mem

def Ordinal.succ_sup (o: Ordinal) : Ordinal.sup o.succ.val (fun _ => (o.succ.property.mem ·)) = o := by
  unfold sup succ
  dsimp
  cases o with | mk o ord =>
  dsimp
  congr
  exact Zf.IsOrdinal.succ_sUnion

def Ordinal.limit_sup (o: Ordinal) (h: o.IsLimit) : Ordinal.sup o.val (fun _ => (o.property.mem ·)) = o := by
  unfold sup
  cases o with | mk o ord =>
  dsimp
  congr
  have := Ordinal.IsLimit.IsLimitOrdinal.mp h
  refine Zf.IsLimitOrdinal.sUnion

def Ordinal.ord_inf (o: Ordinal) : Ordinal.inf o.val (fun _ => (o.property.mem ·)) = 0 := by
  unfold inf
  cases o with | mk o ord =>
  dsimp
  congr
  apply Zf.IsOrdinal.sInter_eq_empty

instance : WellFoundedRelation Ordinal where
  rel a b := a < b
  wf := by
    apply WellFounded.intro
    intro ⟨a, aord⟩
    induction a using Zf.mem_wf.induction with
    | h a ih =>
    apply Acc.intro
    intro ⟨b, bord⟩ lt
    replace lt : b ∈ a := lt
    apply ih
    assumption

def Ordinal.rec { motive: Ordinal -> Sort _ } (mem: ∀x, (∀y < x, motive y) -> motive x)
  (o: Ordinal) : motive o :=
  mem o (fun y _ => Ordinal.rec mem y)
termination_by o
decreasing_by assumption

def Ordinal.recZf { motive: Ordinal -> Sort _ } (mem: ∀x, (∀y, (h: y ∈ x.val) -> motive ⟨y, x.property.mem h⟩) -> motive x)
  (o: Ordinal) : motive o :=
  mem o (fun y h => Ordinal.recZf mem ⟨y, o.property.mem h⟩)
termination_by o
decreasing_by assumption

open Classical in
noncomputable def Ordinal.transfiniteRecursion
  { motive: Ordinal -> Sort _ }
  (zero: motive 0)
  (limit: ∀x, 0 < x -> x.IsLimit -> (∀y < x, motive y) -> motive x)
  (succ: ∀x, motive x -> motive x.succ)
  (o: Ordinal) : motive o :=
  if h:o = 0 then
    h ▸ zero
  else if g:∃o': Ordinal, o'.succ = o then
    have := succ (Classical.choose g) (transfiniteRecursion zero limit succ _)
    Classical.choose_spec g ▸ this
  else
    limit o (by
      apply lt_of_not_le
      intro h
      cases lt_or_eq_of_le h <;> rename_i h
      exact Zf.not_mem_empty _ h
      contradiction) (by
      apply not_exists.mp
      assumption) (by
      intro y h
      apply transfiniteRecursion <;> assumption)
termination_by o
decreasing_by
  apply Ordinal.lt_of_succ_lt_succ
  rw [Classical.choose_spec g]
  apply lt_succ_self
  assumption

def Zf.IsOrdinal.add (a b: Zf) :
  a.IsOrdinal ->
  b.IsOrdinal -> Zf := by
  intro orda ordb
  refine a ∪ ⋃₀ (?_: Zf)
  apply b.mapAttach
  intro b' b'_in_b
  apply Zf.succ
  apply Zf.IsOrdinal.add a b'
  assumption
  apply Zf.IsOrdinal.mem _ b'_in_b
  assumption
termination_by b

def Ordinal.map (o: Ordinal) : (Ordinal -> Zf) -> Zf :=
  fun f => o.val.mapAttach <| fun o' mem => f ⟨o', o.property.mem mem⟩

def Ordinal.sup_map (o: Ordinal) : (Ordinal -> Ordinal) -> Ordinal :=
  fun f => Ordinal.sup (o.map (fun x => (f x).val)) (fun x mem => by
    have ⟨x', x'_in_o, x_eq⟩  := Zf.mem_mapAttach.mp mem
    subst x
    dsimp
    apply (f _).property)

def Ordinal.add (a b: Ordinal) : Ordinal where
  val :=  Zf.IsOrdinal.add a.val b.val a.property b.property
  property := by
    induction b using rec with | mem b ih =>
    unfold Zf.IsOrdinal.add
    apply Zf.IsOrdinal.union (ordx := _) (ordy := _)
    exact a.property
    apply Zf.IsOrdinal.sUnion
    intro x₀ mem
    have ⟨b', b'_in_b, prf⟩  := Zf.mem_mapAttach.mp mem
    subst x₀
    apply Zf.IsOrdinal.succ (ordx := _)
    apply ih ⟨b', _⟩
    assumption
    apply b.property.mem
    assumption

instance [orda: Zf.IsOrdinal a] [ordb: Zf.IsOrdinal b] : Zf.IsOrdinal (Zf.IsOrdinal.add a b orda ordb) :=
  (Ordinal.add ⟨a, orda⟩ ⟨b, ordb⟩).property

instance : Add Ordinal := ⟨.add⟩

def Ordinal.add.add_zero (o: Ordinal) : o + 0 = o := by
  show o.add 0 = o
  unfold add
  unfold Zf.IsOrdinal.add
  have : Subtype.val (0: Ordinal) = ∅ := rfl
  cases o with | mk o ord =>
  congr
  rw [Zf.mapAttach_congr _ _ this, Zf.mapAttach_nil, Zf.sUnion_nil, Zf.union_nil]

def Ordinal.add.zero_add (o: Ordinal) : 0 + o = o := by
  show (0: Ordinal).add o = o
  induction o using rec with | mem o ih =>
  unfold add
  unfold Zf.IsOrdinal.add
  have : Subtype.val (0: Ordinal) = ∅ := rfl
  cases o with | mk o ord =>
  congr
  show ∅ ∪ _ = _
  rw [Zf.nil_union]
  dsimp
  ext x
  apply Iff.intro
  intro mem
  have ⟨x₀, x₀_mem, x_in_x₀⟩  := Zf.mem_sUnion.mp mem
  have ⟨x₁, x₁_in_o, x₀_eq⟩  := Zf.mem_mapAttach.mp x₀_mem
  subst x₀
  rw [Subtype.mk.inj (ih ⟨x₁, ord.mem x₁_in_o⟩ x₁_in_o)] at x_in_x₀
  cases Zf.mem_succ.mp x_in_x₀ <;> rename_i h
  subst x₁
  assumption
  apply ord.toIsTransitive.mem_is_sub
  assumption
  assumption
  intro x_in_o
  apply Zf.mem_sUnion.mpr
  exists x.succ
  apply flip And.intro
  apply Zf.mem_succ.mpr
  left; rfl
  apply Zf.mem_mapAttach.mpr
  exists x
  exists x_in_o
  congr
  symm
  apply Subtype.mk.inj <| ih ⟨x, ord.mem x_in_o⟩ x_in_o

def Ordinal.add.assoc (a b c: Ordinal) : (a + b) + c = a + (b + c) := by
  induction c using recZf generalizing a b with | mem c ih =>
  show add (add a b) c = add a (add b c)
  cases a with | mk a aord =>
  cases b with | mk b bord =>
  unfold add Zf.IsOrdinal.add
  dsimp
  ext x
  cases x with | mk x xord =>
  show x ∈ _ ↔ x ∈ _
  dsimp
  apply Iff.intro
  · intro h
    replace h := Zf.mem_union.mp h
    apply Zf.mem_union.mpr
    apply ClassicLogic.byCases (x ∈ a)
    exact .inl
    intro x_notin_a; right
    apply Zf.mem_sUnion.mpr
    cases h <;> rename_i h
    have g := Zf.IsOrdinal.toIsTransitive.mem_is_sub _ (Zf.mem_succ.mpr (.inl rfl)) _ h
    refine ⟨_, ?_, g⟩
    apply Zf.mem_mapAttach.mpr
    refine ⟨b, ?_, rfl⟩


    sorry





    sorry
  . sorry






def Zf.sUnion_mapAttach_succ (a: Zf) (f: ∀x ∈ a, Zf) (aord: a.IsOrdinal) (ford: ∀x (h: x ∈ a), (f x h).IsOrdinal) :
  ⋃₀a.mapAttach (fun x h => (f x h).succ) = (⋃₀ a.mapAttach f).succ := by
  ext x
  apply Iff.intro
  · intro h
    replace ⟨x', h, x_in_x'⟩ := Zf.mem_sUnion.mp h
    replace ⟨a', h, _⟩ := Zf.mem_mapAttach.mp h
    subst x'
    cases Zf.mem_succ.mp x_in_x' <;> (clear x_in_x'; rename_i x_in_x')
    · subst x
      apply Zf.mem_succ.mpr
      right
      apply Zf.mem_sUnion.mpr
      exists f a' h
      apply And.intro
      apply Zf.mem_mapAttach.mpr
      exists a'
      exists h
      sorry
    · apply Zf.mem_succ.mpr
      right
      apply Zf.mem_sUnion.mpr
      exists f a' h
      apply And.intro
      apply Zf.mem_mapAttach.mpr
      exists a'
      exists h
      assumption
  · sorry

def Ordinal.add.add_succ (a b: Ordinal) : a + b.succ = (a + b).succ := by
  induction b using recZf with | mem b ih =>
  show add _ _ = _
  unfold add Zf.IsOrdinal.add
  cases a with | mk a aord =>
  cases b with | mk b bord =>
  congr 1
  unfold Ordinal.succ
  rw [Zf.mapAttach_congr _ _ (Zf.succ_eq_insert b)]
  rw [Zf.mapAttach_insert, Zf.sUnion_insert]
  dsimp
  show _ = (add _ _).val.succ
  conv => { rhs; unfold add Zf.IsOrdinal.add }
  dsimp
  dsimp at ih






  have : (Zf.IsOrdinal.add o ∅ ord Zf.IsOrdinal.zero) = o := by
    exact Subtype.mk.inj (add_zero ⟨o, ord⟩)
  rw [this]
  rw [Zf.sub_union]
  intro x mme
  apply Zf.mem_succ.mpr
  right; assumption
  show {{}} ∪ {} = {∅}
  rw [Zf.union_nil]
  -- show add _ _ = succ (add _ _)
  -- unfold add Zf.IsOrdinal.add
  -- cases a with | mk a aord =>
  -- cases b with | mk b bord =>
  -- unfold succ
  -- dsimp
  -- congr 1
  -- ext x
  -- apply Iff.intro
  -- · intro h
  --   cases Zf.mem_union.mp h <;> (clear h; rename_i h)
  --   apply Zf.mem_union.mpr; right
  --   apply Zf.mem_union.mpr; left; assumption
  --   replace ⟨x₀, h, x_in_x₀⟩ := Zf.mem_sUnion.mp h
  --   replace ⟨b', h, x₀_eq⟩  := Zf.mem_mapAttach.mp h
  --   subst x₀
  --   -- cases Zf.mem_succ.mp h <;> rename_i h
  --   -- subst b'
  --   apply Zf.mem_succ.mpr

  --     sorry
  --   -- right
  --   -- apply Zf.mem_union.mpr; right
  --   -- apply Zf.mem_sUnion.mpr
  --   -- cases Zf.mem_succ.mp x_in_x₀ <;> rename_i h
  --   -- subst x
  --   -- clear x_in_x₀
  --   -- sorry
  --   -- refine ⟨_, ?_, x_in_x₀⟩
  --   -- apply Zf.mem_mapAttach.mpr
  --   -- refine ⟨b, ?_, rfl⟩








  --   repeat sorry
  -- · intro h
  --   cases Zf.mem_succ.mp h <;> rename_i h
  --   subst x
  --   clear h
  --   apply Zf.mem_union.mpr; right
  --   apply Zf.mem_sUnion.mpr
  --   exists b.mapAttach fun b' b'_in_b => (Zf.IsOrdinal.add a b' aord (bord.mem b'_in_b)).succ
  --   apply And.intro
  --   apply Zf.mem_mapAttach.mpr
  --   refine ⟨ ⟩

  --   repeat sorry

def Ordinal.add.add_one (o: Ordinal) : o + 1 = o.succ := by
  -- show o + (Ordinal.succ 0) = o.succ
  -- rw [add_succ, add_zero]
  show add _ _ = _
  unfold add Zf.IsOrdinal.add
  cases o with | mk o ord =>
  congr 1
  rw [
    Zf.mapAttach_congr (Subtype.val (1: Ordinal)) {{}},
    Zf.mapAttach_singleton, Zf.sUnion_singleton]
  dsimp
  have : (Zf.IsOrdinal.add o ∅ ord Zf.IsOrdinal.zero) = o := by
    exact Subtype.mk.inj (add_zero ⟨o, ord⟩)
  rw [this]
  rw [Zf.sub_union]
  intro x mme
  apply Zf.mem_succ.mpr
  right; assumption
  show {{}} ∪ {} = {∅}
  rw [Zf.union_nil]

def Ordinal.add.lt_right (a b k: Ordinal) : a < b -> k + a < k + b := by
  intro a_lt_b
  show (k.add a).val ∈ (k.add b).val
  unfold add
  dsimp
  induction b using recZf generalizing a with | mem b ih =>
  replace ih := fun b' => ih b'
  conv => {
    lhs
    unfold Zf.IsOrdinal.add
  }
  apply Zf.mem_union.mpr
  right
  apply Zf.mem_sUnion.mpr
  exists (Zf.IsOrdinal.add k.val a.val k.property a.property).succ
  apply flip And.intro
  apply Zf.mem_succ.mpr; left; rfl
  apply Zf.mem_mapAttach.mpr
  exists a.val
  exists a_lt_b

def Ordinal.add.add_limit (a b: Ordinal) (h: b.IsLimit) (b_pos: 0 < b) : a + b = (b.sup_map (fun b => a + b)) := by
  induction b using rec with | mem b ih =>
  ext x
  apply Iff.trans _ Zf.mem_sUnion.symm
  apply Iff.intro
  · intro m
    replace m : x < add _ _ := m
    unfold add Zf.IsOrdinal.add at m
    cases Zf.mem_union.mp m <;> (clear m; rename_i m)
    · dsimp
      exists a.val
      apply flip And.intro
      assumption
      apply Zf.mem_mapAttach.mpr
      dsimp
      exists 0
      exists b_pos
      erw [add_zero]
    · replace ⟨x₀, m, x_in_x₀⟩ := Zf.mem_sUnion.mp m
      replace ⟨b', m, x₀_eq⟩ := Zf.mem_mapAttach.mp m
      subst x₀
      cases Zf.mem_succ.mp x_in_x₀ <;> (clear x_in_x₀; rename_i h)
      · dsimp
        exists x.val.succ
        apply flip And.intro
        apply Zf.mem_succ.mpr; left; rfl
        apply Zf.mem_mapAttach.mpr
        dsimp
        exists b'.succ
        refine ⟨?_, ?_⟩
        apply Zf.IsLimitOrdinal.succ_mem_of_mem (ordx := _)
        assumption
        apply Ordinal.IsLimit.IsLimitOrdinal.mp
        assumption
        have := b.property.mem m
        show _ = (a + (Ordinal.mk b').succ).val
        rw [add_succ]
        congr
        cases x
        dsimp at h
        subst h
        rfl
      · dsimp
        exists  Zf.IsOrdinal.add a.val b' a.property (b.property.mem m)
        apply flip And.intro
        assumption
        apply Zf.mem_mapAttach.mpr
        dsimp
        refine ⟨b', ?_, ?_⟩
        assumption
        rfl
  · intro ⟨x', x'_in_map, x_in_x'⟩
    have ⟨b', b'_in_b, x'_eq⟩  := Zf.mem_mapAttach.mp x'_in_map
    clear x'_in_map
    dsimp at x'_eq
    subst x'
    apply lt_trans
    assumption
    apply Ordinal.add.lt_right
    assumption
