class IsWellOrder (rel: α -> α -> Prop) where
  wf: WellFounded rel
  tri: ∀a b: α, rel a b ∨ a = b ∨ rel b a
  trans: ∀a b c: α, rel a b -> rel b c -> rel a c

structure WellOrder.{u} where
  ty: Type u
  rel: ty -> ty -> Prop
  wo: IsWellOrder rel

inductive WellOrder.Le : WellOrder.{u} -> WellOrder.{v} -> Prop where
| mk (f: α₀ -> α₁)
    (f_inj: ∀x y, f x = f y -> x = y)
    (f_resp: ∀x y, r₀ x y -> r₁ (f x) (f y)) :
    Le (.mk α₀ r₀ to₀) (.mk α₁ r₁ to₁)

inductive WellOrder.Equiv : WellOrder.{u} -> WellOrder.{v} -> Type _ where
| mk (f: α₀ -> α₁) (g: α₁ -> α₀) :
    (∀x, f (g x) = x) ->
    (∀x, g (f x) = x) ->
    (f_resp: ∀x y, r₀ x y -> r₁ (f x) (f y)) ->
    (g_resp: ∀x y, r₁ x y -> r₀ (g x) (g y)) ->
    Equiv (.mk α₀ r₀ to₀) (.mk α₁ r₁ to₁)

@[refl]
def WellOrder.Le.refl (a: WellOrder) : Le a a := Le.mk id (fun _ _ => id) (fun _ _ => id)

def WellOrder.Le.trans {a b c: WellOrder} : Le a b -> Le b c -> Le a c
| .mk ab ab_inj ab_resp, .mk bc bc_inj bc_resp => by
  apply Le.mk (bc ∘ ab)
  intro x y h
  exact ab_inj _ _ (bc_inj _ _ h)
  intro x y h
  dsimp
  apply bc_resp
  apply ab_resp
  exact h

@[refl]
def WellOrder.Equiv.refl (a: WellOrder) : Equiv a a :=
  ⟨ id, id, fun _ => rfl, fun _ => rfl, fun {_ _} => id, fun {_ _} => id ⟩

@[symm]
def WellOrder.Equiv.symm { a b: WellOrder } : Equiv a b -> Equiv b a
| .mk f g fg gf fresp gresp => .mk g f gf fg gresp fresp

@[symm]
def WellOrder.Equiv.symm_symm (ab: Equiv a b) : ab.symm.symm = ab := by
  cases ab
  rfl

def WellOrder.Equiv.trans { a b c: WellOrder } : Equiv a b -> Equiv b c -> Equiv a c
| .mk ab ba abba baab ab_resp ba_resp,
  .mk bc cb bccb cbbc bc_resp cb_resp => by
  apply Equiv.mk (bc ∘ ab) (ba ∘ cb)
  all_goals dsimp
  · intro x
    rw [abba, bccb]
  · intro x
    rw [cbbc, baab]
  · intro x y xy
    apply bc_resp
    apply ab_resp
    exact xy
  · intro x y xy
    apply ba_resp
    apply cb_resp
    exact xy

def WellOrder.Equiv.left : Equiv a b -> a.1 -> b.1
| .mk f _ _ _ _ _ => f
def WellOrder.Equiv.right : Equiv a b -> b.1 -> a.1
| .mk _ g  _ _ _ _ => g
def WellOrder.Equiv.right_left : ∀(h: Equiv a b), ∀x, h.left (h.right x) = x
| .mk _ _ prf _ _ _ => prf
def WellOrder.Equiv.left_right : ∀(h: Equiv a b), ∀x, h.right (h.left x) = x
| .mk _ _ _ prf _ _ => prf
def WellOrder.Equiv.left_resp : ∀(h: Equiv a b), ∀x y, a.2 x y -> b.2 (h.left x) (h.left y)
| .mk _ _ _ _ prf _ => prf
def WellOrder.Equiv.right_resp : ∀(h: Equiv a b), ∀x y, b.2 x y -> a.2 (h.right x) (h.right y)
| .mk _ _ _ _ _ prf => prf

def WellOrder.Equiv.left_inj (h: Equiv a b) : ∀x y, h.left x = h.left y -> x = y := by
  intro x y hx_eq_hy
  have : h.right (h.left x) = h.right (h.left y) := by rw [hx_eq_hy]
  rw [h.left_right, h.left_right] at this
  exact this

def WellOrder.Equiv.right_inj (h: Equiv a b) : ∀x y, h.right x = h.right y -> x = y := by
  intro x y hx_eq_hy
  have : h.left (h.right x) = h.left (h.right y) := by rw [hx_eq_hy]
  rw [h.right_left, h.right_left] at this
  exact this

def WellOrder.Equiv.le_left (h: Equiv a b) : Le a b := .mk h.left h.left_inj h.left_resp
def WellOrder.Equiv.le_right (h: Equiv a b) : Le b a := .mk h.right h.right_inj h.right_resp

instance WellOrder.setoid : Setoid WellOrder where
  r a b := Nonempty (Equiv a b)
  iseqv := {
    refl := fun a => Nonempty.intro (.refl a)
    symm := fun ⟨ ab ⟩ => Nonempty.intro (.symm ab)
    trans := fun ⟨ ab ⟩ ⟨ bc ⟩  => Nonempty.intro (.trans ab bc)
  }

def Ordinal := Quotient WellOrder.setoid
def Ordinal.mk : WellOrder -> Ordinal := Quotient.mk WellOrder.setoid
def Ordinal.ind { motive: Ordinal -> Prop } : (mk: ∀x, motive (mk x)) -> ∀o, motive o := Quotient.ind
def Ordinal.lift : (f: WellOrder -> α) -> (all_eq: ∀x y, x ≈ y -> f x = f y) -> Ordinal -> α := Quotient.lift
def Ordinal.lift₂ : (f: WellOrder -> WellOrder -> α) -> (all_eq: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) -> Ordinal -> Ordinal -> α := Quotient.lift₂
def Ordinal.lift_mk : lift f all_eq (mk a) = f a := rfl
def Ordinal.lift₂_mk : lift₂ f all_eq (mk a) (mk b) = f a b := rfl
def Ordinal.exact : mk a = mk b -> a ≈ b := Quotient.exact
def Ordinal.sound : a ≈ b -> mk a = mk b := Quotient.sound
def Ordinal.sound' : WellOrder.Equiv a b -> mk a = mk b := Quotient.sound ∘ Nonempty.intro
def Ordinal.exists_rep : ∀o, ∃p, mk p = o := Quotient.exists_rep

def WellOrder.ulift (o: WellOrder) : WellOrder := by
  apply WellOrder.mk (ULift o.ty) _ _
  intro ⟨x⟩ ⟨y⟩
  exact o.rel x y
  apply IsWellOrder.mk <;> dsimp
  · apply WellFounded.intro
    intro ⟨x⟩
    induction x using o.wo.wf.induction with | h x ih =>
    apply Acc.intro
    intro ⟨y⟩ r
    apply ih
    assumption
  · intro ⟨x⟩ ⟨y⟩
    dsimp
    cases o.wo.tri x y <;> rename_i h
    apply Or.inl h
    apply Or.inr
    cases h <;> rename_i h
    apply Or.inl
    rw [h]
    exact Or.inr h
  · intro ⟨x⟩ ⟨y⟩ ⟨z⟩
    apply o.wo.trans

def WellOrder.ulift_equiv_self (o: WellOrder) : Equiv (ulift o) o := by
  apply Equiv.mk _ _ _ _ _ _
  exact ULift.down
  exact ULift.up
  intros; rfl
  intros; rfl
  exact fun _ _ => id
  exact fun _ _ => id

def WellOrder.ulift_equiv_left (a b: WellOrder) : Equiv a b -> Equiv (ulift a) b := by
  intro eq
  apply WellOrder.Equiv.trans
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.ulift_equiv_right (a b: WellOrder) : Equiv a b -> Equiv a (ulift b) := by
  intro eq
  apply flip WellOrder.Equiv.trans
  apply WellOrder.Equiv.symm
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.of_ulift_equiv_left (a b: WellOrder) : Equiv (ulift a) b -> Equiv a b := by
  intro eq
  apply WellOrder.Equiv.trans
  apply WellOrder.Equiv.symm
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.of_ulift_equiv_right (a b: WellOrder) : Equiv a (ulift b) -> Equiv a b := by
  intro eq
  apply flip WellOrder.Equiv.trans
  apply WellOrder.ulift_equiv_self
  exact eq

def WellOrder.ulift_equiv_ulift (a b: WellOrder) : Equiv a b -> Equiv (ulift a) (ulift b) := by
  intro eq
  apply ulift_equiv_left
  apply ulift_equiv_right
  exact eq

def WellOrder.of_ulift_equiv_ulift (a b: WellOrder) : Equiv (ulift a) (ulift b) -> Equiv a b := by
  intro eq
  apply of_ulift_equiv_left
  apply of_ulift_equiv_right
  exact eq

def Ordinal.ulift (o: Ordinal) : Ordinal := by
  apply o.lift (mk ∘ WellOrder.ulift) _
  · intro a b ⟨ab⟩
    apply sound'
    apply WellOrder.Equiv.mk _ _ _ _ _ _
    · exact ULift.up ∘ ab.left ∘ ULift.down
    · exact ULift.up ∘ ab.right ∘ ULift.down
    · intro ⟨x⟩
      dsimp
      rw [ab.right_left]
    · intro ⟨x⟩
      dsimp
      rw [ab.left_right]
    · intro ⟨x⟩ ⟨y⟩ r
      exact ab.left_resp _ _ r
    . intro ⟨x⟩ ⟨y⟩ r
      exact ab.right_resp _ _ r

def Ordinal.ulift_eq_self (o: Ordinal) : ulift o = o := by
  induction o using ind with | mk o =>
  apply sound'
  apply WellOrder.ulift_equiv_self

def Ordinal.empty : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk Empty
  apply IsWellOrder.mk
  apply WellFounded.intro
  repeat exact fun x => x.elim

def Ordinal.unit : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk Unit (fun _ _ => False)
  apply IsWellOrder.mk
  apply WellFounded.intro
  intro
  apply Acc.intro
  intro _ _
  contradiction
  intro a b
  apply Or.inr
  apply Or.inl
  rfl
  intros
  contradiction

def Ordinal.bool : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk Bool (fun a b => a < b)
  apply IsWellOrder.mk
  apply WellFounded.intro
  intro x
  apply Acc.intro
  intro y r
  cases x <;> cases y
  any_goals contradiction
  apply Acc.intro
  intro z _
  cases z <;> contradiction
  intro a b
  cases a <;> cases b <;> trivial
  intro a b c
  cases a <;> cases b <;> cases c <;> trivial

def Ordinal.ofNat (n: Nat) : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk (Fin n) _ _
  exact (· < ·)
  apply IsWellOrder.mk
  · apply WellFounded.intro
    rintro ⟨x, xLt⟩
    induction x using Nat.lt_wfRel.wf.induction with | h x ih =>
    apply Acc.intro
    intro y r
    apply ih
    exact r
  · rintro ⟨a, aLt⟩ ⟨b, bLt⟩
    cases Nat.decLt b a <;> rename_i h
    cases Nat.lt_or_eq_of_le (Nat.le_of_not_lt h)
    apply Or.inl
    assumption
    apply Or.inr
    apply Or.inl
    congr
    apply Or.inr
    apply Or.inr
    assumption
  · apply Fin.lt_trans

def Ordinal.omega : Ordinal := by
  apply Ordinal.mk
  apply WellOrder.mk Nat _ _
  exact (· < ·)
  apply IsWellOrder.mk
  exact Nat.lt_wfRel.wf
  exact Nat.lt_trichotomy
  apply Nat.lt_trans

instance : OfNat Ordinal n := ⟨ Ordinal.ulift (Ordinal.ofNat n) ⟩

inductive Sum.Lex (alt: α -> α -> Prop) (blt: β -> β -> Prop) : α ⊕ β -> α ⊕ β -> Prop where
| inl : alt x y -> Lex alt blt (inl x) (inl y)
| inl_inr: Lex alt blt (inl x) (inr y)
| inr : blt x y -> Lex alt blt (inr x) (inr y)

def WellOrder.add_rel (a b: WellOrder) : a.ty ⊕ b.ty -> a.ty ⊕ b.ty -> Prop := Sum.Lex a.rel b.rel

def WellOrder.add (a b: WellOrder) : WellOrder := by
  apply WellOrder.mk _ (add_rel a b) _
  apply IsWellOrder.mk
  · apply WellFounded.intro
    intro  x
    have ind_left : ∀a₀: a.1, Acc (a.add_rel b) (Sum.inl a₀) := by
      intro a₀
      induction a₀ using a.wo.wf.induction with | h a₀ ih =>
      apply Acc.intro
      intro y r
      cases y with
      | inl y =>
        apply ih
        cases r
        assumption
      | inr y => contradiction
    cases x with
    | inl a₀ => apply ind_left
    | inr b₀ =>
      induction b₀ using b.wo.wf.induction with | h b₀ ih =>
      apply Acc.intro
      intro y r
      cases y with
      | inr y =>
        apply ih
        cases r
        assumption
      | inl y =>
        clear r
        apply ind_left
  · intro x y
    cases x <;> cases y <;> rename_i x y
    · cases a.wo.tri x y <;> rename_i h
      apply Or.inl
      apply Sum.Lex.inl
      exact h
      apply Or.inr
      cases h <;> rename_i h
      apply Or.inl
      congr
      apply Or.inr
      apply Sum.Lex.inl
      exact h
    · apply Or.inl
      apply Sum.Lex.inl_inr
    · apply Or.inr
      apply Or.inr
      apply Sum.Lex.inl_inr
    · cases b.wo.tri x y <;> rename_i h
      apply Or.inl
      apply Sum.Lex.inr
      exact h
      apply Or.inr
      cases h <;> rename_i h
      apply Or.inl
      congr
      apply Or.inr
      apply Sum.Lex.inr
      exact h
  · intro x y z xy yz
    cases xy <;> cases yz
    apply Sum.Lex.inl
    apply a.wo.trans <;> assumption
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inr
    apply b.wo.trans <;> assumption

def WellOrder.add_congr : ∀a b c d: WellOrder, Equiv a c -> Equiv b d -> Equiv (a.add b) (c.add d) := by
  intro a b c d ac bd
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · intro x
    cases x <;> rename_i x
    apply Sum.inl (ac.left x)
    apply Sum.inr (bd.left x)
  · intro x
    cases x <;> rename_i x
    apply Sum.inl (ac.right x)
    apply Sum.inr (bd.right x)
  · intro x
    cases x <;> dsimp
    rw [ac.right_left]
    rw [bd.right_left]
  · intro x
    cases x <;> dsimp
    rw [ac.left_right]
    rw [bd.left_right]
  · intro x y r
    cases r <;> dsimp
    apply Sum.Lex.inl
    apply ac.left_resp
    assumption
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inr
    apply bd.left_resp
    assumption
  · intro x y r
    cases r <;> dsimp
    apply Sum.Lex.inl
    apply ac.right_resp
    assumption
    apply Sum.Lex.inl_inr
    apply Sum.Lex.inr
    apply bd.right_resp
    assumption

def Ordinal.add (a b: Ordinal) : Ordinal := by
  apply lift₂ (fun a b => mk (WellOrder.add a b)) _ a b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound'
  apply WellOrder.add_congr <;> assumption

instance : HAdd Ordinal Ordinal Ordinal := ⟨ Ordinal.add ⟩

def WellOrder.mul_rel (a b: WellOrder) : a.ty × b.ty -> a.ty × b.ty -> Prop := Prod.Lex a.rel b.rel

def WellOrder.mul (a b: WellOrder) : WellOrder := by
  apply WellOrder.mk _ (mul_rel b a) _
  apply IsWellOrder.mk
  · exact ⟨fun (b₀, a₀) => Prod.lexAccessible (WellFounded.apply b.wo.wf b₀) (WellFounded.apply a.wo.wf) a₀⟩
  · rintro ⟨xl,xr⟩ ⟨yl,yr⟩
    cases b.wo.tri xl yl <;> rename_i h
    apply Or.inl
    apply Prod.Lex.left
    assumption
    cases h
    subst yl
    cases a.wo.tri xr yr <;> rename_i h
    apply Or.inl
    apply Prod.Lex.right
    assumption
    cases h
    subst yr
    apply Or.inr
    apply Or.inl
    rfl
    apply Or.inr
    apply Or.inr
    apply Prod.Lex.right
    assumption
    apply Or.inr
    apply Or.inr
    apply Prod.Lex.left
    assumption
  · intro x y z xy yz
    cases xy <;> cases yz
    apply Prod.Lex.left
    apply b.wo.trans <;> assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.right
    apply a.wo.trans <;> assumption

def WellOrder.mul_congr : ∀a b c d: WellOrder, Equiv a c -> Equiv b d -> Equiv (a.mul b) (c.mul d) := by
  intro a b c d ac bd
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · rintro ⟨ b₀, a₀ ⟩
    exact ⟨ bd.left b₀, ac.left a₀ ⟩
  · rintro ⟨ d₀, c₀ ⟩
    exact ⟨ bd.right d₀, ac.right c₀ ⟩
  · rintro ⟨ d₀, c₀ ⟩
    dsimp
    rw [ac.right_left, bd.right_left]
  · rintro ⟨ c₀, d₀ ⟩
    dsimp
    rw [ac.left_right, bd.left_right]
  · rintro ⟨ xl, xr ⟩ ⟨ yl, yr ⟩ r
    dsimp
    cases r <;> rename_i r
    apply Prod.Lex.left
    apply bd.left_resp
    assumption
    apply Prod.Lex.right
    apply ac.left_resp
    assumption
  · rintro ⟨ xl, xr ⟩ ⟨ yl, yr ⟩ r
    dsimp
    cases r <;> rename_i r
    apply Prod.Lex.left
    apply bd.right_resp
    assumption
    apply Prod.Lex.right
    apply ac.right_resp
    assumption

def Ordinal.mul (a b: Ordinal) : Ordinal := by
  apply lift₂ (fun a b => mk (WellOrder.mul a b)) _ a b
  clear a b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound'
  apply WellOrder.mul_congr <;> assumption

instance : HMul Ordinal Ordinal Ordinal := ⟨ Ordinal.mul ⟩

def Ordinal.zero_eq_ulift_empty : 0 = ulift empty := by
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  apply WellOrder.Equiv.mk
  exact fun x => x.elim
  exact fun x => x.elim0
  exact fun x => x.elim0
  exact fun x => x.elim
  exact fun x => x.elim0
  exact fun x => x.elim

def Ordinal.one_eq_ulift_unit : 1 = ulift unit := by
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  apply WellOrder.Equiv.mk (fun _ => ⟨⟩) (fun _ => 0)
  intro; rfl
  intro x; apply Subsingleton.allEq
  intro ⟨x,xLt⟩ ⟨y,yLt⟩ h
  cases x <;> cases y <;> contradiction
  intros; contradiction

def Ordinal.two_eq_ulift_bool : 2 = ulift bool := by
  apply sound'
  apply WellOrder.ulift_equiv_ulift
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  intro ⟨x,xLt⟩
  match x with
  | 0 => exact false
  | 1 => exact true
  intro b
  match b with
  | false => exact 0
  | true => exact 1
  intro b
  cases b <;> rfl
  intro ⟨x,xLt⟩
  match x with
  | 0 => rfl
  | 1 => rfl
  intro x y lt
  match x, y with
  | 0, 1 => rfl
  | 0, 0 | 1, 0 | 1, 1 => contradiction
  intro x y lt
  cases x <;> cases y <;> trivial

def Ordinal.zero_eq_empty : 0 = empty := by
  rw [zero_eq_ulift_empty, ulift_eq_self]

def Ordinal.one_eq_unit : 1 = unit := by
  rw [one_eq_ulift_unit, ulift_eq_self]

def Ordinal.two_eq_unit : 2 = bool := by
  rw [two_eq_ulift_bool, ulift_eq_self]

def Ordinal.ulift_add.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : ulift.{u,w} a + b = ulift.{max u v,w} (a + b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.add_congr a.ulift b a b
  exact a.ulift_equiv_self
  rfl
  rfl

def Ordinal.add_ulift.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : a + ulift.{v,w} b = ulift.{max u v,w} (a + b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.add_congr a b.ulift a b
  rfl
  exact b.ulift_equiv_self
  rfl

def Ordinal.ulift_mul.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : ulift.{u,w} a * b = ulift.{max u v,w} (a * b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.mul_congr a.ulift b a b
  exact a.ulift_equiv_self
  rfl
  rfl

def Ordinal.mul_ulift.{u,v,w} (a: Ordinal.{u}) (b: Ordinal.{v}) : a * ulift.{v,w} b = ulift.{max u v,w} (a * b) := by
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply sound'
  apply WellOrder.ulift_equiv_right
  apply WellOrder.Equiv.trans
  apply WellOrder.mul_congr a b.ulift a b
  rfl
  exact b.ulift_equiv_self
  rfl

def Ordinal.zero_add (a: Ordinal) : 0 + a = a := by
  rw [zero_eq_ulift_empty]
  rw [ulift_add]
  induction a using ind with | mk a =>
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.add
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x
  cases x; contradiction
  assumption
  intro x
  exact Sum.inr x
  intro x; rfl
  intro x; cases x; contradiction; rfl
  intro x y r
  cases x; contradiction
  cases y; contradiction
  cases r
  assumption
  intro x y r
  apply Sum.Lex.inr
  assumption

def Ordinal.add_zero (a: Ordinal) : a + 0 = a := by
  rw [zero_eq_ulift_empty]
  rw [add_ulift]
  induction a using ind with | mk a =>
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.add
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x
  cases x; assumption; contradiction
  intro x
  exact Sum.inl x
  intro x; rfl
  intro x; cases x; rfl; contradiction
  intro x y r
  cases x
  cases y
  cases r
  assumption
  repeat contradiction
  intro x y r
  apply Sum.Lex.inl
  assumption

def Ordinal.one_mul (a: Ordinal) : 1 * a = a := by
  rw [one_eq_ulift_unit]
  rw [ulift_mul]
  induction a using ind with | mk a =>
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.mul WellOrder.mul_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x; exact x.1
  intro x; exact ⟨x, ⟨⟩⟩
  intros; rfl
  intros; rfl
  intro x y r
  cases r; assumption; contradiction
  intro x y r
  apply Prod.Lex.left; assumption

def Ordinal.mul_one (a: Ordinal) : a * 1 = a := by
  rw [one_eq_ulift_unit]
  rw [mul_ulift]
  induction a using ind with | mk a =>
  apply sound'
  apply WellOrder.ulift_equiv_left
  unfold WellOrder.mul WellOrder.mul_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  intro x; exact x.2
  intro x; exact ⟨⟨⟩, x⟩
  intros; rfl
  intros; rfl
  intro x y r
  cases r; contradiction; assumption
  intro x y r
  apply Prod.Lex.right; assumption

def Ordinal.two_mul (a: Ordinal) : a * 2 = a + a := by
  rw [two_eq_ulift_bool]
  induction a using ind with | mk a =>
  apply sound'
  apply WellOrder.Equiv.trans
  apply WellOrder.mul_congr
  rfl
  apply WellOrder.ulift_equiv_self
  unfold WellOrder.mul WellOrder.mul_rel WellOrder.add WellOrder.add_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _ <;> dsimp
  rintro ⟨b,x⟩
  cases b
  exact .inl x
  exact .inr x
  intro x
  cases x <;> rename_i x
  exact ⟨false,x⟩
  exact ⟨true,x⟩
  intro x
  cases x <;> rfl
  intro ⟨b,x⟩
  cases b <;> rfl
  intro ⟨b₀,x₀⟩ ⟨b₁,x₁⟩ r
  cases b₀ <;> cases b₁ <;> dsimp
  any_goals contradiction
  cases r; contradiction
  apply Sum.Lex.inl; assumption
  apply Sum.Lex.inl_inr
  cases r; contradiction
  apply Sum.Lex.inr; assumption
  intro x y r
  cases r <;> dsimp
  any_goals apply Prod.Lex.right; assumption
  apply Prod.Lex.left; trivial

def Ordinal.omega_mul_fin (n: Nat) : ofNat (n+1) * omega = omega := by
  apply sound'
  unfold WellOrder.mul WellOrder.mul_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · intro ⟨x,y⟩
    exact x * n.succ + y
  · intro x
    exact ⟨x/n.succ,Fin.ofNat x⟩
  · intro x
    dsimp
    rw [Fin.ofNat]
    dsimp
    rw [Nat.mul_comm]
    apply Nat.div_add_mod
  · intro ⟨x,y,yLt⟩
    dsimp
    congr
    rw [Nat.div_eq_of_lt_le]
    apply Nat.le_add_right
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left yLt (x * (n + 1))
    rw [Fin.ofNat]
    congr
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
    assumption
  · intro ⟨x₀,x₁⟩ ⟨y₀,y₁⟩ r
    dsimp
    cases r
    apply Nat.lt_of_lt_of_le
    apply Nat.add_lt_add_left
    exact x₁.isLt
    rw [←Nat.succ_mul, ←Nat.add_zero (x₀.succ * _)]
    apply Nat.add_le_add
    apply Nat.mul_le_mul_right
    apply Nat.succ_le_of_lt
    assumption
    apply Nat.zero_le
    apply Nat.add_lt_add_left
    assumption
  · intro x y x_lt_y
    cases Nat.decLt (x / n.succ) (y / n.succ) <;> rename_i r
    replace r := Nat.le_of_not_lt r
    have : x / n.succ ≤ y / n.succ := by
      refine (Nat.le_div_iff_mul_le ?k0).mpr ?_
      apply Nat.zero_lt_succ
      rw [Nat.mul_comm]
      apply Nat.le_trans
      apply Nat.le_add_right
      exact x % n.succ
      rw [Nat.div_add_mod]
      apply Nat.le_of_lt
      assumption
    have := Nat.le_antisymm this r
    rw [this]
    apply Prod.Lex.right
    rw [←Nat.div_add_mod x n.succ, ←Nat.div_add_mod y n.succ] at x_lt_y
    rw [this] at x_lt_y
    exact Nat.lt_of_add_lt_add_left x_lt_y
    apply Prod.Lex.left
    assumption

def Ordinal.omega_add_fin (n: Nat) : ofNat n + omega = omega := by
  apply sound'
  unfold WellOrder.add WellOrder.add_rel
  dsimp
  apply WellOrder.Equiv.mk _ _ _ _ _ _
  · intro x
    match x with
    | .inl x => exact x.val
    | .inr x => exact x + n
  · intro x
    match Nat.decLt x n with
    | .isTrue h => exact .inl ⟨ x, h ⟩
    | .isFalse _ => exact .inr (x - n)
  · intro x
    cases Nat.decLt x n
    dsimp
    rw [Nat.sub_add_cancel]
    apply Nat.le_of_not_lt
    assumption
    rfl
  · intro x
    cases x <;> (rename_i x; dsimp)
    split
    rfl
    have := x.isLt
    contradiction
    split
    have := Nat.not_lt_of_le (Nat.le_add_left n x)
    contradiction
    rw [Nat.add_sub_cancel]
  · intro x y r
    cases x <;> rename_i x <;> cases y <;> rename_i y <;> dsimp
    cases r
    assumption
    apply Nat.lt_of_lt_of_le x.isLt
    apply Nat.le_add_left
    cases r
    apply Nat.add_lt_add_right
    cases r
    assumption
  · intro x y x_lt_y
    split <;> split
    apply Sum.Lex.inl
    assumption
    apply Sum.Lex.inl_inr
    rename_i h₀ _ _ h₁ _
    have := Nat.lt_of_lt_of_le h₁ (Nat.le_of_not_lt h₀)
    have := Nat.lt_irrefl _ (Nat.lt_trans this x_lt_y)
    contradiction
    apply Sum.Lex.inr
    refine Nat.sub_lt_sub_right ?h_2.h_2.a.a x_lt_y
    apply Nat.le_of_not_lt
    assumption
