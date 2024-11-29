-- SAFETY: @Quot α r is represented exactly the same as α at runtime
-- so there is no problem with casting between them
unsafe def Quot.getRuntime : (f: @Quot α r -> α) ×' (∀x, mk _ (f x) = x) := ⟨cast lcProof, lcProof⟩
@[implemented_by Quot.getRuntime]
opaque Quot.getBuilder : (f: @Quot α r -> α) ×' (∀x, mk _ (f x) = x) :=
  ⟨(Classical.choose ·.exists_rep), (Classical.choose_spec ·.exists_rep)⟩

def Quot.unwrapQuot : @Quot α r -> α := Quot.getBuilder.fst
def Quot.mk_unwrapQuot : ∀q: Quot r, mk r q.unwrapQuot = q := Quot.getBuilder.snd
def Quotient.unwrapQuot : @Quotient α s -> α := Quot.unwrapQuot
def Quotient.mk_unwrapQuot : ∀q: Quotient s, Quotient.mk s q.unwrapQuot = q := Quot.mk_unwrapQuot
def Quotient.get_equiv {s: Setoid α} : ∀q: α, (Quotient.mk s q).unwrapQuot ≈ q := by
  intro q
  apply Quotient.exact
  rw [mk_unwrapQuot]

class QuotLike {α: outParam (Sort u)} (r: outParam (α -> α -> Prop)) (Q: Sort u) where
  mkQuotLike ::
  mk: α -> Q := by exact Quot.mk _
  unwrapQuot: Q -> α := by exact Quot.unwrapQuot
  mk_unwrapQuot: ∀q, mk (unwrapQuot q) = q := by exact Quot.mk_unwrapQuot
  ind: ∀{motive: Q -> Prop}, (mk: ∀x, motive (mk x)) -> ∀q, motive q := by exact Quot.ind
  sound: ∀x y, r x y -> mk x = mk y := by intros; apply Quot.sound; assumption

local notation "⟦" a "⟧" => QuotLike.mk a
def unwrapQuot [@QuotLike α r Q] : Q -> α := QuotLike.unwrapQuot
def mk_unwrapQuot [@QuotLike α r Q] (q: Q) : ⟦unwrapQuot q⟧ = q := QuotLike.mk_unwrapQuot q
def quot.ind [@QuotLike α r Q] : {motive: Q -> Prop} -> (mk: ∀x, motive (⟦x⟧)) -> ∀q, motive q := QuotLike.ind
def quot.sound' [@QuotLike α r Q] : r a b -> (⟦a⟧: Q) = ⟦b⟧ := QuotLike.sound _ _

class QuotientLike {α: outParam (Sort u)} (s: outParam (Setoid α)) (Q: Sort u) extends QuotLike s.r Q where
  mkQuotientLike ::
  exact : ∀{a b: α}, (⟦a⟧: Q) = ⟦b⟧ -> a ≈ b := by exact Quotient.exact

def quot.sound {s: Setoid α} [QuotientLike s Q] : a ≈ b -> (⟦a⟧: Q) = ⟦b⟧ := QuotLike.sound _ _
def quot.exact {s: Setoid α} [QuotientLike s Q] :(⟦a⟧: Q) = ⟦b⟧ -> a ≈ b := QuotientLike.exact
def quot.exact' {s: Setoid α} [QuotientLike s Q] : unwrapQuot (⟦a⟧: Q) ≈ a := by
  apply quot.exact (Q := Q)
  rw [mk_unwrapQuot]

def quot.lift' {r: α -> α -> Prop} [QuotLike r Q] (f: α -> β) : (∀x y, r x y -> f x = f y) -> Q -> β := fun _ q => f (QuotLike.unwrapQuot q)
def quot.lift {s: Setoid α} [QuotientLike s Q] (f: α -> β) : (∀x y, x ≈ y -> f x = f y) -> Q -> β := quot.lift' f
def quot.lift_mk [QuotientLike r Q] : lift f h (⟦a⟧: Q) = f a := by
  unfold lift
  apply h
  apply quot.exact (Q := Q)
  erw [mk_unwrapQuot]

def quot.lift₂
  [@QuotLike α₁ r₁ Q₁] [@QuotLike α₂ r₂ Q₂]
  {β: Sort v} (f: α₁ -> α₂ -> β)
  (_h: ∀a b c d, r₁ a c -> r₂ b d -> f a b = f c d)
  (q₁: Q₁) (q₂: Q₂) : β := f (unwrapQuot q₁) (unwrapQuot q₂)

def quot.lift₃
  [@QuotLike α₁ r₁ Q₁] [@QuotLike α₂ r₂ Q₂] [@QuotLike α₃ r₃ Q₃]
  {β: Sort v} (F: α₁ -> α₂ -> α₃ -> β)
  (_h: ∀a b c d e f, r₁ a d -> r₂ b e -> r₃ c f -> F a b c = F d e f)
  (q₁: Q₁) (q₂: Q₂) (q₃: Q₃) : β :=
  F (unwrapQuot q₁) (unwrapQuot q₂) (unwrapQuot q₃)

def quot.lift₂_mk [QuotientLike s₁ Q₁] [QuotientLike s₂ Q₂] :
  lift₂ f h (⟦a⟧: Q₁) (⟦b⟧: Q₂) = f a b := by
  apply h <;> apply quot.exact'

def quot.lift₃_mk [QuotientLike s₁ Q₁] [QuotientLike s₂ Q₂] [QuotientLike s₃ Q₃] :
  lift₃ f h (⟦a⟧: Q₁) (⟦b⟧: Q₂) (⟦c⟧: Q₃) = f a b c := by
  apply h <;> apply quot.exact'

instance : QuotLike r (Quot r) where
instance : QuotLike (fun _ _: α => True) (Squash α) where

def quot.liftProp [@QuotLike α r Q] : (f: α -> Prop) -> (∀a b, r a b -> (f a -> f b)) -> Q -> Prop := fun f _ x => f (unwrapQuot x)
def quot.liftProp_mk [@QuotientLike α r Q] : liftProp f h (⟦a⟧: Q) ↔ f a := by
  apply Iff.intro
  apply h <;> apply quot.exact'
  apply h <;> (
    apply Setoid.iseqv.symm
    apply quot.exact')

def quot.liftProp₂
  [@QuotLike α₁ r₁ Q₁] [@QuotLike α₂ r₂ Q₂]
  : (f: α₁ -> α₂ -> Prop) -> (∀a b c d, r₁ a c -> r₂ b d -> (f a b -> f c d)) -> Q₁ -> Q₂ -> Prop := fun f _ x y => f (unwrapQuot x) (unwrapQuot y)
def quot.liftProp₂_mk [QuotientLike s₁ Q₁] [QuotientLike s₂ Q₂] : liftProp₂ f h (⟦a⟧: Q₁) (⟦b⟧: Q₂)  ↔ f a b := by
  apply Iff.intro
  apply h <;> apply quot.exact'
  apply h <;> (
    apply Setoid.iseqv.symm
    apply quot.exact')

def quot.liftProp₃
  [@QuotLike α₁ r₁ Q₁] [@QuotLike α₂ r₂ Q₂] [@QuotLike α₃ r₃ Q₃]
  : (F: α₁ -> α₂ -> α₃ -> Prop) -> (∀a b c d e f, r₁ a d -> r₂ b e -> r₃ c f -> (F a b c -> F d e f)) -> Q₁ -> Q₂ -> Q₃ -> Prop := fun f _ x y z => f (unwrapQuot x) (unwrapQuot y) (unwrapQuot z)
def quot.liftProp₃_mk [QuotientLike s₁ Q₁] [QuotientLike s₂ Q₂] [QuotientLike s₃ Q₃] :
  liftProp₃ f h (⟦a⟧: Q₁) (⟦b⟧: Q₂) (⟦c⟧: Q₃)  ↔ f a b c := by
  apply Iff.intro
  apply h <;> apply quot.exact'
  apply h <;> (
    apply Setoid.iseqv.symm
    apply quot.exact')

def quot.liftWith [QuotLike r Q] :
  {P: Q -> Prop} ->
  (f: ∀a, P ⟦a⟧ -> α) ->
  (∀a b, r a b -> (h₀: P ⟦a⟧) -> (h₁: P ⟦b⟧) -> f a h₀ = f b h₁) ->
  ∀a, P a -> α :=
  fun f _ r h => f (unwrapQuot r) <| by
    rw [mk_unwrapQuot]
    exact h
def quot.liftWith_mk [QuotientLike r Q] {P: Q -> Prop} {f: ∀a, P ⟦a⟧ -> α} {all_eq} {h: P ⟦a⟧} :
  liftWith f all_eq (⟦a⟧: Q) h = f a h := by
  apply all_eq
  apply quot.exact'
def quot.liftWith₂
  [QuotLike r₁ Q₁] [QuotLike r₂ Q₂]:
  {P: Q₁ -> Q₂ -> Prop} ->
  (f: ∀a b, P ⟦a⟧ ⟦b⟧ -> α) ->
  (∀a b c d, r₁ a c -> r₂ b d ->
    (h₀: P ⟦a⟧ ⟦b⟧) ->
    (h₁: P ⟦c⟧ ⟦d⟧) -> f a b h₀ = f c d h₁) ->
   ∀a b, P a b -> α :=
  fun f _ r₀ r₁ h => f (unwrapQuot r₀) (unwrapQuot r₁) <| by
    rw [mk_unwrapQuot, mk_unwrapQuot]
    exact h
def quot.liftWith₂_mk
  [QuotientLike r₁ Q₁] [QuotientLike r₂ Q₂]
  {P: Q₁ -> Q₂ -> Prop} {f: ∀a b, P ⟦a⟧ ⟦b⟧ -> α} {all_eq} {h: P ⟦a⟧ ⟦b⟧}:
  liftWith₂ f all_eq (⟦a⟧: Q₁) (⟦b⟧: Q₂) h = f a b h := by
  apply all_eq <;> apply quot.exact'
