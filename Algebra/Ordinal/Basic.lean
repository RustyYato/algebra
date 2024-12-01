import Algebra.Relation.Basic
import Algebra.Equiv

namespace Ordinal

inductive Pre where
| intro {α: Type u} (r: α -> α -> Prop) (wo: Relation.IsWellOrder r)

inductive Pre.Equiv : Pre.{u} -> Pre.{u} -> Prop where
| intro : Relation.EmbedIso r s -> Equiv (.intro r rwo) (.intro s swo)

@[refl]
def Pre.Equiv.refl : ∀a, Pre.Equiv a a
| .intro _  _ => ⟨Relation.EmbedIso.refl _⟩

@[symm]
def Pre.Equiv.symm : Pre.Equiv a b -> Pre.Equiv b a
| .intro h => .intro h.symm

def Pre.Equiv.trans : Pre.Equiv a b -> Pre.Equiv b c -> Pre.Equiv a c
| .intro h, .intro g => .intro (h.trans g)

instance Pre.setoid : Setoid Pre where
  r a b := a.Equiv b
  iseqv := ⟨.refl, .symm, .trans⟩

@[refl]
def Pre.refl : ∀a: Pre, a ≈ a := Pre.Equiv.refl
@[symm]
def Pre.symm : Pre.Equiv a b -> Pre.Equiv b a := Pre.Equiv.symm
def Pre.trans : Pre.Equiv a b -> Pre.Equiv b c -> Pre.Equiv a c := Pre.Equiv.trans

def _root_.Ordinal := Equiv Pre.setoid
instance : QuotientLike Pre.setoid Ordinal := instQuotientLikeEquiv

local notation "⟦" a "⟧" => (QuotLike.mk (a: Pre): Ordinal)

end Ordinal
