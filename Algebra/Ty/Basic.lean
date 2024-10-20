import Algebra.Ty.Notation
import Algebra.Function.Basic

namespace Ty

structure Embed (α β: Sort*) where
  embed: α -> β
  embed_inj: Function.Injective embed

structure EmbedIso (α β: Sort*) where
  fwd: α -> β
  rev: β -> α
  fwd_rev: ∀x, rev (fwd x) = x
  rev_fwd: ∀x, fwd (rev x) = x

def EmbedIso.fwd_inj (e: EmbedIso α β) : Function.Injective e.fwd := by
  intro a b h
  rw [←e.fwd_rev a, ←e.fwd_rev b, h]
def EmbedIso.rev_inj (e: EmbedIso α β) : Function.Injective e.rev := by
  intro a b h
  rw [←e.rev_fwd a, ←e.rev_fwd b, h]
@[symm]
def EmbedIso.symm: EmbedIso α β -> EmbedIso β α
| .mk fwd rev fwd_rev rev_fwd => .mk rev fwd rev_fwd fwd_rev
def EmbedIso.trans: EmbedIso α β -> EmbedIso β γ -> EmbedIso α γ
| a, b => .mk (b.fwd ∘ a.fwd) (a.rev ∘ b.rev) (by
  intro x; dsimp
  rw [b.fwd_rev, a.fwd_rev]) (by
  intro x; dsimp
  rw [a.rev_fwd, b.rev_fwd])

def EmbedIso.fwdEmbed (e: EmbedIso α β) : Embed α β := .mk e.fwd e.fwd_inj
def EmbedIso.revEmbed (e: EmbedIso α β) : Embed β α := .mk e.rev e.rev_inj

@[refl]
def Embed.refl (α: Sort*) : Embed α α where
  embed := id
  embed_inj := id

@[refl]
def EmbedIso.refl (α: Sort*) : EmbedIso α α where
  fwd := id
  rev := id
  fwd_rev _ := rfl
  rev_fwd _ := rfl

instance : CoeFun (Embed α β) (fun _ => α -> β) := ⟨Embed.embed⟩

end Ty
