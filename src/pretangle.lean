import mathlib.equiv
import mathlib.order
import params

noncomputable theory

open cardinal cardinal.is_regular equiv equiv.perm function set
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open params

/-- Either the base type or a proper type index (an element of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def type_index := with_bot Λ

/-- Since `Λ` is well-ordered, so is `Λ` together with the base type `⊥`.
This allows well founded recursion on type indices.
TODO(zeramorphic): This proof is rather arduous, is there an easier solution? -/
instance : is_well_order type_index (<) := begin
  split,
  rw well_founded.well_founded_iff_has_min',
  intros p hp,
  have := well_founded.well_founded_iff_has_min'.mp Λwf.2,
  let p' : set Λ := ⋃ (x ∈ p), option.elim ∅ singleton x,
  by_cases h : p'.nonempty,
  { obtain ⟨m, ⟨i, hi₁, hi₂⟩, hm⟩ := this p' h, clear this,
    simp at hi₁,
    obtain ⟨y, hy⟩ := hi₁,
    rw ← hy at hi₂, clear hy,
    simp at hi₂,
    obtain ⟨hy₁, hy₂⟩ := hi₂,
    cases y; simp at hy₂,
    { contradiction },
    by_cases hbot : ⊥ ∈ p,
    { refine ⟨⊥, hbot, _⟩, intros x hx₁ hx₂,
      simp at hx₂, exact hx₂ },
    rw hy₂ at *, clear hy₂, clear m,
    refine ⟨↑y, _, _⟩,
    { exact hy₁ },
    { intros x hx₁ hx₂,
      cases x,
      { exfalso, exact hbot hx₁ },
      { rw option.coe_def,
        rw hm x _ _,
        { simp, refine ⟨some x, hx₁, _⟩, simp },
        { rw option.coe_def at hx₂, simp at hx₂, exact hx₂ } } } },
  { simp at h,
    simp_rw ← set.ne_empty_iff_nonempty at h,
    push_neg at h,
    have : ∀ x ∈ p, x = ⊥,
    { intros x hx, have := h x hx, cases x,
      { refl },
      { dsimp at this, exfalso,
        exact (set.nonempty.ne_empty (set.singleton_nonempty x)) this_1 } },
    have : p = {⊥},
    { ext, split; intro hx,
      { simp, exact this x hx },
      { simp at hx,
        obtain ⟨t, ht⟩ := hp,
        have := this t ht,
        rw [this, ← hx] at ht,
        exact ht } },
    refine ⟨⊥, _, _⟩,
    { rw this, simp },
    { intros x hx₁ hx₂,
      simp at hx₂, exact hx₂ } }
end
instance : linear_order type_index := linear_order_of_STO' (<)
instance : has_well_founded type_index := is_well_order.to_has_well_founded

/-- A pretangle has a preferred extension, which is either a proper type `β : Λ`,
or the base type `-1`. A pretangle has a `-1`-extension if and only if its preferred extension
is the `-1`-extension. -/
inductive preferred_extension (α : Λ) : Type u
| proper_extension : Π (β < α), preferred_extension
| base_extension : set base_type → preferred_extension

/-- A *pretangle* is an object that may become a *tangle*,
an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def pretangle : Λ → Type u
| α :=
    (Π β < α, set (pretangle β)) ×
    (preferred_extension α)
using_well_founded { dec_tac := `[assumption] }

namespace pretangle

/-- Obtains the members of a pretangle of type `α`, seen as a set of elements of type `β < α`. -/
def members {α : Λ} (a : pretangle α) : Π (β < α), set (pretangle β) :=
by { unfold pretangle at a, exact a.1 }

/-- The preferred extension of a pretangle. -/
def pref_extension {α : Λ} (a : pretangle α) : preferred_extension α :=
by { unfold pretangle at a, exact a.2 }

/-- The membership relation defined on pretangles.
This is exactly the membership relation on tangles, without the extensionality condition that
allows this membership relation to be used in a model of TTT. -/
instance has_mem {α β : Λ} (h : β < α) :
has_mem (pretangle β) (pretangle α) :=
⟨λ b a, b ∈ a.members β h⟩

end pretangle

end con_nf
