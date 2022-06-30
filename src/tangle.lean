import allowable
import mathlib.option

noncomputable theory

open cardinal cardinal.is_regular equiv equiv.perm function set with_bot
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open params

/-

/-- A pretangle has a preferred extension, which is either a proper type `β : Λ`,
or the base type `-1`. A pretangle has a `-1`-extension if and only if its preferred extension
is the `-1`-extension. -/
inductive preferred_extension (α : Λ) : Type u
| proper_extension : Π (β < α), preferred_extension
| base_extension : set atom → preferred_extension

/-- A *pretangle* is an object that may become a *tangle*,
an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def pretangle : Λ → Type u
| α := set atom × Π β < α, set (pretangle β)
using_well_founded { dec_tac := `[assumption] }

namespace pretangle

/-- Obtains the members of a pretangle of type `α`, seen as a set of atoms. -/
def atom_members {α : Λ} (a : pretangle α) : set atom :=
by { unfold pretangle at a, exact a.fst }

/-- Obtains the members of a pretangle of type `α`, seen as a set of elements of type `β < α`. -/
def members {α : Λ} (a : pretangle α) : Π (β < α), set (pretangle β) :=
by { unfold pretangle at a, exact a.snd }

/-- The membership relation defined on pretangles for atoms. -/
instance has_mem_atom {α : Λ} : has_mem atom (pretangle α) :=
⟨λ b a, b ∈ a.atom_members⟩

-- Yaël: Note, this instance is useless as it won't fire because `β < α` is not a class
/-- The membership relation defined on pretangles.
This is exactly the membership relation on tangles, without the extensionality condition that
allows this membership relation to be used in a model of TTT. -/
instance has_mem {α β : Λ} (h : β < α) : has_mem (pretangle β) (pretangle α) :=
⟨λ b a, b ∈ a.members β h⟩

end pretangle

-/

variables (α : Λ) [phase_1a.{u} α]

abbreviation semitangle_members :=
Π β (hβ : β < α), {s : set (tangle α β $ coe_lt_coe.mpr hβ) // s.nonempty}

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
inductive semitangle_extension (members : semitangle_members α)
| proper (β : Λ) (hβ : β < α) :
    let c : code α α le_rfl := ⟨β, coe_lt_coe.mpr hβ, members β hβ⟩
    in c.is_representative →
      (∀ γ (hγ : γ < α) (hβγ : β ≠ γ),
        A_map_code hγ ⟨c, (members β hβ).property⟩
        = ⟨⟨γ, coe_lt_coe.mpr hγ, members γ hγ⟩, (members γ hγ).property⟩)
      → semitangle_extension
| base (atoms : set atom) (hne : atoms.nonempty) :
    let c : code α α le_rfl := ⟨⊥, bot_lt_coe _, atoms⟩
    in c.is_representative →
      (∀ γ (hγ : γ < α),
        A_map_code hγ ⟨c, hne⟩ = ⟨⟨γ, coe_lt_coe.mpr hγ, members γ hγ⟩, (members γ hγ).property⟩)
      → semitangle_extension

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`.

Here, we restrict our definition to just nonempty semitangles; this simplifies the definition. -/
structure nonempty_semitangle :=
(members : semitangle_members α)
(extension : semitangle_extension α members)

namespace nonempty_semitangle

def mem {β : Λ} (hβ : β < α)
  (t : tangle α β (coe_lt_coe.mpr hβ)) (s : nonempty_semitangle α) := t ∈ (s.members β hβ).val

def representative_code : nonempty_semitangle α → code α α le_rfl
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ := ⟨β, coe_lt_coe.mpr hβ, members β hβ⟩
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ := ⟨⊥, bot_lt_coe _, atoms⟩

lemma representative_code_spec :
  Π (s : nonempty_semitangle α), (representative_code α s).is_representative
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ := rep
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ := rep

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
lemma ext_core (x y : nonempty_semitangle α) : (∃ γ, γ < α) → x.members = y.members → x = y :=
begin
  obtain ⟨xs, hxs⟩ := x, obtain ⟨ys, hys⟩ := y, dsimp,
  intros ex_γ h, subst h, refine congr_arg (λ h, ⟨xs, h⟩) _,
  cases hxs with β hβ rep₁ hA₁ atoms₁ hne rep₁ hA₁;
  cases hys with γ hγ rep₂ hA₂ atoms₂ hne rep₂ hA₂,
  { simp,
    by_contradiction β_ne_γ,
    refine code.is_representative.A_map
      ⟨⟨β, coe_lt_coe.mpr hβ, (xs β hβ).val⟩, (xs β hβ).property⟩
      ⟨⟨γ, coe_lt_coe.mpr hγ, (xs γ hγ).val⟩, (xs γ hγ).property⟩
      rep₁ rep₂ hβ (ne.symm β_ne_γ ∘ coe_eq_coe.mp) _,
    symmetry,
    exact hA₂ _ _ (ne.symm β_ne_γ) },
  { exfalso,
    exact code.is_representative.A_map
      ⟨⟨β, coe_lt_coe.mpr hβ, (xs β hβ).val⟩, (xs β hβ).property⟩
      ⟨⟨⊥, bot_lt_coe _, atoms₂⟩, hne⟩
      rep₁ rep₂ hβ bot_ne_coe (hA₂ β hβ).symm },
  { exfalso,
    exact code.is_representative.A_map
      ⟨⟨γ, coe_lt_coe.mpr hγ, (xs γ hγ).val⟩, (xs γ hγ).property⟩
      ⟨⟨⊥, bot_lt_coe _, atoms₁⟩, hne⟩
      rep₂ rep₁ hγ bot_ne_coe (hA₁ γ hγ).symm },
  { simp, obtain ⟨γ, hγ⟩ := ex_γ, have h₁ := hA₁ γ hγ, have h₂ := hA₂ γ hγ, rw ← h₂ at h₁,
    have := A_map_code_injective hγ h₁, cases this, refl }
end

lemma ext (x y : nonempty_semitangle α) {β : Λ} (hβ : β < α) :
  x.members β hβ = y.members β hβ → x = y :=
begin
  intro h,
  obtain ⟨xs, hxs⟩ := x, obtain ⟨ys, hys⟩ := y, dsimp at h,
  refine ext_core α _ _ ⟨β, hβ⟩ _, dsimp,
  sorry
end

lemma ext' (x y : nonempty_semitangle α) {β : Λ} (hβ : β < α) :
  (∀ (t : tangle α β (coe_lt_coe.mpr hβ)), mem α hβ t x ↔ mem α hβ t y) → x = y :=
by { intro h, refine ext α x y hβ _, ext t, exact h t }

end nonempty_semitangle

/-- A semitangle is either a nonempty semitangle, or the `⊥` element, which is considered the empty
set. Note that in TTT, a set contains no elements at one level if and only if it contains no
elements at all levels. -/
@[reducible] def semitangle := with_bot (nonempty_semitangle α)

/-- The membership relation of tangles and semitangles in TTT at this level. -/
def semitangle.mem {β : Λ} (hβ : β < α)
  (t : tangle α β (coe_lt_coe.mpr hβ)) (s : semitangle α) :=
  s.elim false (nonempty_semitangle.mem α hβ t)

@[simp] lemma semitangle.mem_bot {β : Λ} (hβ : β < α)
  (t : tangle α β (coe_lt_coe.mpr hβ)) : semitangle.mem α hβ t ⊥ = false := rfl

@[simp] lemma semitangle.mem_none {β : Λ} (hβ : β < α)
  (t : tangle α β (coe_lt_coe.mpr hβ)) : semitangle.mem α hβ t none = false := rfl

lemma semitangle.eq_bot_of_forall_not_mem {β : Λ} (hβ : β < α) (s : semitangle α) :
  (∀ (t : tangle α β (coe_lt_coe.mpr hβ)), ¬ semitangle.mem α hβ t s) → s = ⊥ := sorry

lemma semitangle.ext (x y : semitangle α) {β : Λ} (hβ : β < α) :
  (∀ (t : tangle α β (coe_lt_coe.mpr hβ)),
    semitangle.mem α hβ t x ↔ semitangle.mem α hβ t y) → x = y :=
begin
  intro h, cases x,
  { symmetry, simp at h, refine semitangle.eq_bot_of_forall_not_mem α hβ y h },
  cases y,
  { simp at h, refine semitangle.eq_bot_of_forall_not_mem α hβ x h },
  rw nonempty_semitangle.ext' α x y hβ _, intro t, exact h t
end

def semitangle_members_of_nonempty_code (c : nonempty_code α α le_rfl)
  {β : Λ} (hβ : c.val.extension = β) : semitangle_members α :=
λ γ hγ, dite (β = γ)
    (λ heq, ⟨cast (by simp_rw [hβ, heq]) c.val.elts, by { convert c.property, rw [hβ, heq], simp }⟩)
    (λ hne, A_map c.val.extension_lt hγ ⟨c.val.elts, c.property⟩)

@[simp] lemma semitangle_members_eq (c : nonempty_code α α le_rfl)
  {β : Λ} (hβ : c.val.extension = β) :
  (⟨β, (hβ ▸ c.val.extension_lt : (β : type_index) < α),
    (semitangle_members_of_nonempty_code α c hβ β
      (coe_lt_coe.mp $ hβ ▸ c.val.extension_lt : β < α))⟩ : code α α le_rfl) = c.val :=
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c, dsimp at hβ, subst hβ,
  unfold semitangle_members_of_nonempty_code,
  rw dif_pos rfl, refl
end

@[simp] lemma semitangle_members_ne (c : nonempty_code α α le_rfl)
  {β : Λ} (hβ : c.val.extension = β) {γ : Λ} (hγ : γ < α) (hβγ : β ≠ γ) :
  (⟨γ, coe_lt_coe.mpr hγ, semitangle_members_of_nonempty_code α c hβ γ hγ⟩ : code α α le_rfl) =
  A_map_code hγ c :=
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c, dsimp at hβ, subst hβ,
  unfold semitangle_members_of_nonempty_code,
  rw dif_neg hβγ, refl
end

/-- We can construct nonempty semitangles from nonempty representative codes with extensions at
proper type indices. -/
def intro_nonempty_semitangle_proper (c : nonempty_code α α le_rfl)
  (heven : even $ height c) {β : Λ} (hβ : c.val.extension = β) : nonempty_semitangle α :=
⟨semitangle_members_of_nonempty_code α c hβ,
semitangle_extension.proper β (coe_lt_coe.mp $ hβ ▸ c.val.extension_lt : β < α)
(by { convert code.is_representative.nonempty c heven, rw semitangle_members_eq, refl })
(λ γ hγ hβγ, by { simp_rw [semitangle_members_ne α c hβ hγ hβγ, semitangle_members_eq], refl })⟩

def semitangle_members_of_nonempty_code_base (c : nonempty_code α α le_rfl)
  (hc : c.val.extension = ⊥) : semitangle_members α :=
λ γ hγ, A_map (bot_lt_coe _) hγ
  ⟨cast (by simp_rw hc) c.val.elts, by { convert c.property, rw hc, simp }⟩

@[simp] lemma semitangle_members_base (c : nonempty_code α α le_rfl)
  (hc : c.val.extension = ⊥) {β : Λ} (hβ : β < α) :
  (⟨β, coe_lt_coe.mpr hβ, semitangle_members_of_nonempty_code_base α c hc β hβ⟩ : code α α le_rfl) =
  A_map_code hβ c :=
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c, dsimp at hc, subst hc,
  unfold semitangle_members_of_nonempty_code_base, simp
end

def intro_nonempty_semitangle_base (c : nonempty_code α α le_rfl)
  (hc : c.val.extension = ⊥) : nonempty_semitangle α :=
⟨semitangle_members_of_nonempty_code_base α c hc,
semitangle_extension.base (cast (by { simp_rw hc, refl }) c.val.elts)
(by { convert c.property, simp_rw hc, refl, simp })
begin
  convert code.is_representative.nonempty c (by { convert even_zero, exact height_base c hc }),
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c, dsimp at hc, subst hc, refl
end
(λ β hβ, begin
  simp_rw semitangle_members_base α c hc hβ,
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c, dsimp at hc, subst hc, refl
end)⟩

variable [phase_1b.{u u} α]

/-- Allowable permutations act on nonempty semitangles. -/
instance nonempty_semitangle.mul_action :
  mul_action (allowable_perm α le_rfl) (nonempty_semitangle α) := sorry

/-- Allowable permutations act on semitangles. -/
instance semitangle.mul_action : mul_action (allowable_perm α le_rfl) (semitangle α) :=
option.mul_action

/-- A tangle at the new level `α` is a symmetric semitangle. This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def new_tangle :=
{s : semitangle α // symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) s}

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
lemma supportedness_equiv {c d : code α α le_rfl} (hcd : c ≡ d) (S : set (support_condition α))
(hS : supports (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) c S) :
  supports (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) d S := sorry

/-- By the previous lemma, if two codes are equivalent,
one is symmetric if and only if the other is. -/
lemma symmetric_equiv {c d : code α α le_rfl} (hcd : c ≡ d) :
  symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) c ↔
  symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) d := sorry

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def typed_near_litter (N : near_litter) : new_tangle α :=
⟨some $ intro_nonempty_semitangle_base α ⟨⟨⊥, bot_lt_coe _, N.snd.val⟩, sorry⟩ rfl, sorry⟩

/-- For any symmetric tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def symmetric_singleton {β : Λ} (hβ : β < α) (x : tangle α β (coe_lt_coe.mpr hβ))
  (symm : symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) x) : new_tangle α :=
⟨some $ intro_nonempty_semitangle_proper α ⟨⟨β, coe_lt_coe.mpr hβ, {x}⟩, set.singleton_nonempty _⟩
  (by { convert even_zero, exact height_singleton x }) rfl,
  sorry⟩

/-- For any small set `B` of symmetric `β`-tangles, the code `(α, β, B)` is a tangle at level `α`. -/
def symmetric_set {β : Λ} (hβ : β < α) (B : set $ tangle α β (coe_lt_coe.mpr hβ))
  (hne : B.nonempty) (hsmall : small B)
  (symm : ∀ b ∈ B, symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) b) :
  new_tangle α :=
⟨some $ intro_nonempty_semitangle_proper α ⟨⟨β, coe_lt_coe.mpr hβ, B⟩, hne⟩
  sorry rfl,
  sorry⟩

/-- Allowable permutations act on `α`-tangles. -/
instance new_tangle.has_scalar : has_scalar (allowable_perm α le_rfl) (new_tangle α) :=
⟨λ π t, ⟨π • t.val, sorry⟩⟩

instance new_tangle.mul_action : mul_action (allowable_perm α le_rfl) (new_tangle α) :=
sorry

end con_nf
