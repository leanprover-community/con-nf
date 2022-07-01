import allowable
import mathlib.option

noncomputable theory

open cardinal cardinal.is_regular equiv equiv.perm function set with_bot
open_locale cardinal pointwise

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

variables (α : Λ) [phase_1a.{u} α] {β γ : Λ} {hβ : β < α}

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

def mem (hβ : β < α) (t : tangle α β (coe_lt_coe.mpr hβ)) (s : nonempty_semitangle α) : Prop :=
t ∈ (s.members β hβ).val

def representative_code : nonempty_semitangle α → nonempty_code α α le_rfl
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ :=
  ⟨⟨β, coe_lt_coe.mpr hβ, members β hβ⟩, (members β hβ).property⟩
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ :=
  ⟨⟨⊥, bot_lt_coe _, atoms⟩, hne⟩

@[simp] lemma representative_code_proper_def (members : semitangle_members α) (β) (hβ) (rep) (hA) :
  representative_code α ⟨members, semitangle_extension.proper β hβ rep hA⟩ =
  ⟨⟨β, coe_lt_coe.mpr hβ, members β hβ⟩, (members β hβ).property⟩ := rfl

@[simp] lemma representative_code_base_def (members : semitangle_members α) (atoms) (hne) (rep) (hA) :
  representative_code α ⟨members, semitangle_extension.base atoms hne rep hA⟩ =
  ⟨⟨⊥, bot_lt_coe _, atoms⟩, hne⟩ := rfl

lemma representative_code_spec :
  Π (s : nonempty_semitangle α), (representative_code α s : code α α le_rfl).is_representative
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ := rep
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ := rep

lemma representative_code_members_eq :
  Π (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (representative_code α s : code α α le_rfl).extension = γ),
  s.members γ hγ =
    ⟨cast (by simp_rw hcγ) (representative_code α s : code α α le_rfl).elts,
    by { convert (representative_code α s).property, exact hcγ.symm, exact cast_heq _ _ }⟩
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ γ hγ hcγ :=
    by { rw representative_code_proper_def at hcγ, cases hcγ, dsimp, rw subtype.coe_eta }
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ γ hγ hcγ :=
    by { rw representative_code_base_def at hcγ, cases hcγ }

lemma representative_code_members_ne :
  Π (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (representative_code α s : code α α le_rfl).extension ≠ γ),
  A_map_code hγ (representative_code α s)
  = ⟨⟨γ, coe_lt_coe.mpr hγ, s.members γ hγ⟩, (s.members γ hγ).property⟩
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ γ hγ hcγ := hA _ _ (hcγ ∘ coe_eq_coe.mpr)
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ γ hγ hcγ := hA _ _

lemma representative_code_members_val (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (representative_code α s : code α α le_rfl).extension ≠ γ) :
  (s.members γ hγ).val = (A_map_code hγ (representative_code α s)).val.elts :=
begin
  have := congr_arg_heq code.elts (congr_arg subtype.val (representative_code_members_ne α s hγ hcγ)),
  rw heq_iff_eq at this, exact this.symm
end

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
lemma ext_core (x y : nonempty_semitangle α) : (∃ γ, γ < α) → x.members = y.members → x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp,
  rintro ex_γ rfl,
  refine congr_arg (λ h, ⟨xs, h⟩) _,
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
  { cases code.is_representative.A_map
      ⟨⟨β, coe_lt_coe.mpr hβ, (xs β hβ).val⟩, (xs β hβ).property⟩
      ⟨⟨⊥, bot_lt_coe _, atoms₂⟩, hne⟩
      rep₁ rep₂ hβ bot_ne_coe (hA₂ β hβ).symm },
  { cases code.is_representative.A_map
      ⟨⟨γ, coe_lt_coe.mpr hγ, (xs γ hγ).val⟩, (xs γ hγ).property⟩
      ⟨⟨⊥, bot_lt_coe _, atoms₁⟩, hne⟩
      rep₂ rep₁ hγ bot_ne_coe (hA₁ γ hγ).symm },
  { simp,
    obtain ⟨γ, hγ⟩ := ex_γ,
    have := A_map_code_injective hγ ((hA₁ γ hγ).trans (hA₂ γ hγ).symm), cases this, refl }
end

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their representative codes are equivalent (and hence equal, by uniqueness). -/
lemma ext_code (x y : nonempty_semitangle α) :
  ((representative_code α x : code α α le_rfl) ≡ representative_code α y) → x = y :=
begin
  intro h,
  have code_eq := code.is_representative.unique
    (representative_code_spec α x) (representative_code_spec α y) h,
  rw subtype.coe_inj at code_eq,
  by_cases ex_γ : ∃ γ, γ < α,
  { refine ext_core _ _ _ ex_γ _,
    refine funext _, intro γ, refine funext _, intro hγ, rw ← subtype.val_inj, dsimp only at ⊢,
    by_cases (representative_code α x : code α α le_rfl).extension = γ,
    { rw representative_code_members_eq α _ _ h,
      rw representative_code_members_eq α _ _ _,
      dsimp only, rw _root_.cast_eq_iff_heq, symmetry, convert cast_heq _ _ using 2,
      rw code_eq, rw code_eq, simp_rw h, rw ← code_eq, rw h },
    rw representative_code_members_val,
    rw representative_code_members_val,
    rw code_eq, rw ← code_eq, exact h, exact h },
  { obtain ⟨xs, hxs⟩ := x,
    obtain ⟨ys, hys⟩ := y,
    have : xs = ys,
    { refine funext _, intro γ, refine funext _, intro hγ, exfalso, exact ex_γ ⟨γ, hγ⟩ },
    subst this, congr,
    cases hxs with β hβ rep hA atoms₁ hne₁ rep₁ hA₁,
    { exfalso, exact ex_γ ⟨β, hβ⟩ },
    cases hys with β hβ rep hA atoms₂ hne₂ rep₂ hA₂,
    { exfalso, exact ex_γ ⟨β, hβ⟩ },
    rw [representative_code_base_def, representative_code_base_def] at code_eq,
    cases code_eq, refl }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext (x y : nonempty_semitangle α) (hβ : β < α) (h : x.members β hβ = y.members β hβ) :
  x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp only at h,
  refine ext_code α _ _ _,
  cases hxs with γ hγ rep₁ hA₁ atoms₁ hne₁ rep₁ hA₁;
  cases hys with δ hδ rep₂ hA₂ atoms₂ hne₂ rep₂ hA₂,
  { rw [representative_code_proper_def, representative_code_proper_def],
    by_cases hβγ : β = γ,
    { subst hβγ,
      by_cases hβδ : β = δ,
      { subst hβδ, convert code.equiv.refl _, exact h.symm },
      rw h, exact code.equiv.symm (code.equiv_A_map (hA₂ β hβ (ne.symm hβδ))
        (code.is_representative.even _ rep₂) (ne.symm hβδ ∘ coe_eq_coe.mp)) },
    by_cases hβδ : β = δ,
    { subst hβδ,
      rw ← h,
      exact code.equiv_A_map (hA₁ β hβ (ne.symm hβγ))
        (code.is_representative.even _ rep₁) (ne.symm hβγ ∘ coe_eq_coe.mp) },
    have h₁ := code.equiv_A_map (hA₁ β hβ (ne.symm hβγ))
      (code.is_representative.even _ rep₁) (ne.symm hβγ ∘ coe_eq_coe.mp),
    have h₂ := code.equiv_A_map (hA₂ β hβ (ne.symm hβδ))
      (code.is_representative.even _ rep₂) (ne.symm hβδ ∘ coe_eq_coe.mp),
    rw h at h₁, exact code.equiv_transitive h₁ h₂.symm },
  { rw [representative_code_proper_def, representative_code_base_def],
    by_cases hβγ : β = γ,
    { subst hβγ, rw h, exact code.equiv.symm (code.equiv_A_map (hA₂ β hβ) (by simp) (by simp)) },
    { have h₁ := code.equiv_A_map (hA₁ β hβ (ne.symm hβγ))
        (code.is_representative.even _ rep₁) (ne.symm hβγ ∘ coe_eq_coe.mp),
      have h₂ := code.equiv_A_map (hA₂ β hβ) (by simp) (by simp),
      rw h at h₁, exact code.equiv_transitive h₁ h₂.symm } },
  { rw [representative_code_proper_def, representative_code_base_def],
    by_cases hβδ : β = δ,
    { subst hβδ, rw ← h, exact code.equiv_A_map (hA₁ β hβ) (by simp) (by simp) },
    { have h₁ := code.equiv_A_map (hA₁ β hβ) (by simp) (by simp),
      have h₂ := code.equiv_A_map (hA₂ β hβ (ne.symm hβδ))
        (code.is_representative.even _ rep₂) (ne.symm hβδ ∘ coe_eq_coe.mp),
      rw h at h₁, exact code.equiv_transitive h₁ h₂.symm } },
  { rw [representative_code_base_def, representative_code_base_def],
    have h₁ := code.equiv_A_map (hA₁ β hβ) (by simp) (by simp),
    have h₂ := code.equiv_A_map (hA₂ β hβ) (by simp) (by simp),
    rw h at h₁, exact code.equiv_transitive h₁ h₂.symm }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext' (x y : nonempty_semitangle α) (hβ : β < α) (h : ∀ t, mem α hβ t x ↔ mem α hβ t y) :
  x = y :=
by { refine ext α x y hβ _, ext t, exact h t }

end nonempty_semitangle

/-- A semitangle is either a nonempty semitangle, or the `⊥` element, which is considered the empty
set. Note that in TTT, a set contains no elements at one level if and only if it contains no
elements at all levels. -/
@[reducible] def semitangle := with_bot (nonempty_semitangle α)

/-- The membership relation of tangles and semitangles in TTT at this level. -/
def semitangle.mem (hβ : β < α) (t : tangle α β (coe_lt_coe.2 hβ)) (s : semitangle α) :=
  s.elim false (nonempty_semitangle.mem α hβ t)

@[simp] lemma semitangle.mem_bot (hβ : β < α) (t : tangle α β (coe_lt_coe.mpr hβ)) :
  semitangle.mem α hβ t ⊥ = false := rfl

@[simp] lemma semitangle.mem_none (hβ : β < α) (t : tangle α β (coe_lt_coe.mpr hβ)) :
  semitangle.mem α hβ t none = false := rfl

lemma semitangle.eq_bot_of_forall_not_mem (hβ : β < α) (s : semitangle α) :
  (∀ t, ¬ semitangle.mem α hβ t s) → s = ⊥ := sorry

lemma semitangle.ext (x y : semitangle α) (hβ : β < α) :
  (∀ t, semitangle.mem α hβ t x ↔ semitangle.mem α hβ t y) → x = y :=
begin
  intro h, cases x,
  { symmetry, simp at h, refine semitangle.eq_bot_of_forall_not_mem α hβ y h },
  cases y,
  { simp at h, refine semitangle.eq_bot_of_forall_not_mem α hβ x h },
  rw nonempty_semitangle.ext' α x y hβ _, intro t, exact h t
end

def semitangle_members_of_nonempty_code (c : nonempty_code α α le_rfl) (hβ : c.val.extension = β) :
  semitangle_members α :=
λ γ hγ, dite (β = γ)
    (λ heq, ⟨cast (by simp_rw [hβ, heq]) c.val.elts, by { convert c.property, rw [hβ, heq], simp }⟩)
    (λ hne, A_map c.val.extension_lt hγ ⟨c.val.elts, c.property⟩)

@[simp] lemma semitangle_members_eq (c : nonempty_code α α le_rfl) (hβ : c.val.extension = β) :
  (⟨β, (hβ ▸ c.val.extension_lt : (β : type_index) < α),
    (semitangle_members_of_nonempty_code α c hβ β
      (coe_lt_coe.mp $ hβ ▸ c.val.extension_lt : β < α))⟩ : code α α le_rfl) = c.val :=
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c, dsimp at hβ, subst hβ,
  unfold semitangle_members_of_nonempty_code,
  rw dif_pos rfl, refl
end

@[simp] lemma semitangle_members_ne (c : nonempty_code α α le_rfl) (hβ : c.val.extension = β)
  (hγ : γ < α) (hβγ : β ≠ γ) :
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
  (heven : even $ height c) (hβ : c.val.extension = β) : nonempty_semitangle α :=
⟨semitangle_members_of_nonempty_code α c hβ,
  semitangle_extension.proper β (coe_lt_coe.mp $ hβ ▸ c.val.extension_lt : β < α)
  (by { convert code.is_representative.nonempty c heven, rw semitangle_members_eq, refl })
  (λ γ hγ hβγ, by { simp_rw [semitangle_members_ne α c hβ hγ hβγ, semitangle_members_eq], refl })⟩

def semitangle_members_of_nonempty_code_base (c : nonempty_code α α le_rfl)
  (hc : c.val.extension = ⊥) : semitangle_members α :=
λ γ hγ, A_map (bot_lt_coe _) hγ
  ⟨cast (by simp_rw hc) c.val.elts, by { convert c.property, rw hc, simp }⟩

@[simp] lemma semitangle_members_base (c : nonempty_code α α le_rfl) (hc : c.val.extension = ⊥)
  (hβ : β < α) :
  (⟨β, coe_lt_coe.mpr hβ, semitangle_members_of_nonempty_code_base α c hc β hβ⟩ : code α α le_rfl) =
  A_map_code hβ c :=
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c, dsimp at hc, subst hc,
  unfold semitangle_members_of_nonempty_code_base, simp
end

def intro_nonempty_semitangle_base (c : nonempty_code α α le_rfl) (hc : c.val.extension = ⊥) :
  nonempty_semitangle α :=
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

namespace allowable_perm

/-- Allowable permutations act on nonempty semitangles. -/
instance mul_action_nonempty_semitangle :
  mul_action (allowable_perm α le_rfl) (nonempty_semitangle α) := sorry

/-- Allowable permutations act on semitangles. -/
instance mul_action_semitangle : mul_action (allowable_perm α le_rfl) (semitangle α) :=
option.mul_action

end allowable_perm

/-- A tangle at the new level `α` is a symmetric semitangle. This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def new_tangle :=
{s : semitangle α // symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) s}

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
lemma supportedness_equiv {c d : code α α le_rfl} (hcd : c ≡ d) (S : set (support_condition α))
  (hS : supports (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) S c) :
  supports (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) S d := sorry

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
def symmetric_singleton (hβ : β < α) (x : tangle α β (coe_lt_coe.mpr hβ))
  (symm : symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) x) : new_tangle α :=
⟨some $ intro_nonempty_semitangle_proper α ⟨⟨β, coe_lt_coe.mpr hβ, {x}⟩, set.singleton_nonempty _⟩
  (by { convert even_zero, exact height_singleton x }) rfl,
  sorry⟩

/-- For any small set `B` of symmetric `β`-tangles, the code `(α, β, B)` is a tangle at level `α`. -/
def symmetric_set (hβ : β < α) (B : set $ tangle α β (coe_lt_coe.mpr hβ)) (hne : B.nonempty)
  (hsmall : small B)
  (symm : ∀ b ∈ B, symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) b) :
  new_tangle α :=
⟨some $ intro_nonempty_semitangle_proper α ⟨⟨β, coe_lt_coe.mpr hβ, B⟩, hne⟩
  sorry rfl,
  sorry⟩

variables {α}

namespace new_tangle

instance : has_coe (new_tangle α) (semitangle α) := coe_subtype

lemma coe_injective : injective (coe : new_tangle α → semitangle α) := subtype.coe_injective

end new_tangle

namespace allowable_perm

lemma _root_.supports.smul {s : set (support_condition α)} {t : semitangle α}
  (f : allowable_perm α le_rfl) (h : supports (allowable_perm.to_struct_perm $ le_refl α) s t) :
  supports (allowable_perm.to_struct_perm $ le_refl α) (f • s) (f • t) :=
λ g hg, begin
  have := ball_image_iff.1 hg,
  sorry
end

/-- Allowable permutations act on `α`-tangles. -/
instance has_smul_new_tangle : has_smul (allowable_perm α le_rfl) (new_tangle α) :=
⟨λ π t, ⟨π • t, t.2.map $ λ s, ⟨π • s.1, s.2.smul _⟩⟩⟩

@[simp, norm_cast] lemma coe_smul_new_tangle (f : allowable_perm α le_rfl) (t : new_tangle α) :
  (↑(f • t) : semitangle α) = f • t := rfl

instance mul_action_new_tangle : mul_action (allowable_perm α le_rfl) (new_tangle α) :=
new_tangle.coe_injective.mul_action _ coe_smul_new_tangle

end allowable_perm
end con_nf
