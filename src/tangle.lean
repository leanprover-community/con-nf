import allowable
import mathlib.option

noncomputable theory

open function set with_bot
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

-/

variables (α : Λ) [phase_1a.{u} α] {β γ : Λ} {hβ : β < α}

abbreviation semitangle_members :=
Π β (hβ : β < α), {s : set (tangle α β $ coe_lt_coe.mpr hβ) // s.nonempty}

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
inductive semitangle_extension (members : semitangle_members α)
| proper (β : Λ) (hβ : β < α) :
    let c : code α α le_rfl := ⟨β, coe_lt_coe.mpr hβ, members β hβ⟩
    in c.is_even →
      (∀ γ hγ (hβγ : β ≠ γ), A_map hγ c.elts = members γ hγ)
      → semitangle_extension
| base (atoms : set atom) (hne : atoms.nonempty) :
    let c : code α α le_rfl := ⟨⊥, bot_lt_coe _, atoms⟩
    in c.is_even →
      (∀ γ hγ, A_map hγ c.elts = members γ hγ)
      → semitangle_extension

/-- The `-1`-extension associated with a given semitangle extension. -/
def semitangle_extension.atoms {α : Λ} [phase_1a.{u} α] {members : semitangle_members α} :
  semitangle_extension α members → set atom
| (semitangle_extension.proper _ _ _ _) := ∅
| (semitangle_extension.base atoms _ _ _) := atoms

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`.

Here, we restrict our definition to just nonempty semitangles; this simplifies the definition. -/
structure nonempty_semitangle :=
(members : semitangle_members α)
(extension : semitangle_extension α members)

namespace nonempty_semitangle

def mem (hβ : β < α) (t : tangle α β (coe_lt_coe.mpr hβ)) (s : nonempty_semitangle α) : Prop :=
t ∈ (s.members β hβ).val

def repr_code : nonempty_semitangle α → nonempty_code α α le_rfl
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ :=
  ⟨⟨β, coe_lt_coe.mpr hβ, members β hβ⟩, (members β hβ).property⟩
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ :=
  ⟨⟨⊥, bot_lt_coe _, atoms⟩, hne⟩

@[simp] lemma repr_code_proper (members : semitangle_members α) (β hβ rep hA) :
  repr_code α ⟨members, semitangle_extension.proper β hβ rep hA⟩ =
    ⟨⟨β, coe_lt_coe.mpr hβ, members β hβ⟩, (members β hβ).property⟩ := rfl

@[simp] lemma repr_code_base (members : semitangle_members α) (atoms hne rep hA) :
  repr_code α ⟨members, semitangle_extension.base atoms hne rep hA⟩ =
    ⟨⟨⊥, bot_lt_coe _, atoms⟩, hne⟩ := rfl

lemma repr_code_spec : Π (s : nonempty_semitangle α), (repr_code α s : code α α le_rfl).is_even
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ := rep
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ := rep

lemma repr_code_members_eq :
  Π (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (repr_code α s : code α α le_rfl).extension = γ),
  s.members γ hγ =
    ⟨cast (by simp_rw hcγ) (repr_code α s : code α α le_rfl).elts,
    by { convert (repr_code α s).property, exact hcγ.symm, exact cast_heq _ _ }⟩
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ γ hγ hcγ :=
    by { rw repr_code_proper at hcγ, cases hcγ, dsimp, rw subtype.coe_eta }
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ γ hγ hcγ :=
    by { rw repr_code_base at hcγ, cases hcγ }

lemma repr_code_members_ne :
  Π (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (repr_code α s : code α α le_rfl).extension ≠ γ),
  (A_map_code hγ (repr_code α s : code α α le_rfl)).elts =
    (s.members γ hγ : set (tangle α γ _))
| ⟨members, semitangle_extension.proper β hβ rep hA⟩ γ hγ hcγ := hA _ _ (hcγ ∘ coe_eq_coe.mpr)
| ⟨members, semitangle_extension.base atoms hne rep hA⟩ γ hγ hcγ := hA _ _

lemma repr_code_members_val (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (repr_code α s : code α α le_rfl).extension ≠ γ) :
  A_map_code hγ (repr_code α s : code α α le_rfl) =
    ⟨γ, coe_lt_coe.mpr hγ, s.members γ hγ⟩ :=
by { rw ←repr_code_members_ne _ _ _ hcγ, refl }

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
lemma ext_core (x y : nonempty_semitangle α) : (∃ γ, γ < α) → x.members = y.members → x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp,
  rintro ⟨γ, hγ⟩ rfl,
  refine congr_arg (λ h, ⟨xs, h⟩) _,
  cases hxs with β hβ rep₁ hA₁ atoms₁ hne₁ rep₁ hA₁;
    cases hys with γ hγ rep₂ hA₂ atoms₂ hne₂ rep₂ hA₂,
  { simp only,
    refine not_ne_iff.1 (λ β_ne_γ, rep₂.A_map_code_ne rep₁
      (coe_ne_coe.2 β_ne_γ.symm) $ (code.ext_iff _ _).2 ⟨rfl, (hA₂ _ hβ β_ne_γ.symm).heq⟩),
    assumption },
  { cases rep₂.A_map_code_ne rep₁ bot_ne_coe
      ((code.ext_iff _ _).2 ⟨rfl, (hA₂ _ hβ).heq⟩),
    assumption },
  { cases rep₁.A_map_code_ne rep₂  bot_ne_coe
      ((code.ext_iff _ _).2 ⟨rfl, (hA₁ γ hγ).heq⟩),
    assumption },
  { simp_rw A_map_injective _ ((hA₁ γ hγ).trans (hA₂ γ hγ).symm) }
end

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
lemma ext_code (x y : nonempty_semitangle α) :
  ((repr_code α x : code α α le_rfl) ≡ repr_code α y) → x = y :=
begin
  intro h,
  have code_eq := (repr_code_spec α x).unique (repr_code_spec α y) h,
  rw subtype.coe_inj at code_eq,
  by_cases ex_γ : ∃ γ, γ < α,
  { refine ext_core _ _ _ ex_γ _,
    ext γ hγ : 2,
    rw ← subtype.val_inj,
    dsimp only at ⊢,
    by_cases (repr_code α x : code α α le_rfl).extension = γ,
    { obtain ⟨x, γ | s⟩ := x,
      { have := coe_injective h,
        subst this,
        obtain ⟨y, γ' | t⟩ := y,
        { rw [subtype.ext_iff, code.ext_iff] at code_eq,
          have : γ = γ' := coe_injective code_eq.1,
          subst this,
          exact code_eq.2.eq },
        { cases coe_ne_bot (congr_arg (code.extension ∘ subtype.val) code_eq) } },
      cases bot_ne_coe h },
    sorry
    -- rw repr_code_members_val,
    -- rw repr_code_members_val,
    -- rw code_eq,
    -- rw ← code_eq,
    -- exact h,
    -- exact h
    },
  { obtain ⟨xs, hxs⟩ := x,
    obtain ⟨ys, hys⟩ := y,
    have : xs = ys,
    { refine funext _, intro γ, refine funext _, intro hγ, exfalso, exact ex_γ ⟨γ, hγ⟩ },
    subst this, congr,
    cases hxs with β hβ rep hA atoms₁ hne₁ rep₁ hA₁,
    { exfalso, exact ex_γ ⟨β, hβ⟩ },
    cases hys with β hβ rep hA atoms₂ hne₂ rep₂ hA₂,
    { exfalso, exact ex_γ ⟨β, hβ⟩ },
    rw [repr_code_base, repr_code_base] at code_eq,
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
  { dsimp,
    obtain rfl | hγβ := eq_or_ne γ β,
    { obtain rfl | hδγ := eq_or_ne δ γ,
      { convert code.equiv.refl _,
        exact h.symm },
      { simp_rw [h, ←hA₂ _ hγ hδγ],
        exact code.equiv.A_map_left _ rep₂ _ hγ (coe_ne_coe.2 hδγ) } },
    obtain rfl | hδβ := eq_or_ne δ β,
    { simp_rw [←h, ←hA₁ _ hδ hγβ],
      exact code.equiv.A_map_right _ rep₁ _ hδ (coe_ne_coe.2 hγβ) },
    refine (code.equiv.A_map_right _ rep₁ _ hβ $ coe_ne_coe.2 hγβ).trans _,
    dsimp,
    rw [hA₁ _ hβ hγβ, h, ←hA₂ _ hβ hδβ],
    exact code.equiv.A_map_left _ rep₂ _ hβ (coe_ne_coe.2 hδβ) },
  { dsimp,
    obtain rfl | hγβ := eq_or_ne γ β,
    { rw [h, ←hA₂ _ hβ],
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ hβ bot_ne_coe },
    { refine (code.equiv.A_map_right _ rep₁ _ hβ $ coe_ne_coe.2 hγβ).trans _,
      dsimp,
      rw [hA₁ _ hβ hγβ, h, ←hA₂ _ hβ],
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ hβ bot_ne_coe } },
  { dsimp,
    obtain rfl | hδβ := eq_or_ne δ β,
    { simp_rw [←h, ←hA₁ _ hβ],
      exact code.equiv.A_map_right _ (code.is_even_bot _) _ hβ bot_ne_coe },
    { refine (code.equiv.A_map_right _ (code.is_even_bot _) _ hβ bot_ne_coe).trans _,
      dsimp,
      rw [hA₁ _ hβ, h, ←hA₂ _ hβ hδβ],
      exact code.equiv.A_map_left _ rep₂ _ hβ (coe_ne_coe.2 hδβ) } },
  { refine (code.equiv.A_map_right _ (code.is_even_bot _) _ hβ bot_ne_coe).trans _,
    dsimp,
    rw [hA₁ _ hβ, h, ←hA₂ _ hβ],
    exact code.equiv.A_map_left _ (code.is_even_bot _) _ hβ bot_ne_coe }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext' (x y : nonempty_semitangle α) (hβ : β < α) (h : ∀ t, mem α hβ t x ↔ mem α hβ t y) :
  x = y :=
by { refine ext α x y hβ _, ext t, exact h t }

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all nonempty semitangles have a `-1`-extension.
Therefore, the extensionality principle in this case applies to the `-1`-extensions. -/
lemma ext_zero (x y : nonempty_semitangle α) (α_zero : ¬∃ β, β < α)
  (h : x.extension.atoms = y.extension.atoms) : x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  obtain ⟨γ, hγ, _, _⟩ | ⟨atoms₁, hne₁, rep₁, hA₁⟩ := hxs,
  { exfalso, exact α_zero ⟨γ, hγ⟩ },
  obtain ⟨γ, hγ, _, _⟩ | ⟨atoms₂, hne₂, rep₂, hA₂⟩ := hys,
  { exfalso, exact α_zero ⟨γ, hγ⟩ },
  cases h,
  suffices : xs = ys, by subst this,
  ext β hβ -, exfalso, exact α_zero ⟨β, hβ⟩
end

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
    (λ hne, ⟨A_map hγ c.1.elts, c.2.A_map⟩)

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
  rw dif_neg hβγ,
  refl,
end

/-- We can construct nonempty semitangles from nonempty even codes with extensions at proper type
indices. -/
def intro_nonempty_semitangle_proper (c : nonempty_code α α le_rfl) (heven : c.1.is_even)
  (hβ : c.val.extension = β) : nonempty_semitangle α :=
⟨semitangle_members_of_nonempty_code α c hβ,
  semitangle_extension.proper β (coe_lt_coe.mp $ hβ ▸ c.val.extension_lt : β < α)
  (by rwa semitangle_members_eq)
  (λ γ hγ hβγ, begin
    obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c,
    dsimp at hβ,
    subst hβ,
    simp [semitangle_members_of_nonempty_code, dif_neg hβγ],
  end)⟩

def semitangle_members_of_nonempty_code_base (c : nonempty_code α α le_rfl)
  (hc : c.val.extension = ⊥) : semitangle_members α :=
λ γ hγ, ⟨A_map hγ $ cast (by simp_rw hc) c.val.elts, begin
    obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c,
    dsimp at hc,
    subst hc,
    simpa using hG,
  end⟩

@[simp] lemma semitangle_members_base (c : nonempty_code α α le_rfl) (hc : c.val.extension = ⊥)
  (hβ : β < α) :
  (⟨β, coe_lt_coe.mpr hβ, semitangle_members_of_nonempty_code_base α c hc β hβ⟩ : code α α le_rfl) =
  A_map_code hβ c :=
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c,
  dsimp at hc,
  subst hc,
  simp [semitangle_members_of_nonempty_code_base],
end

def intro_nonempty_semitangle_base (c : nonempty_code α α le_rfl) (hc : c.val.extension = ⊥) :
  nonempty_semitangle α :=
⟨semitangle_members_of_nonempty_code_base α c hc,
  semitangle_extension.base (cast (by { simp_rw hc, refl }) c.val.elts)
  (by { convert c.property, simp_rw hc, refl, simp })
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c,
  dsimp at hc,
  subst hc,
  exact code.is_even_bot _,
end
(λ β hβ, begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c,
  dsimp at hc,
  subst hc,
  simp [semitangle_members_of_nonempty_code_base],
end)⟩

variable [phase_1b α]

namespace allowable_perm

/-- Allowable permutations act on nonempty semitangles. -/
instance mul_action_nonempty_semitangle :
  mul_action (allowable_perm α) (nonempty_semitangle α) := sorry

/-- Allowable permutations act on semitangles. -/
instance mul_action_semitangle : mul_action (allowable_perm α) (semitangle α) := option.mul_action

end allowable_perm

/-- A tangle at the new level `α` is a symmetric semitangle. This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def new_tangle := {s : semitangle α // symmetric (λ π : allowable_perm α, π.1.to_struct_perm) s}

variables {α} {c d : code α α le_rfl} {S : set (support_condition α)}

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected lemma code.equiv.supports (hcd : c ≡ d)
  (hS : supports (λ π : allowable_perm α, π.1.to_struct_perm) S c) :
  supports (λ π : allowable_perm α, π.1.to_struct_perm) S d :=
λ f h, (hcd.symm.smul.trans $ (code.equiv.of_eq $ hS f h).trans hcd).unique rfl

lemma code.equiv.supports_iff (hcd : c ≡ d) :
  supports (λ π : allowable_perm α, π.1.to_struct_perm) S c ↔
    supports (λ π : allowable_perm α, π.1.to_struct_perm) S d :=
⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is symmetric if and only if the other is. -/
lemma code.equiv.symmetric_iff (hcd : c ≡ d) :
  symmetric (λ π : allowable_perm α, π.1.to_struct_perm) c ↔
    symmetric (λ π : allowable_perm α, π.1.to_struct_perm) d :=
⟨λ ⟨⟨s, h⟩⟩, ⟨⟨s, hcd.supports h⟩⟩, λ ⟨⟨s, h⟩⟩, ⟨⟨s, hcd.symm.supports h⟩⟩⟩

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def typed_near_litter (N : near_litter) : new_tangle α :=
⟨some $ intro_nonempty_semitangle_base α ⟨⟨⊥, bot_lt_coe _, N.snd.val⟩, sorry⟩ rfl, sorry⟩

/-- For any symmetric tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def symmetric_singleton (hβ : β < α) (x : tangle α β (coe_lt_coe.mpr hβ))
  (symm : symmetric (λ π : allowable_perm α, π.1.to_struct_perm) x) : new_tangle α :=
⟨some $ intro_nonempty_semitangle_proper α ⟨⟨β, coe_lt_coe.mpr hβ, {x}⟩, set.singleton_nonempty _⟩
  (code.is_even_singleton _) rfl,
  sorry⟩

/-- For any small set `B` of symmetric `β`-tangles, the code `(α, β, B)` is a tangle at level `α`.
-/
def symmetric_set (hβ : β < α) (B : set $ tangle α β (coe_lt_coe.mpr hβ)) (hne : B.nonempty)
  (hsmall : small B)
  (symm : ∀ b ∈ B, symmetric (λ π : allowable_perm α, π.1.to_struct_perm) b) :
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
  (f : allowable_perm α) (h : supports (to_struct_perm : allowable_perm α → struct_perm α) s t) :
  supports (to_struct_perm : allowable_perm α → struct_perm α) (f • s) (f • t) :=
λ g hg, begin
  have := ball_image_iff.1 hg,
  sorry
end

/-- Allowable permutations act on `α`-tangles. -/
instance has_smul_new_tangle : has_smul (allowable_perm α) (new_tangle α) :=
⟨λ π t, ⟨π • t, t.2.map $ λ s, ⟨π • s.1, s.2.smul _⟩⟩⟩

@[simp, norm_cast] lemma coe_smul_new_tangle (f : allowable_perm α) (t : new_tangle α) :
  (↑(f • t) : semitangle α) = f • t := rfl

instance mul_action_new_tangle : mul_action (allowable_perm α) (new_tangle α) :=
new_tangle.coe_injective.mul_action _ coe_smul_new_tangle

end allowable_perm
end con_nf
