import mathlib.group_action
import mathlib.option
import mathlib.pointwise
import phase1.allowable

noncomputable theory

open function set with_bot
open_locale cardinal pointwise

universe u

namespace con_nf
variables [params.{u}]

/-

/-- A pretangle has a preferred extension, which is either a proper type `β : Λ`,
or the base type `-1`. A pretangle has a `-1`-extension if and only if its preferred extension
is the `-1`-extension. -/
inductive preferred_extension (α : Λ) : Type u
| proper_extension : Π (β < α), preferred_extension
| base_extension : set atom → preferred_extension

-/

variables (α : Λ) [tangle_data α] {β : Λ} {hβ : β < α} {γ : type_index} {hγ : γ < α}

namespace semitangle

/-- The possible extensions of a nonempty semitangle. -/
abbreviation extension := Π β (hβ : β < α), tangles α β $ coe_lt_coe.2 hβ

namespace extension
variables {α}

/-- The extensions for a code. -/
protected def A_map (s : tangles α γ hγ) : extension α :=
λ β hβ, if hβγ : ↑β = γ then by { subst hβγ, exact s } else ⟨A_map hβ _, s.prop.A_map⟩

@[simp] lemma A_map_self (s : tangles α β $ coe_lt_coe.2 hβ) : extension.A_map s _ hβ = s :=
dif_pos rfl

lemma A_map_of_ne (s : tangles α γ hγ) (hβγ : ↑β ≠ γ) :
  extension.A_map s β hβ = ⟨A_map hβ _, s.prop.A_map⟩ := dif_neg hβγ

end extension

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
inductive preference (exts : extension α)
| base (atoms : tangles α ⊥ $ bot_lt_coe _) :
    (⟨⊥, bot_lt_coe _, atoms⟩ : code α).is_even →
      (∀ γ hγ, A_map hγ (atoms : set (tangle α ⊥ $ bot_lt_coe _)) = exts γ hγ) → preference
| proper (β : Λ) (hβ : β < α) :
    (⟨β, coe_lt_coe.mpr hβ, exts β hβ⟩ : code α).is_even →
      (∀ γ hγ, β ≠ γ → A_map hγ (exts β hβ : set (tangle α ↑β $ coe_lt_coe.2 hβ)) = exts γ hγ)
      → preference

/-- The `-1`-extension associated with a given semitangle extension. -/
def preference.atoms {α : Λ} [tangle_data α] {members : extension α} :
  preference α members → set atom
| (preference.base atoms _ _) := (atoms : set (tangle α ⊥ $ bot_lt_coe _))
| (preference.proper _ _ _ _) := ∅

end semitangle

open semitangle

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`.

Here, we restrict our definition to just nonempty semitangles; this simplifies the definition. -/
structure nonempty_semitangle :=
(exts : extension α)
(pref : preference α exts)

namespace nonempty_semitangle
variables {α}

/-- The membership relation for nonempty semitangles. -/
def mem (hβ : β < α) (t : tangle α β $ coe_lt_coe.2 hβ) (s : nonempty_semitangle α) : Prop :=
t ∈ (s.exts β hβ).val

notation t ` ∈ₙₛₜ `:50 s:50 := mem ‹_› t s

/-- The even code associated to a nonempty semitangle. -/
def repr_code : nonempty_semitangle α → nonempty_code α
| ⟨exts, preference.base atoms rep hA⟩ := ⟨⟨⊥, bot_lt_coe _, atoms⟩, atoms.2⟩
| ⟨exts, preference.proper β hβ rep hA⟩ := ⟨⟨β, coe_lt_coe.mpr hβ, exts β hβ⟩, (exts β hβ).property⟩

@[simp] lemma repr_code_proper (exts : extension α) (β hβ rep hA) :
  repr_code ⟨exts, preference.proper β hβ rep hA⟩ =
    ⟨⟨β, coe_lt_coe.mpr hβ, exts β hβ⟩, (exts β hβ).property⟩ := rfl

@[simp] lemma repr_code_base (exts : extension α) (atoms rep hA) :
  repr_code ⟨exts, preference.base atoms rep hA⟩ = ⟨⟨⊥, bot_lt_coe _, atoms⟩, atoms.2⟩ := rfl

lemma repr_code_spec : Π (s : nonempty_semitangle α), (repr_code s : code α).is_even
| ⟨exts, preference.proper β hβ rep hA⟩ := rep
| ⟨exts, preference.base atoms rep hA⟩ := rep

lemma repr_code_members_eq :
  Π (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (repr_code s : code α).extension = γ),
  s.exts γ hγ =
    ⟨cast (by simp_rw hcγ) (repr_code s : code α).elts,
    by { convert (repr_code s).property, exact hcγ.symm, exact cast_heq _ _ }⟩
| ⟨exts, preference.proper β hβ rep hA⟩ γ hγ hcγ :=
    by { rw repr_code_proper at hcγ, cases hcγ, dsimp, rw subtype.coe_eta }
| ⟨exts, preference.base atoms rep hA⟩ γ hγ hcγ := by { rw repr_code_base at hcγ, cases hcγ }

lemma repr_code_members_ne :
  Π (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α) (hcγ : (repr_code s : code α).extension ≠ γ),
  (A_map_code hγ (repr_code s)).elts = (s.exts γ hγ : set (tangle α γ _))
| ⟨exts, preference.proper β hβ rep hA⟩ γ hγ hcγ := hA _ _ (hcγ ∘ coe_eq_coe.mpr)
| ⟨exts, preference.base atoms rep hA⟩ γ hγ hcγ := hA _ _

lemma repr_code_members_val (s : nonempty_semitangle α) {γ : Λ} (hγ : γ < α)
  (hcγ : (repr_code s : code α).extension ≠ γ) :
  A_map_code hγ (repr_code s) = ⟨γ, coe_lt_coe.mpr hγ, s.exts γ hγ⟩ :=
by { rw ←repr_code_members_ne _ _ hcγ, refl }

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
lemma ext_core (x y : nonempty_semitangle α) : (∃ γ, γ < α) → x.exts = y.exts → x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp,
  rintro ⟨γ, hγ⟩ rfl,
  refine congr_arg (λ h, ⟨xs, h⟩) _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨β, hβ, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨γ, hγ, even₂, hA₂⟩ := hys,
  { simp_rw subtype.coe_injective (A_map_injective _ $ (hA₁ γ hγ).trans (hA₂ γ hγ).symm) },
  { cases even₁.A_map_code_ne even₂  bot_ne_coe ((code.ext_iff _ _).2 ⟨rfl, (hA₁ γ hγ).heq⟩) },
  { cases even₂.A_map_code_ne even₁ bot_ne_coe ((code.ext_iff _ _).2 ⟨rfl, (hA₂ _ hβ).heq⟩) },
  { simp only,
    refine not_ne_iff.1 (λ hβγ, even₂.A_map_code_ne even₁ (coe_ne_coe.2 hβγ.symm) $
      (code.ext_iff _ _).2 ⟨rfl, (hA₂ _ hβ hβγ.symm).heq⟩) }
end

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
lemma ext_code : ∀ {x y : nonempty_semitangle α}, (repr_code x : code α) ≡ repr_code y → x = y
| ⟨x, preference.base atoms₁ even₁ hA₁⟩ ⟨y, preference.base atoms₂ even₂ hA₂⟩ h := begin
  obtain rfl := subtype.coe_injective (code.equiv.bot_bot_iff.1 h),
  obtain rfl : x = y := funext (λ γ, funext $ λ hγ, subtype.coe_injective $ (hA₁ _ _).symm.trans $
    hA₂ _ _),
  refl,
end
| ⟨x, preference.base s even₁ hA₁⟩ ⟨y, preference.proper γ hγ even₂ hA₂⟩ h := begin
  dsimp at h,
  obtain ⟨δ, hδ, hγδ⟩ := (code.equiv.bot_left_iff.1 h).resolve_left
    (λ h, bot_ne_coe $ congr_arg code.extension h),
  rw hγδ at even₂,
  cases even₂.not_is_odd (even₁.A_map_code bot_ne_coe),
end
| ⟨x, preference.proper γ hγ even₁ hA₁⟩ ⟨y, preference.base s even₂ hA₂⟩ h := begin
  dsimp at h,
  obtain ⟨δ, hδ, hγδ⟩ := (code.equiv.bot_right_iff.1 h).resolve_left
    (λ h, coe_ne_bot $ congr_arg code.extension h),
  rw hγδ at even₁,
  cases even₁.not_is_odd (even₂.A_map_code bot_ne_coe),
end
| ⟨x, preference.proper γ hγ even₁ hA₁⟩ ⟨y, preference.proper δ hδ even₂ hA₂⟩ h := begin
  dsimp at h,
  simp [code.equiv_iff, code.ext_iff, with_bot.coe_eq_coe] at h,
  obtain ⟨rfl, h⟩ | ⟨-, γ, hδγ, rfl, hγ, h⟩ | ⟨-, δ, hγδ, rfl, hδ, h⟩ |
    ⟨c, hc, γ, hcγ, hγ, δ, hcδ, ⟨rfl, hx⟩, rfl, hδ, hy⟩ := h,
  { suffices : x = y,
    { subst this },
    refine funext (λ ε, funext $ λ hε, subtype.coe_injective _),
    obtain rfl | hδε := eq_or_ne δ ε,
    { exact h.eq.symm },
    refine (hA₁ _ _ hδε).symm.trans (eq.trans _ $ hA₂ _ _ hδε),
    rw h.eq },
  { rw h.eq at even₁,
    cases (even₂.A_map_code $ coe_ne_coe.2 hδγ).not_is_even even₁ },
  { rw h.eq at even₂,
    cases (even₁.A_map_code $ coe_ne_coe.2 hγδ).not_is_even even₂ },
  { rw hx.eq at even₁,
    cases (hc.A_map_code hcγ).not_is_even even₁ }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext (x y : nonempty_semitangle α) (hβ : β < α) (h : x.exts β hβ = y.exts β hβ) : x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp only at h,
  refine ext_code _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨γ, hγ, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨δ, hδ, even₂, hA₂⟩ := hys,
  { refine (code.equiv.A_map_right _ (code.is_even_bot _) _ hβ bot_ne_coe).trans _,
    dsimp,
    rw [hA₁ _ hβ, h, ←hA₂ _ hβ],
    exact code.equiv.A_map_left _ (code.is_even_bot _) _ hβ bot_ne_coe },
  { dsimp,
    obtain rfl | hδβ := eq_or_ne δ β,
    { simp_rw [←h, ←hA₁ _ hβ],
      exact code.equiv.A_map_right _ (code.is_even_bot _) _ hβ bot_ne_coe },
    { refine (code.equiv.A_map_right _ (code.is_even_bot _) _ hβ bot_ne_coe).trans _,
      dsimp,
      rw [hA₁ _ hβ, h, ←hA₂ _ hβ hδβ],
      exact code.equiv.A_map_left _ even₂ _ hβ (coe_ne_coe.2 hδβ) } },
  { dsimp,
    obtain rfl | hγβ := eq_or_ne γ β,
    { rw [h, ←hA₂ _ hβ],
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ hβ bot_ne_coe },
    { refine (code.equiv.A_map_right _ even₁ _ hβ $ coe_ne_coe.2 hγβ).trans _,
      dsimp,
      rw [hA₁ _ hβ hγβ, h, ←hA₂ _ hβ],
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ hβ bot_ne_coe } },
  { dsimp,
    obtain rfl | hγβ := eq_or_ne γ β,
    { obtain rfl | hδγ := eq_or_ne δ γ,
      { rw h },
      { simp_rw [h, ←hA₂ _ hγ hδγ],
        exact code.equiv.A_map_left _ even₂ _ hγ (coe_ne_coe.2 hδγ) } },
    obtain rfl | hδβ := eq_or_ne δ β,
    { simp_rw [←h, ←hA₁ _ hδ hγβ],
      exact code.equiv.A_map_right _ even₁ _ hδ (coe_ne_coe.2 hγβ) },
    refine (code.equiv.A_map_right _ even₁ _ hβ $ coe_ne_coe.2 hγβ).trans _,
    dsimp,
    rw [hA₁ _ hβ hγβ, h, ←hA₂ _ hβ hδβ],
    exact code.equiv.A_map_left _ even₂ _ hβ (coe_ne_coe.2 hδβ) }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext' (x y : nonempty_semitangle α) (hβ : β < α) (h : ∀ t, t ∈ₙₛₜ x ↔ t ∈ₙₛₜ y) : x = y :=
ext x y hβ $ subtype.ext $ set.ext h

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all nonempty semitangles have a `-1`-extension.
Therefore, the extensionality principle in this case applies to the `-1`-extensions. -/
lemma ext_zero (x y : nonempty_semitangle α) (α_zero : is_min α) (h : x.pref.atoms = y.pref.atoms) :
  x = y :=
begin
  obtain ⟨xs, ⟨atoms₁, rep₁, hA₁⟩ | ⟨γ, hγ, _, _⟩⟩ := x, swap,
  { cases α_zero.not_lt hγ },
  obtain ⟨ys, ⟨atoms₂, rep₂, hA₂⟩ | ⟨γ, hγ, _, _⟩⟩ := y, swap,
  { cases α_zero.not_lt hγ },
  have : atoms₁ = atoms₂ := subtype.coe_injective h,
  subst this,
  suffices : xs = ys, by subst this,
  ext β hβ -,
  cases α_zero.not_lt hβ,
end

end nonempty_semitangle

/-- A semitangle is either a nonempty semitangle, or the `⊥` element, which is considered the empty
set. Note that in TTT, a set contains no elements at one level if and only if it contains no
elements at all levels. -/
@[reducible] def semitangle := with_bot (nonempty_semitangle α)

variables {α}

namespace semitangle

/-- The membership relation of tangles and semitangles in TTT at this level. -/
def mem (hβ : β < α) (t : tangle α β _) (s : semitangle α) := s.elim false $ (∈ₙₛₜ) t

notation t ` ∈ₛₜ `:50 s:50 := mem ‹_› t s

variables (t : tangle α β $ coe_lt_coe.2 hβ) {s : semitangle α}

lemma not_mem_bot (hβ : β < α) (t : tangle α β _) : ¬ t ∈ₛₜ ⊥ := id
@[simp] lemma mem_coe {hβ : β < α} {s : nonempty_semitangle α} {t : tangle α β _} :
  t ∈ₛₜ s ↔ t ∈ₙₛₜ s := iff.rfl

lemma eq_bot_of_forall_not_mem (hβ : β < α) (s : semitangle α) (h : ∀ t, ¬ t ∈ₛₜ s) : s = ⊥ :=
begin
  cases s,
  { refl },
  { cases h _ (s.exts _ _).2.some_spec }
end

lemma ext (x y : semitangle α) (hβ : β < α) : (∀ t, t ∈ₛₜ x ↔ t ∈ₛₜ y) → x = y :=
begin
  intro h,
  cases x,
  { exact (eq_bot_of_forall_not_mem _ _ $ λ _, (h _).2).symm },
  cases y,
  { exact eq_bot_of_forall_not_mem _ _ (λ _, (h _).1) },
  rw nonempty_semitangle.ext' x y hβ h,
end

/-- Construct a nonempty semitangle from an even nonempty code. -/
def intro (s : tangles α γ hγ)
  (heven : (⟨γ, hγ, s⟩ : code α).is_even) : nonempty_semitangle α :=
⟨extension.A_map s, rec_bot_coe
  (λ _ s _, preference.base s (code.is_even_bot _) $ λ β hβ, sorry)
  (λ γ hγ s heven, preference.proper γ (coe_lt_coe.1 hγ)
    (by rwa extension.A_map_self) $ λ β hβ hβγ,
      by { rw [extension.A_map_self, extension.A_map_of_ne _ (coe_ne_coe.2 hβγ.symm)], refl })
    γ hγ s heven⟩

@[simp] lemma exts_intro (s : tangles α γ hγ) (heven) :
  (intro s heven).exts = extension.A_map s := rfl

end semitangle

open semitangle

namespace allowable_perm

lemma smul_extension_A_map (f : allowable_perm α) (s : tangles α γ hγ) :
  f • extension.A_map s = extension.A_map (f • s) :=
begin
unfold extension.A_map,
funext β hβ,
dsimp,
split_ifs,
{ subst h, },
{ rw ← subtype.coe_inj,
  simp only [smul_nonempty_mk, subtype.coe_mk],
  exact smul_A_map _ _ _ (ne.symm h), },
end

lemma smul_aux₁ {f : allowable_perm α} {e : extension α}
  {s : set (tangle α ⊥ $ bot_lt_coe _)} (h : ∀ γ (hγ : γ < α), A_map hγ s = e γ hγ) (γ hγ) :
  A_map hγ (f • s) = f • e γ hγ :=
by rw [←h γ hγ, smul_A_map _ _ _ bot_ne_coe]

lemma smul_aux₂ {f : allowable_perm α} {e : extension α} {γ} {hγ : γ < α}
  (h : ∀ δ (hδ : δ < α), γ ≠ δ →
    A_map hδ (e γ hγ : set (tangle α ↑γ $ coe_lt_coe.2 hγ)) = ↑(e δ hδ)) (δ hδ) (hγδ : γ ≠ δ) :
  A_map hδ (f • (e γ hγ : set (tangle α ↑γ $ coe_lt_coe.2 hγ))) = f • ↑(e δ hδ) :=
by rw [←smul_A_map _ _ _ (coe_ne_coe.2 hγδ), h _ _ hγδ]

/-- Allowable permutations act on nonempty semitangles. -/
instance mul_action_nonempty_semitangle : mul_action (allowable_perm α) (nonempty_semitangle α) :=
{ smul := λ f t, ⟨f • t.exts, begin
    obtain ⟨exts, ⟨s, ht, h⟩ | ⟨γ, hγ, ht, h⟩⟩ := t,
    { exact preference.base (f • s) (code.is_even_bot _) (smul_aux₁ h) },
    { exact preference.proper _ hγ ht.smul (smul_aux₂ h) }
    end⟩,
  one_smul := begin
    rintro ⟨exts, ⟨s, ht, h⟩ | ⟨γ, hγ, ht, h⟩⟩; sorry
  end,
  mul_smul := begin
    rintro f g ⟨exts, ⟨s, ht, h⟩ | ⟨γ, hγ, ht, h⟩⟩; sorry
  end }

@[simp] lemma members_smul (f : allowable_perm α) (s : nonempty_semitangle α) :
  (f • s).exts = f • s.exts := rfl

@[simp] lemma smul_base (f : allowable_perm α) (e : extension α) (s ht h) :
  f • (⟨e, preference.base s ht h⟩ : nonempty_semitangle α) =
    ⟨f • e, preference.base (f • s) ht.smul $ smul_aux₁ h⟩ := rfl

@[simp] lemma smul_proper (f : allowable_perm α) (e : extension α) (γ hγ ht h) :
  f • (⟨e, preference.proper γ hγ ht h⟩ : nonempty_semitangle α) =
    ⟨f • e, preference.proper _ hγ ht.smul $ smul_aux₂ h⟩ := rfl

/-- Allowable permutations act on semitangles. -/
instance mul_action_semitangle : mul_action (allowable_perm α) (semitangle α) := option.mul_action

end allowable_perm

variables (α)

/-- A tangle at the new level `α` is a supported semitangle. This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def new_tangle := {s : semitangle α // supported (λ π : allowable_perm α, π.1.to_struct_perm) s}

variables {α} {c d : code α} {S : set (support_condition α)}

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected lemma code.equiv.supports (hcd : c ≡ d)
  (hS : supports (λ π : allowable_perm α, π.1.to_struct_perm) S c) :
  supports (λ π : allowable_perm α, π.1.to_struct_perm) S d :=
λ f h, (hcd.symm.smul.trans $ (code.equiv.of_eq $ hS f h).trans hcd).unique rfl

lemma code.equiv.supports_iff (hcd : c ≡ d) :
  supports (λ π : allowable_perm α, π.1.to_struct_perm) S c ↔
    supports (λ π : allowable_perm α, π.1.to_struct_perm) S d :=
⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
lemma code.equiv.supported_iff (hcd : c ≡ d) :
  supported (λ π : allowable_perm α, π.1.to_struct_perm) c ↔
    supported (λ π : allowable_perm α, π.1.to_struct_perm) d :=
⟨λ ⟨⟨s, h⟩⟩, ⟨⟨s, hcd.supports h⟩⟩, λ ⟨⟨s, h⟩⟩, ⟨⟨s, hcd.symm.supports h⟩⟩⟩

@[simp] lemma smul_intro (f : allowable_perm α) (s : tangles α γ hγ) (hs) :
  f • intro s hs = intro (f • s) (by cases γ; exact hs.smul) :=
begin
  induction γ using with_bot.rec_bot_coe,
  { dsimp [intro],
    simp_rw f.smul_extension_A_map,
    sorry },
  { dsimp [intro],
    simp_rw f.smul_extension_A_map,
    sorry }
end

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def typed_near_litter (N : near_litter) : new_tangle α :=
⟨some $ intro ⟨(show set (tangle α ⊥ $ bot_lt_coe _), from N.2.1), N.2.2.nonempty⟩ $
  code.is_even_bot _, ⟨⟨⟨{(sum.inr N, default)}, small_singleton _⟩, λ f h, begin
  dsimp at ⊢ h,
  rw smul_intro,
  have := congr_arg prod.fst (h _ rfl),
  have := sum.inr_injective this,
  conv { to_rhs, rw ←this },
  dsimp,
  congr',
  sorry
end⟩⟩⟩

/-- For any supported tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def supported_singleton (hβ : β < α) (x : tangle α β (coe_lt_coe.mpr hβ))
  (supp : supported (λ π : allowable_perm α, π.1.to_struct_perm) x) : new_tangle α :=
⟨some $ intro ⟨{x}, singleton_nonempty _⟩ (code.is_even_singleton _), sorry⟩

/-- For any small set `B` of supported `β`-tangles, the code `(α, β, B)` is a tangle at level `α`.
-/
def supported_set (hβ : β < α) (s : {s : set $ tangle α β (coe_lt_coe.2 hβ) // s.nonempty})
  (hs : small (s : set $ tangle α β (coe_lt_coe.2 hβ)))
  (symm : ∀ b ∈ (s : set $ tangle α β (coe_lt_coe.2 hβ)),
    supported (λ π : allowable_perm α, π.1.to_struct_perm) b) :
  new_tangle α :=
⟨some $ intro s sorry, sorry⟩

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
