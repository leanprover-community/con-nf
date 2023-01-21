import group_theory.group_action.option
import mathlib.group_action
import mathlib.pointwise
import phase1.allowable

noncomputable theory

open function set with_bot
open_locale cardinal pointwise

universe u

namespace con_nf
variables [params.{u}] [position_data.{}]

open code Iio_index

variables (α : Λ) [core_tangle_cumul α] {β : Iio_index α} {γ : Iio α}

abbreviation extensions := Π β : Iio α, set (tangle β)

namespace semitangle

variables [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
@[nolint has_nonempty_instance] inductive preference (members : extensions α)
| base (atoms : set (tangle (⊥ : Iio_index α))) :
    (mk ⊥ atoms).is_even →
    (∀ γ, A_map bot_ne_coe atoms = members γ) →
    preference
| proper (β : Iio α) :
    (mk β (members β) : code α).is_even →
    (∀ (γ : Iio α) (hβγ : Iio_coe β ≠ γ), A_map hβγ (members β) = members γ) →
    preference

variables {α} {members : extensions α}

/-- The `-1`-extension associated with a given semitangle extension. -/
def preference.atoms : preference α members → set atom
| (preference.base atoms _ _) := (atoms : set (tangle ⊥))
| (preference.proper _ _ _) := ∅

lemma preference.base_heq_base {m₁ m₂ : extensions α} {s₁ s₂ h₁ h₂ h₃ h₄}
  (hm : m₁ = m₂) (hs : s₁ = s₂) :
  (preference.base s₁ h₁ h₂ : preference α m₁) ==
    (preference.base s₂ h₃ h₄ : preference α m₂) :=
by cases hm; cases hs; refl

lemma preference.proper_heq_proper {m₁ m₂ : extensions α} {β₁ β₂ h₁ h₂ h₃ h₄}
  (hm : m₁ = m₂) (hs : β₁ = β₂) :
  (preference.proper β₁ h₁ h₂ : preference α m₁) ==
    (preference.proper β₂ h₃ h₄ : preference α m₂) :=
by cases hm; cases hs; refl

end semitangle

open semitangle

variables [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`. -/
@[nolint has_nonempty_instance]
structure semitangle :=
(members : extensions α)
(pref : preference α members)

variables {α}
namespace semitangle

/-- The membership relation for nonempty semitangles. -/
def mem (t : tangle γ) (s : semitangle α) : Prop := t ∈ s.members γ

notation t ` ∈ₛₜ `:50 s:50 := mem t s

/-- The even code associated to a nonempty semitangle. -/
def repr_code : semitangle α → code α
| ⟨exts, preference.base atoms rep hA⟩ := ⟨⊥, atoms⟩
| ⟨exts, preference.proper β rep hA⟩ := ⟨β, exts β⟩

@[simp] lemma repr_code_base (exts : extensions α) (atoms rep hA) :
  repr_code ⟨exts, preference.base atoms rep hA⟩ = ⟨⊥, atoms⟩ := rfl

@[simp] lemma repr_code_proper (exts : extensions α) (β rep hA) :
  repr_code ⟨exts, preference.proper β rep hA⟩ = ⟨β, exts β⟩ := rfl

lemma repr_code_spec : Π (s : semitangle α), (repr_code s : code α).is_even
| ⟨exts, preference.proper β rep hA⟩ := rep
| ⟨exts, preference.base atoms rep hA⟩ := rep

lemma repr_code_members_ne :
  Π (s : semitangle α) (γ : Iio α) (hcγ : (repr_code s : code α).1 ≠ γ),
  (A_map_code γ (repr_code s)).2 = s.members γ
| ⟨exts, preference.proper β rep hA⟩ γ hcγ := by rw snd_A_map_code; exact hA _ hcγ
| ⟨exts, preference.base atoms rep hA⟩ γ hcγ := hA _

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
lemma ext_core (x y : semitangle α) : (∃ γ, γ < α) → x.members = y.members → x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp,
  rintro ⟨γ, hγ⟩ rfl,
  have γ : Iio α := ⟨γ, hγ⟩,
  refine congr_arg (λ h, ⟨xs, h⟩) _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨γ, even₂, hA₂⟩ := hys,
  { simp_rw A_map_injective ((hA₁ γ).trans (hA₂ _).symm) },
  { cases even₁.A_map_code_ne even₂  bot_ne_mk_coe (sigma.ext_iff.2 ⟨rfl, (hA₁ γ).heq⟩) },
  { cases even₂.A_map_code_ne even₁ bot_ne_mk_coe (sigma.ext_iff.2 ⟨rfl, (hA₂ β).heq⟩) },
  { simp only,
    refine not_ne_iff.1 (λ hβγ, even₂.A_map_code_ne even₁ (Iio.coe_injective.ne hβγ.symm) $
      sigma.ext_iff.2 ⟨rfl, heq_of_eq _⟩),
    rw snd_A_map_code,
    exact hA₂ β (λ h, hβγ.symm (Iio.coe_injective h)) }
end

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
lemma ext_code : ∀ {x y : semitangle α}, (repr_code x : code α) ≡ repr_code y → x = y
| ⟨x, preference.base atoms₁ even₁ hA₁⟩ ⟨y, preference.base atoms₂ even₂ hA₂⟩ h := begin
  obtain rfl := code.equiv.bot_bot_iff.1 h,
  obtain rfl : x = y := funext (λ γ, (hA₁ _).symm.trans $ hA₂ _),
  refl,
end
| ⟨x, preference.base s even₁ hA₁⟩ ⟨y, preference.proper γ even₂ hA₂⟩ h := begin
  change code.mk _ _ ≡ code.mk _ _ at h,
  obtain ⟨δ, hδ⟩ := (code.equiv.bot_left_iff.1 h).resolve_left
    (ne_of_apply_ne sigma.fst bot_ne_mk_coe),
  rw hδ at even₂,
  cases even₂.not_is_odd (even₁.A_map_code bot_ne_mk_coe),
end
| ⟨x, preference.proper γ even₁ hA₁⟩ ⟨y, preference.base s even₂ hA₂⟩ h := begin
  change code.mk _ _ ≡ code.mk _ _ at h,
  obtain ⟨δ, hδ⟩ := (code.equiv.bot_right_iff.1 h).resolve_left
    (ne_of_apply_ne sigma.fst mk_coe_ne_bot),
  rw hδ at even₁,
  cases even₁.not_is_odd (even₂.A_map_code bot_ne_mk_coe),
end
| ⟨x, preference.proper γ even₁ hA₁⟩ ⟨y, preference.proper δ even₂ hA₂⟩ h := begin
  dsimp at h,
  simp only [code.equiv_iff, sigma.ext_iff, mem_Iio, Iio.coe_inj, ne.def, fst_A_map_code,
    snd_A_map_code, Iio.coe_mk] at h,
  obtain ⟨rfl, h⟩ | ⟨-, γ, hδγ, rfl, h⟩ | ⟨-, δ, hγδ, rfl, h⟩ |
    ⟨c, hc, γ, hcγ, δ, hcδ, ⟨⟨rfl, hx'⟩, hx⟩, _⟩ := h,
  { suffices : x = y,
    { subst this },
    refine funext (λ ε, _),
    obtain rfl | hδε := eq_or_ne δ ε,
    { exact h.eq.symm },
    refine (hA₁ _ (λ h, hδε (Iio.coe_injective h))).symm.trans
      (eq.trans _ $ hA₂ _ (λ h, hδε (Iio.coe_injective h))),
    dsimp,
    rw h.eq },
  { rw h.eq at even₁,
    cases (even₂.A_map_code $ Iio.coe_injective.ne hδγ).not_is_even even₁ },
  { rw h.eq at even₂,
    cases (even₁.A_map_code $ Iio.coe_injective.ne hγδ).not_is_even even₂ },
  { rw hx.eq at even₁,
    cases (hc.A_map_code hcγ).not_is_even even₁ }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `γ < α`.
TODO: This proof can be golfed quite a bit just by cleaning up the `simp` calls. -/
lemma ext (x y : semitangle α) (h : x.members γ = y.members γ) : x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp only at h,
  refine ext_code _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨δ, even₂, hA₂⟩ := hys,
  { refine (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _,
    simp only [ne.def, Iio_index.bot_ne_coe, not_false_iff, A_map_code_mk_ne,
      repr_code_base, subtype.coe_mk],
    rw [hA₁ γ, h, ← hA₂ γ],
    exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe },
  { simp only [repr_code_base, subtype.coe_mk, repr_code_proper],
    obtain rfl | hδγ := eq_or_ne δ γ,
    { simp only [is_even_bot, mem_Iio, subtype.val_eq_coe, set_coe.forall,
        ne.def, Iio.coe_inj] at *,
      have := hA₁ δ δ.prop,
      rw subtype.coe_eta at this,
      rw [← h, ← this],
      exact code.equiv.A_map_right _ (code.is_even_bot _) _ bot_ne_mk_coe },
    { refine (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _,
      simp only [ne.def, Iio_index.bot_ne_coe, not_false_iff, A_map_code_mk_ne],
      rw [hA₁ γ, h, ←hA₂ γ (Iio.coe_injective.ne hδγ), ← A_map_code_mk_ne],
      exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ) } },
  { simp only [repr_code_proper, subtype.coe_mk, repr_code_base],
    obtain rfl | hβγ := eq_or_ne β γ,
    { dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall] at *,
      rw [h, ←hA₂ β],
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ bot_ne_mk_coe },
    { refine (code.equiv.A_map_right _ even₁ γ $ Iio.coe_injective.ne hβγ).trans _,
      dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall] at *,
      rw A_map_code_mk_ne _ _ (Iio.coe_injective.ne hβγ),
      rw [hA₁ γ (Iio.coe_injective.ne hβγ), h, ←hA₂ γ],
      exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe } },
  { simp only [repr_code_proper, subtype.coe_mk],
    obtain rfl | hβγ := eq_or_ne β γ,
    { obtain rfl | hδβ := eq_or_ne δ β,
      { rw h },
      { have := A_map_code_ne β (code.mk δ (ys δ)) (Iio.coe_injective.ne hδβ),
        dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall, code.snd_mk] at *,
        rw [h, ←hA₂ _ (Iio.coe_injective.ne hδβ), ← code.mk_def, ← this],
        exact code.equiv.A_map_left _ even₂ _ (Iio.coe_injective.ne hδβ) } },
    obtain rfl | hδγ := eq_or_ne δ γ,
    { have := A_map_code_ne δ (code.mk β (xs β)) (Iio.coe_injective.ne hβγ),
      dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall, code.snd_mk] at *,
      simp_rw [←h, ←hA₁ _ (Iio.coe_injective.ne hβγ), ← code.mk_def, ← this],
      exact code.equiv.A_map_right _ even₁ _ (Iio.coe_injective.ne hβγ) },
    refine (code.equiv.A_map_right _ even₁ γ $ Iio.coe_injective.ne hβγ).trans _,
    have := A_map_code_ne γ (code.mk ↑δ (ys δ)) (Iio.coe_injective.ne hδγ),
    dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall, code.snd_mk] at *,
    rw A_map_code_ne,
    rw [code.snd_mk, hA₁ γ (Iio.coe_injective.ne hβγ), h, ←hA₂ γ (Iio.coe_injective.ne hδγ)],
    rw ← this,
    exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ) }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext' (x y : semitangle α) (h : ∀ t : tangle γ, t ∈ₛₜ x ↔ t ∈ₛₜ y) : x = y :=
ext x y $ set.ext h

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all nonempty semitangles have a `-1`-extension.
Therefore, the extensionality principle in this case applies to the `-1`-extensions. -/
lemma ext_zero (x y : semitangle α) (α_zero : is_min α) (h : x.pref.atoms = y.pref.atoms) :
  x = y :=
begin
  obtain ⟨xs, ⟨atoms₁, rep₁, hA₁⟩ | ⟨γ, _, _⟩⟩ := x, swap,
  { cases α_zero.not_lt γ.2 },
  obtain ⟨ys, ⟨atoms₂, rep₂, hA₂⟩ | ⟨γ, _, _⟩⟩ := y, swap,
  { cases α_zero.not_lt γ.2 },
  have : atoms₁ = atoms₂ := h,
  subst this,
  suffices : xs = ys, by subst this,
  ext β -,
  cases α_zero.not_lt β.2,
end


/-- Construct a semitangle from an even nonempty code. -/
def intro (s : set (tangle β)) (heven : (code.mk β s : code α).is_even) : semitangle α :=
⟨extension s, match β, s, heven with
  | ⟨⊥, _⟩, s, _ := preference.base s (code.is_even_bot _) $ λ β, rfl
  | ⟨(γ : Λ), hγ⟩, s, heven := preference.proper ⟨γ, coe_lt_coe.1 hγ⟩
    (by { convert heven, exact extension_self (show set (tangle $ Iio_coe ⟨γ, _⟩), from s) }) $
      λ δ hδ, by { rw extension_ne s δ hδ, congr,
        exact extension_self (show set (tangle $ Iio_coe ⟨γ, _⟩), from s) }
  end⟩

@[simp] lemma exts_intro (s : set (tangle β)) (heven) :
  (intro s heven).members = extension s := rfl

end semitangle

open semitangle

variables [core_tangle_data α]

namespace allowable_perm
variables {f : allowable_perm α} {e : extensions α}

@[simp] lemma smul_extension_apply (f : allowable_perm α) (s : set (tangle β)) :
  f • extension s γ = extension (f • s) γ :=
begin
  by_cases β = γ,
  { subst h,
    simp only [extension_eq, cast_eq], },
  { simp only [extension_ne _ _ h, smul_A_map], },
end

@[simp] lemma smul_extension (f : allowable_perm α) (s : set (tangle β)) :
  f • extension s = extension (f • s) :=
begin
  ext γ : 1,
  rw ← smul_extension_apply,
  refl,
end

lemma smul_aux₁ {s : set (tangle (⊥ : Iio_index α))}
  (h : ∀ (γ : Iio α), A_map bot_ne_coe s = (e γ : set (tangle (Iio_coe γ)))) (γ : Iio α) :
  A_map bot_ne_coe (f • s) = (f • e) γ :=
by simpa only [smul_A_map] using congr_arg (λ c, f • c) (h γ)

lemma smul_aux₂ (h : ∀ (δ : Iio α) (hγδ : Iio_coe γ ≠ δ),
  A_map hγδ (e γ) = (e δ : set (tangle (Iio_coe δ)))) (δ : Iio α) (hγδ : Iio_coe γ ≠ δ) :
  A_map hγδ ((f • e) γ) = (f • e) δ :=
by simpa only [smul_A_map] using congr_arg (λ c, f • c) (h δ hγδ)

/-- Allowable permutations act on nonempty semitangles. -/
noncomputable! instance : has_smul (allowable_perm α) (semitangle α) :=
{ smul := λ f t, ⟨f • t.members, begin
    obtain ⟨members, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩ := t,
    { exact preference.base (f • s) (code.is_even_bot _) (smul_aux₁ h) },
    { exact preference.proper _ ht.smul (smul_aux₂ h) }
    end⟩ }

@[simp] lemma members_smul (f : allowable_perm α) (s : semitangle α) :
  (f • s).members = f • s.members := rfl

@[simp] lemma smul_base (f : allowable_perm α) (e : extensions α) (s ht h) :
  f • (⟨e, preference.base s ht h⟩ : semitangle α) =
    ⟨f • e, preference.base (f • s) (code.is_even_bot _) (smul_aux₁ h)⟩ := rfl

@[simp] lemma smul_proper (f : allowable_perm α) (e : extensions α) (γ ht h) :
  f • (⟨e, preference.proper γ ht h⟩ : semitangle α) =
    ⟨f • e, preference.proper _ ht.smul (smul_aux₂ h)⟩ := rfl

instance mul_action_semitangle : mul_action (allowable_perm α) (semitangle α) := {
  one_smul := begin
    rintro ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩,
    { rw smul_base,
      simp only [one_smul, eq_self_iff_true, true_and],
      refine preference.base_heq_base _ _,
      rw one_smul,
      refl, },
    { rw smul_proper,
      simp only [one_smul, eq_self_iff_true, true_and],
      refine semitangle.preference.proper_heq_proper _ rfl,
      rw one_smul, },
  end,
  mul_smul := begin
    rintro f g ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩,
    { simp only [smul_base, mul_smul, eq_self_iff_true, true_and],
      refine preference.base_heq_base _ _,
      rw mul_smul,
      refl, },
    { simp only [smul_proper, mul_smul, eq_self_iff_true, true_and],
      refine semitangle.preference.proper_heq_proper _ rfl,
      rw mul_smul, },
  end
}

end allowable_perm

variables (α)

/-- A tangle at the new level `α` is a semitangle supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
@[nolint has_nonempty_instance]
def new_tangle := {s : semitangle α // supported α (allowable_perm α) s}

variables {α} {c d : code α} {S : set (support_condition α)}

open mul_action

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected lemma code.equiv.supports (hcd : c ≡ d) (hS : supports (allowable_perm α) S c) :
  supports (allowable_perm α) S d :=
λ f h, (hcd.symm.smul.trans $ (code.equiv.of_eq $ hS f h).trans hcd).unique rfl

lemma code.equiv.supports_iff (hcd : c ≡ d) :
  supports (allowable_perm α) S c ↔ supports (allowable_perm α) S d :=
⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
lemma code.equiv.small_supported_iff (hcd : c ≡ d) :
  supported α (allowable_perm α) c ↔ supported α (allowable_perm α) d :=
⟨λ ⟨⟨s, hs, h⟩⟩, ⟨⟨s, hs, hcd.supports h⟩⟩, λ ⟨⟨s, hs, h⟩⟩, ⟨⟨s, hs, hcd.symm.supports h⟩⟩⟩

@[simp] lemma smul_intro (f : allowable_perm α) (s : set (tangle β)) (hs) :
  f • intro s hs = intro (f • s) hs.smul :=
begin
  cases β,
  induction β_val using with_bot.rec_bot_coe,
  { simp only [intro, allowable_perm.smul_base, allowable_perm.smul_extension,
      eq_self_iff_true, true_and],
    refine preference.base_heq_base _ rfl,
    rw allowable_perm.smul_extension },
  { simp only [intro, allowable_perm.smul_proper, allowable_perm.smul_extension,
      eq_self_iff_true, true_and],
    refine preference.proper_heq_proper _ rfl,
    rw allowable_perm.smul_extension }
end

-- TODO: Move next two lemmas elsewhere.
lemma allowable_to_struct_perm_bot (π : allowable (⊥ : Iio_index α)) :
  core_tangle_data.allowable_to_struct_perm π = struct_perm.to_bot_iso.to_monoid_hom π := rfl

lemma _root_.semiallowable_perm.to_allowable_bot (π : semiallowable_perm α) :
  semiallowable_perm.to_allowable ⊥ π = struct_perm.to_near_litter_perm
    (semiallowable_perm.to_struct_perm π) :=
begin
  unfold semiallowable_perm.to_allowable semiallowable_perm.to_struct_perm
    struct_perm.to_near_litter_perm struct_perm.lower allowable.to_struct_perm,
  rw dif_neg with_bot.bot_ne_coe,
  simp only [monoid_hom.coe_mk, monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom,
    comp_app, struct_perm.of_coe_to_coe, allowable_to_struct_perm_bot, mul_equiv.symm_apply_apply],
  refl,
end

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def new_typed_near_litter (N : near_litter) : new_tangle α :=
⟨intro (show set (tangle (⊥ : Iio_index α)), from N.2.1) $
  code.is_even_bot _, ⟨⟨{(sum.inr N, default)}, small_singleton _, λ π h, begin
    simp only [subtype.val_eq_coe, option.smul_some, smul_intro, option.some_inj],
    have := show (struct_perm.lower (bot_lt_coe α).le (semiallowable_perm.to_struct_perm ↑π)) •
      sum.inr N = sum.inr N, from congr_arg prod.fst (h rfl),
    simp only [sum.smul_inr] at this,
    have : π • N = N := this,
    conv_rhs { rw ← this },
    congr' 1,
    ext : 1,
    simp only [coe_smul_nonempty, subtype.coe_mk, allowable_perm.snd_smul_near_litter],
    unfold has_smul.smul has_smul.comp.smul,
    simp only [semiallowable_perm.to_allowable_bot (allowable_perm.coe_hom π)],
  end⟩⟩⟩

/-- For any supported tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def supported_singleton (x : tangle β) (supp : supported α (allowable_perm α) x) :
  new_tangle α :=
⟨intro {x} (code.is_even_singleton _), begin
  unfreezingI { obtain ⟨s, hs₁, hs₂⟩ := supp },
  refine ⟨⟨s, hs₁, λ π h, _⟩⟩,
  conv_rhs { rw ← hs₂ π h },
  simp only [smul_set_singleton, smul_nonempty_mk, option.smul_some, smul_intro],
end⟩

/-- For any small set `B` of supported `β`-tangles, the code `(α, β, B)` is a tangle at level `α` if
it is even. -/
def supported_set (s : set (tangle β)) (hs : small s) (hc : (mk β s).is_even)
  (symm : ∀ b ∈ s, supported α (allowable_perm α) b) :
  new_tangle α :=
⟨intro s hc, begin
  have symm : Π b ∈ s, support α (allowable_perm α) b,
  { intros b hb, exact (symm b hb).some },
  refine ⟨⟨⋃ b ∈ s, symm b ‹_›, hs.bUnion (λ i hi, (symm _ _).small), λ π h, _⟩⟩,
  suffices : π • s = s,
  { simp only [option.smul_some, smul_intro, option.some_inj, this] },
  have : ∀ x ∈ s, π • x = x,
  { intros x hx,
    refine (symm x hx).supports π _,
    intros a ha,
    refine h _,
    simp only [mem_Union, set_like.mem_coe],
    refine ⟨x, hx, ha⟩ },
  ext : 2,
  refine ⟨λ hx, _, λ hx, _⟩,
  { have := this (π⁻¹ • x) _,
    { rw smul_inv_smul at this,
      rw this,
      rwa ←mem_smul_set_iff_inv_smul_mem },
    { rwa ←mem_smul_set_iff_inv_smul_mem } },
  { rw ← this x hx,
    exact smul_mem_smul_set hx }
end⟩

variables {α}

namespace new_tangle

instance : has_coe (new_tangle α) (semitangle α) := coe_subtype

lemma coe_injective : injective (coe : new_tangle α → semitangle α) := subtype.coe_injective

end new_tangle

namespace allowable_perm

/-- Allowable permutations act on `α`-tangles. -/
--Yaël: I suspect we can generalize `supports.smul` so that it applies here
instance has_smul_new_tangle : has_smul (allowable_perm α) (new_tangle α) :=
⟨λ π t, ⟨π • t, t.2.map $ λ s, { carrier := π • s, small := s.2.image, supports := begin
  intros σ h,
  have := s.supports (π⁻¹ * σ * π) _,
  { conv_rhs { rw [← subtype.val_eq_coe, ← this, ← mul_smul, ← mul_assoc, ← mul_assoc,
      mul_inv_self, one_mul, mul_smul] },
    refl },
  { intros a ha,
    rw [mul_smul, mul_smul, inv_smul_eq_iff],
    exact h (smul_mem_smul_set ha) },
end }⟩⟩

@[simp, norm_cast] lemma coe_smul_new_tangle (f : allowable_perm α) (t : new_tangle α) :
  (↑(f • t) : semitangle α) = f • t := rfl

instance mul_action_new_tangle : mul_action (allowable_perm α) (new_tangle α) :=
new_tangle.coe_injective.mul_action _ coe_smul_new_tangle

end allowable_perm

end con_nf
