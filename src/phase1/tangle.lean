import group_theory.group_action.option
import mathlib.group_action
import mathlib.pointwise
import phase1.allowable

noncomputable theory

open function set with_bot
open_locale cardinal pointwise

universe u

namespace con_nf
variables [params.{u}]

open code

/-
/-- A pretangle has a preferred extension, which is either a proper type `β : Λ`,
or the base type `-1`. A pretangle has a `-1`-extension if and only if its preferred extension
is the `-1`-extension. -/
inductive preferred_extension (α : Λ) : Type u
| proper_extension : Π (β < α), preferred_extension
| base_extension : set atom → preferred_extension
-/

variables (α : Λ) [core_tangle_cumul α] {β : Iio_index α} {γ : Iio α}

namespace semitangle

/-- The possible extensions of a nonempty semitangle. -/
abbreviation extension := Π β : Iio α, tangles (β : Iio_index α)

namespace extension
variables {α} [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- The extensions for a code. -/
protected def A_map (s : tangles β) : extension α :=
λ γ, if hγβ : ↑γ = β then by { subst hγβ, exact s } else ⟨A_map γ _, s.2.A_map⟩

@[simp] lemma A_map_self (s : tangles $ Iio_coe γ) : extension.A_map s γ = s :=
dif_pos rfl

lemma A_map_of_ne (s : tangles β) (hγβ : ↑γ ≠ β) : extension.A_map s γ = ⟨A_map γ _, s.2.A_map⟩ :=
dif_neg hγβ

end extension

variables [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
@[nolint has_nonempty_instance] inductive preference (exts : extension α)
| base (atoms : tangles ⊥) :
    (mk ⊥ (atoms : set $ tangle (⊥ : Iio_index α))).is_even →
      (∀ γ, A_map γ (atoms : set $ tangle (⊥ : Iio_index α)) = (exts γ).val) → preference
| proper (β : Iio α) :
    (mk β (show tangles $ Iio_coe β, from exts β) : code α).is_even →
      (∀ γ, β ≠ γ →
        A_map γ (show set (tangle $ Iio_coe β), from (exts β).val) = (exts γ).val) →
          preference

variables {α} {members : extension α}

/-- The `-1`-extension associated with a given semitangle extension. -/
def preference.atoms : preference α members → set atom
| (preference.base atoms _ _) := (atoms : set (tangle ⊥))
| (preference.proper _ _ _) := ∅

end semitangle

open semitangle

variables [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`.

Here, we restrict our definition to just nonempty semitangles; this simplifies the definition. -/
@[nolint has_nonempty_instance]
structure nonempty_semitangle :=
(exts : extension α)
(pref : preference α exts)

namespace nonempty_semitangle
variables {α}

/-- The membership relation for nonempty semitangles. -/
def mem (t : tangle γ) (s : nonempty_semitangle α) : Prop := t ∈ (s.exts γ).val

notation t ` ∈ₙₛₜ `:50 s:50 := mem t s

/-- The even code associated to a nonempty semitangle. -/
def repr_code : nonempty_semitangle α → nonempty_code α
| ⟨exts, preference.base atoms rep hA⟩ := ⟨⟨⊥, atoms⟩, atoms.2⟩
| ⟨exts, preference.proper β rep hA⟩ := ⟨⟨β, show tangles $ Iio_coe β, from exts β⟩, (exts β).2⟩

@[simp] lemma repr_code_base (exts : extension α) (atoms rep hA) :
  repr_code ⟨exts, preference.base atoms rep hA⟩ = ⟨⟨⊥, atoms⟩, atoms.2⟩ := rfl

@[simp] lemma repr_code_proper (exts : extension α) (β rep hA) :
  repr_code ⟨exts, preference.proper β rep hA⟩ =
    ⟨⟨β, show tangles $ Iio_coe β, from exts β⟩, (exts β).2⟩ := rfl

lemma repr_code_spec : Π (s : nonempty_semitangle α), (repr_code s : code α).is_even
| ⟨exts, preference.proper β rep hA⟩ := rep
| ⟨exts, preference.base atoms rep hA⟩ := rep

lemma repr_code_members_ne :
  Π (s : nonempty_semitangle α) (γ : Iio α) (hcγ : (repr_code s : code α).1 ≠ γ),
  (A_map_code γ (repr_code s)).2 = (s.exts γ : set (tangle $ Iio_coe γ))
| ⟨exts, preference.proper β rep hA⟩ γ hcγ := hA _ $ ne_of_apply_ne coe hcγ
| ⟨exts, preference.base atoms rep hA⟩ γ hcγ := hA _

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
lemma ext_core (x y : nonempty_semitangle α) : (∃ γ, γ < α) → x.exts = y.exts → x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp,
  rintro ⟨γ, hγ⟩ rfl,
  have γ : Iio α := ⟨γ, hγ⟩,
  refine congr_arg (λ h, ⟨xs, h⟩) _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨γ, even₂, hA₂⟩ := hys,
  { simp_rw subtype.coe_injective (A_map_injective $ (hA₁ γ).trans (hA₂ _).symm) },
  { cases even₁.A_map_code_ne even₂  bot_ne_mk_coe (sigma.ext_iff.2 ⟨rfl, (hA₁ γ).heq⟩) },
  { cases even₂.A_map_code_ne even₁ bot_ne_mk_coe (sigma.ext_iff.2 ⟨rfl, (hA₂ β).heq⟩) },
  { simp only,
    exact not_ne_iff.1 (λ hβγ, even₂.A_map_code_ne even₁ (Iio.coe_injective.ne hβγ.symm) $
      sigma.ext_iff.2 ⟨rfl, (hA₂ β hβγ.symm).heq⟩) }
end

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
lemma ext_code : ∀ {x y : nonempty_semitangle α}, (repr_code x : code α) ≡ repr_code y → x = y
| ⟨x, preference.base atoms₁ even₁ hA₁⟩ ⟨y, preference.base atoms₂ even₂ hA₂⟩ h := begin
  obtain rfl := subtype.coe_injective (code.equiv.bot_bot_iff.1 h),
  obtain rfl : x = y := funext (λ γ, subtype.coe_injective $ (hA₁ _).symm.trans $ hA₂ _),
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
    refine funext (λ ε, subtype.coe_injective _),
    obtain rfl | hδε := eq_or_ne δ ε,
    { exact h.eq.symm },
    refine (hA₁ _ hδε).symm.trans (eq.trans _ $ hA₂ _ hδε),
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
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext (x y : nonempty_semitangle α) (h : x.exts γ = y.exts γ) : x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp only at h,
  refine ext_code _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨δ, even₂, hA₂⟩ := hys,
  { refine (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _,
    dsimp,
    rw [hA₁ γ, h, ←hA₂ γ],
    exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe },
  { dsimp,
    obtain rfl | hδγ := eq_or_ne δ γ,
    { dsimp at *,
      simp_rw [←h, ←hA₁ δ],
      exact code.equiv.A_map_right _ (code.is_even_bot _) _ bot_ne_mk_coe },
    { refine (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _,
      dsimp,
      rw [hA₁ γ, h, ←hA₂ γ hδγ],
      exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ) } },
  { dsimp,
    obtain rfl | hβγ := eq_or_ne β γ,
    { dsimp at *,
      rw [h, ←hA₂ β],
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ bot_ne_mk_coe },
    { refine (code.equiv.A_map_right _ even₁ γ $ Iio.coe_injective.ne hβγ).trans _,
      dsimp at *,
      rw [hA₁ γ hβγ, h, ←hA₂ γ],
      exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe } },
  { dsimp,
    obtain rfl | hβγ := eq_or_ne β γ,
    { obtain rfl | hδβ := eq_or_ne δ β,
      { rw h },
      { dsimp at *,
        simp_rw [h, ←hA₂ _ hδβ],
        exact code.equiv.A_map_left _ even₂ _ (Iio.coe_injective.ne hδβ) } },
    sorry --timeout
    -- obtain rfl | hδγ := eq_or_ne δ γ,
    -- { dsimp,
    --   simp_rw [←h, ←hA₁ _ hβγ],
    --   exact code.equiv.A_map_right _ even₁ _ (Iio.coe_injective.ne hβγ) },
    -- refine (code.equiv.A_map_right _ even₁ γ $ Iio.coe_injective.ne hβγ).trans _,
    -- dsimp,
    -- rw [hA₁ γ hβγ, h, ←hA₂ γ hδγ],
    -- exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ)
    }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext' (x y : nonempty_semitangle α) (h : ∀ t : tangle γ, t ∈ₙₛₜ x ↔ t ∈ₙₛₜ y) : x = y :=
ext x y $ subtype.ext $ set.ext h

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all nonempty semitangles have a `-1`-extension.
Therefore, the extensionality principle in this case applies to the `-1`-extensions. -/
lemma ext_zero (x y : nonempty_semitangle α) (α_zero : is_min α) (h : x.pref.atoms = y.pref.atoms) :
  x = y :=
begin
  obtain ⟨xs, ⟨atoms₁, rep₁, hA₁⟩ | ⟨γ, _, _⟩⟩ := x, swap,
  { cases α_zero.not_lt γ.2 },
  obtain ⟨ys, ⟨atoms₂, rep₂, hA₂⟩ | ⟨γ, _, _⟩⟩ := y, swap,
  { cases α_zero.not_lt γ.2 },
  have : atoms₁ = atoms₂ := subtype.coe_injective h,
  subst this,
  suffices : xs = ys, by subst this,
  ext β -,
  cases α_zero.not_lt β.2,
end

end nonempty_semitangle

/-- A semitangle is either a nonempty semitangle, or the `⊥` element, which is considered the empty
set. Note that in TTT, a set contains no elements at one level if and only if it contains no
elements at all levels. -/
@[reducible] def semitangle := with_bot (nonempty_semitangle α)

variables {α}

namespace semitangle

/-- The membership relation of tangles and semitangles in TTT at this level. -/
def mem (t : tangle γ) (s : semitangle α) := s.elim false $ (∈ₙₛₜ) t

notation t ` ∈ₛₜ `:50 s:50 := mem t s

variables {t : tangle γ} {s : semitangle α}

lemma not_mem_bot (t : tangle γ) : ¬ t ∈ₛₜ ⊥ := id
@[simp] lemma mem_coe {s : nonempty_semitangle α} : t ∈ₛₜ s ↔ t ∈ₙₛₜ s := iff.rfl

lemma eq_bot_of_forall_not_mem (s : semitangle α) (h : ∀ t : tangle γ, ¬ t ∈ₛₜ s) : s = ⊥ :=
begin
  cases s,
  { refl },
  { cases h _ (s.exts _).2.some_spec }
end

lemma ext (x y : semitangle α) : (∀ t : tangle γ, t ∈ₛₜ x ↔ t ∈ₛₜ y) → x = y :=
begin
  intro h,
  cases x,
  { exact (eq_bot_of_forall_not_mem _ $ λ _, (h _).2).symm },
  cases y,
  { exact eq_bot_of_forall_not_mem _ (λ _, (h _).1) },
  rw nonempty_semitangle.ext' x y h,
end

/-- Construct a nonempty semitangle from an even nonempty code. -/
def intro (s : tangles β) (heven : (code.mk β s : code α).is_even) : nonempty_semitangle α :=
⟨extension.A_map s, match β, s, heven with
  | ⟨⊥, _⟩, s, _ := preference.base s (code.is_even_bot _) $ λ β, rfl
  | ⟨(β : Λ), hβ⟩, s, heven := preference.proper ⟨β, coe_lt_coe.1 hβ⟩
    (by { convert heven, exact extension.A_map_self _ }) $ λ β hβγ,
      by { rw extension.A_map_of_ne _ (Iio.coe_injective.ne hβγ.symm), congr,
        exact extension.A_map_self _ }
  end⟩

@[simp] lemma exts_intro (s : tangles β) (heven) : (intro s heven).exts = extension.A_map s := rfl

end semitangle

open semitangle

variables [core_tangle_data α]

namespace allowable_perm
variables {f : allowable_perm α} {e : extension α}

lemma smul_extension_A_map (f : allowable_perm α) (s : tangles β) :
  f • extension.A_map s = extension.A_map (f • s) :=
begin
  funext β,
  dsimp [extension.A_map],
  split_ifs,
  { subst h },
  rw ← subtype.coe_inj,
  simp only [smul_nonempty_mk, subtype.coe_mk],
  exact smul_A_map _ _ (ne.symm h),
end

lemma smul_aux₁ {s : set $ tangle (⊥ : Iio_index α)} (h : ∀ γ, A_map γ s = e γ) (γ) :
  A_map γ (f • s) = f • e γ :=
by rw [←h γ, smul_A_map _ _ bot_ne_mk_coe]

lemma smul_aux₂ (h : ∀ δ, γ ≠ δ → A_map δ (e γ : set $ tangle $ Iio_coe γ) = ↑(e δ))
  (δ) (hγδ : γ ≠ δ) :
  A_map δ (f • (e γ : set $ tangle $ Iio_coe γ)) = f • ↑(e δ) :=
by rw [←smul_A_map _ _ (Iio.coe_injective.ne hγδ), h _ hγδ]

/-- Allowable permutations act on nonempty semitangles. -/
instance mul_action_nonempty_semitangle : mul_action (allowable_perm α) (nonempty_semitangle α) :=
{ smul := λ f t, ⟨f • t.exts, begin
    obtain ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩ := t,
    { exact preference.base (f • s) (code.is_even_bot _) sorry }, -- (smul_aux₁ h)
    { exact preference.proper _ ht.smul sorry } -- (smul_aux₂ h)
    end⟩,
  one_smul := begin
    rintro ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩; sorry
  end,
  mul_smul := begin
    rintro f g ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩; sorry
  end }

@[simp] lemma members_smul (f : allowable_perm α) (s : nonempty_semitangle α) :
  (f • s).exts = f • s.exts := rfl

@[simp] lemma smul_base (f : allowable_perm α) (e : extension α) (s ht h) :
  f • (⟨e, preference.base s ht h⟩ : nonempty_semitangle α) =
    ⟨f • e, preference.base (f • s) (code.is_even_bot _) $ sorry⟩ := rfl -- smul_aux₁ h

@[simp] lemma smul_proper (f : allowable_perm α) (e : extension α) (γ ht h) :
  f • (⟨e, preference.proper γ ht h⟩ : nonempty_semitangle α) =
    ⟨f • e, preference.proper _ ht.smul $ smul_aux₂ h⟩ := rfl

/-- Allowable permutations act on semitangles. -/
instance mul_action_semitangle : mul_action (allowable_perm α) (semitangle α) := option.mul_action

end allowable_perm

variables (α)

/-- A tangle at the new level `α` is a semitangle supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
@[nolint has_nonempty_instance]
def new_tangle := {s : semitangle α // small_supported α (allowable_perm α) s}

variables {α} {c d : code α} {S : set (support_condition α)}

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected lemma code.equiv.supports (hcd : c ≡ d) (hS : supports (allowable_perm α) S c) :
  supports (allowable_perm α) S d :=
λ f h, (hcd.symm.smul.trans $ (code.equiv.of_eq $ hS f h).trans hcd).unique rfl

lemma code.equiv.supports_iff (hcd : c ≡ d) :
  supports (allowable_perm α) S c ↔ supports (allowable_perm α) S d :=
⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
lemma code.equiv.small_supported_iff (hcd : c ≡ d) :
  small_supported α (allowable_perm α) c ↔ small_supported α (allowable_perm α) d :=
⟨λ ⟨⟨⟨s, h⟩, hs⟩⟩, ⟨⟨⟨s, hcd.supports h⟩, hs⟩⟩, λ ⟨⟨⟨s, h⟩, hs⟩⟩, ⟨⟨⟨s, hcd.symm.supports h⟩, hs⟩⟩⟩

@[simp] lemma smul_intro (f : allowable_perm α) (s : tangles $ Iio_coe γ) (hs) :
  f • intro s hs = intro (f • s) (by cases γ; exact hs.smul) :=
begin
  sorry
  -- induction γ using with_bot.rec_bot_coe,
  -- { dsimp [intro],
  --   -- simp_rw f.smul_extension_A_map,
  --   sorry },
  -- { dsimp [intro],
  --   -- simp_rw f.smul_extension_A_map,
  --   sorry }
end

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def typed_near_litter (N : near_litter) : new_tangle α :=
⟨some $ intro ⟨(show set (tangle (⊥ : Iio_index α)), from N.2.1), N.2.2.nonempty⟩ $
  code.is_even_bot _, ⟨⟨⟨{(sum.inr N, default)}, λ f h, begin
  dsimp at ⊢ h,
  -- rw smul_intro,
  -- have := congr_arg prod.fst (h _ rfl),
  -- have := sum.inr_injective this,
  -- conv { to_rhs, rw ←this },
  -- dsimp,
  -- congr',
  sorry
end⟩, small_singleton _⟩⟩⟩

/-- For any small-supported tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def small_supported_singleton (x : tangle β) (supp : small_supported α (allowable_perm α) x) :
  new_tangle α :=
⟨some $ intro ⟨{x}, singleton_nonempty _⟩ (code.is_even_singleton _), sorry⟩

/-- For any small set `B` of small-supported `β`-tangles,
the code `(α, β, B)` is a tangle at level `α`. -/
def small_supported_set (s : tangles β) (hs : small (s : set $ tangle β))
  (symm : ∀ b ∈ (s : set $ tangle β), small_supported α (allowable_perm α) b) :
  new_tangle α :=
⟨some $ intro s sorry, sorry⟩

variables {α}

namespace new_tangle

instance : has_coe (new_tangle α) (semitangle α) := coe_subtype

lemma coe_injective : injective (coe : new_tangle α → semitangle α) := subtype.coe_injective

end new_tangle

namespace allowable_perm

/-- Allowable permutations act on `α`-tangles. -/
--Yaël: I suspect we can generalize `supports.smul` so that it applies here
instance has_smul_new_tangle : has_smul (allowable_perm α) (new_tangle α) :=
⟨λ π t, ⟨π • t, t.2.map $ λ s, { carrier := π • s, supports := sorry, small := s.2.image }⟩⟩

@[simp, norm_cast] lemma coe_smul_new_tangle (f : allowable_perm α) (t : new_tangle α) :
  (↑(f • t) : semitangle α) = f • t := rfl

instance mul_action_new_tangle : mul_action (allowable_perm α) (new_tangle α) :=
new_tangle.coe_injective.mul_action _ coe_smul_new_tangle

end allowable_perm

/-
namespace nonempty_semitangle

def to_pretangle (t : nonempty_semitangle α) : pretangle α :=
pretangle.mk t.pref.atoms (λ β hβ, pretangle_inj β hβ ''
  (t.exts β hβ : set (tangle α β $ coe_lt_coe.mpr hβ)))

lemma to_pretangle_ne_empty (t : nonempty_semitangle α) :
  to_pretangle α t ≠ pretangle.mk ∅ (λ β hβ, ∅) :=
begin
  by_cases hzero : ∃ β, β < α,
  { obtain ⟨β, hβ⟩ := hzero,
    intro h,
    have := congr_arg pretangle.extension h,
    rw pretangle.extension_mk at this,
    have := congr_fun₂ this β hβ,
    rw [to_pretangle, pretangle.extension_mk, set.image_eq_empty] at this,
    exact (t.exts β hβ).property.ne_empty this },
  { intro h,
    have := congr_arg pretangle.atom_extension h,
    rw [to_pretangle, pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    obtain ⟨ts, ⟨atoms, rep, hA⟩ | ⟨β, hβ, rep, hA⟩⟩ := t,
    { exact atoms.2.ne_empty this },
    { exfalso, exact hzero ⟨β, hβ⟩ } }
end

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst, unfold to_pretangle at hst,
  by_cases h : is_min α,
  { have := congr_arg pretangle.atom_extension hst,
    rw [pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    exact ext_zero _ _ h this },
  { obtain ⟨β, hβ⟩ := not_is_min_iff.1 h,
    have := congr_arg pretangle.extension hst,
    rw [pretangle.extension_mk, pretangle.extension_mk] at this,
    have := congr_fun₂ this β hβ,
    rw set.image_eq_image (embedding.injective _) at this,
    exact ext _ _ _ (subtype.coe_inj.mp this) }
end

end nonempty_semitangle

namespace semitangle

def to_pretangle : semitangle α → pretangle α
| ⊥ := pretangle.mk ∅ (λ β hβ, ∅)
| (t : nonempty_semitangle α) := nonempty_semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst,
  induction s using with_bot.rec_bot_coe; induction t using with_bot.rec_bot_coe,
  { refl },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst.symm },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst },
  { rw nonempty_semitangle.to_pretangle_injective α hst }
end

end semitangle

namespace new_tangle

def to_pretangle (t : new_tangle α) : pretangle α := semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
λ s t hst, subtype.coe_inj.mp (semitangle.to_pretangle_injective α hst)

end new_tangle
-/
end con_nf
