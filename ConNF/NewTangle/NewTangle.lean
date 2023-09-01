import Mathlib.GroupTheory.GroupAction.Option
import ConNF.Mathlib.GroupAction
import ConNF.Mathlib.Pointwise
import ConNF.NewTangle.NewAllowable

/-!
# Construction of tangles

In this file, we construct the type of tangles at level `α`, assuming they exist at all levels
`β < α`.

## Main declarations

* `ConNF.Extensions`: The type of extensions of an `α`-tangle.
* `ConNF.Preference`: A preferred extension of a semitangle.
* `ConNF.Semitangle`: An extension for each `β < α`, with one chosen as its preferred extension.
    The non-preferred extensions can be derived from the preferred extension.
* `ConNF.NewAllowable.mulActionSemitangle`: Allowable permutations act on semitangles.
* `ConNF.NewTangle`: The type of tangles at level `α`.
* `ConNF.Allowableperm.mulActionNewTangle`: Allowable permutations act on tangles.
-/

open Function Set WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] [BasePositions]

open Code IioBot

variable (α : Λ) [TangleDataIio α] {β : IioBot α} {γ : Iio α}

abbrev Extensions :=
  ∀ β : Iio α, Set (Tangle β)

namespace Semitangle

variable [PositionedTanglesIio α] [TypedObjectsIio α]

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. In particular, each non-preferred extension can be
obtained by applying the `cloud` map to the preferred extension. -/
inductive Preference (members : Extensions α)
  | base (atoms : Set (Tangle (⊥ : IioBot α))) :
    (∀ γ, cloud bot_ne_coe atoms = members γ) → Preference members
  | proper (β : Iio α) :
    (mk β (members β) : Code α).IsEven →
    (∀ (γ : Iio α) (hβγ : iioCoe β ≠ γ), cloud hβγ (members β) = members γ) →
    Preference members

variable {α}
variable {members : Extensions α}

/-- The `⊥`-extension associated with a given semitangle extension. -/
def Preference.atoms : Preference α members → Set Atom
  | Preference.base atoms _ => (atoms : Set (Tangle ⊥))
  | Preference.proper _ _ _ => ∅

theorem Preference.base_heq_base {m₁ m₂ : Extensions α} {s₁ s₂ h₁ h₂} (hm : m₁ = m₂)
    (hs : s₁ = s₂) :
    HEq (Preference.base s₁ h₁ : Preference α m₁) (Preference.base s₂ h₂ : Preference α m₂) := by
  cases hm
  cases hs
  rfl

theorem Preference.proper_heq_proper {m₁ m₂ : Extensions α} {β₁ β₂ h₁ h₂ h₃ h₄}
    (hm : m₁ = m₂) (hs : β₁ = β₂) :
    HEq (Preference.proper β₁ h₁ h₂ : Preference α m₁)
      (Preference.proper β₂ h₃ h₄ : Preference α m₂) := by
  cases hm
  cases hs
  rfl

end Semitangle

open Semitangle

variable [PositionedTanglesIio α] [TypedObjectsIio α]

/-- A *semitangle* is a collection of `β`-tangles for each lower level `β < α`, together with
a preference for one of these extensions. -/
structure Semitangle where
  members : Extensions α
  pref : Preference α members

variable {α}

namespace Semitangle

/-- The even code associated to a semitangle. -/
def reprCode : Semitangle α → Code α
  | ⟨_, Preference.base atoms _⟩ => ⟨⊥, atoms⟩
  | ⟨exts, Preference.proper β _ _⟩ => ⟨β, exts β⟩

@[simp]
theorem reprCode_base (exts : Extensions α) (atoms hA) :
    reprCode ⟨exts, Preference.base atoms hA⟩ = ⟨⊥, atoms⟩ :=
  rfl

@[simp]
theorem reprCode_proper (exts : Extensions α) (β rep hA) :
    reprCode ⟨exts, Preference.proper β rep hA⟩ = ⟨β, exts β⟩ :=
  rfl

theorem reprCodeSpec : ∀ t : Semitangle α, (reprCode t : Code α).IsEven
  | ⟨_, Preference.proper _ rep _⟩ => rep
  | ⟨_, Preference.base _ _⟩ => isEven_bot _

theorem reprCode_members_ne :
    ∀ (t : Semitangle α) (γ : Iio α) (_ : (reprCode t : Code α).1 ≠ γ),
      (cloudCode γ (reprCode t)).2 = t.members γ
  | ⟨exts, Preference.proper β rep hA⟩, γ, hcγ => by
      rw [snd_cloudCode]
      exact hA _ hcγ
  | ⟨_, Preference.base _ hA⟩, γ, _ => hA _

/-- One form of extensionality: If there is a proper type index `γ < α`, then two semitangles
with the same elements have the same preference.

Remark: This formulation of extensionality holds only for types larger than type zero, since
it doesn't take into account any `⊥`-extension. -/
theorem ext_core (t₁ t₂ : Semitangle α) : (∃ γ, γ < α) → t₁.members = t₂.members → t₁ = t₂ := by
  obtain ⟨xs, hxs⟩ := t₁
  obtain ⟨ys, hys⟩ := t₂
  rintro ⟨γ, hγ⟩ rfl
  simp only [mk.injEq, heq_eq_eq, true_and]
  have γ : Iio α := ⟨γ, hγ⟩
  obtain ⟨atoms₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs <;>
  obtain ⟨atoms₂, hA₂⟩ | ⟨γ, even₂, hA₂⟩ := hys
  · simp_rw [cloud_injective ((hA₁ γ).trans (hA₂ _).symm)]
  · cases (isEven_bot _).cloudCode_ne even₂ bot_ne_mk_coe (Sigma.ext_iff.2 ⟨rfl, (hA₁ γ).heq⟩)
  · cases (isEven_bot _).cloudCode_ne even₁ bot_ne_mk_coe (Sigma.ext_iff.2 ⟨rfl, (hA₂ β).heq⟩)
  · simp only [Preference.proper.injEq]
    refine not_ne_iff.1 fun hβγ =>
      even₂.cloudCode_ne even₁ (Iio.coe_injective.ne hβγ.symm) <|
        Sigma.ext_iff.2 ⟨rfl, heq_of_eq ?_⟩
    rw [snd_cloudCode]
    exact hA₂ β fun h => hβγ.symm (Iio.coe_injective h)

/-- One useful form of extensionality in tangled type theory. Two semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
theorem ext_code : ∀ {t₁ t₂ : Semitangle α}, reprCode t₁ ≡ reprCode t₂ → t₁ = t₂
  | ⟨e₁, Preference.base atoms₁ hA₁⟩, ⟨e₂, Preference.base atoms₂ hA₂⟩, h => by
    obtain rfl := Code.Equiv.bot_bot_iff.1 h
    obtain rfl : e₁ = e₂ := funext fun γ => (hA₁ _).symm.trans <| hA₂ _
    rfl
  | ⟨e₁, Preference.base s hA₁⟩, ⟨e₂, Preference.proper γ even₂ hA₂⟩, h => by
    change Code.mk _ _ ≡ Code.mk _ _ at h
    obtain ⟨δ, hδ⟩ :=
      (Code.Equiv.bot_left_iff.1 h).resolve_left (ne_of_apply_ne Sigma.fst bot_ne_mk_coe)
    rw [hδ] at even₂
    cases even₂.not_isOdd ((isEven_bot _).cloudCode bot_ne_mk_coe)
  | ⟨e₁, Preference.proper γ even₁ hA₁⟩, ⟨e₂, Preference.base s hA₂⟩, h => by
    change Code.mk _ _ ≡ Code.mk _ _ at h
    obtain ⟨δ, hδ⟩ :=
      (Code.Equiv.bot_right_iff.1 h).resolve_left (ne_of_apply_ne Sigma.fst mk_coe_ne_bot)
    rw [hδ] at even₁
    cases even₁.not_isOdd ((isEven_bot _).cloudCode bot_ne_mk_coe)
  | ⟨e₁, Preference.proper γ even₁ hA₁⟩, ⟨e₂, Preference.proper δ even₂ hA₂⟩, h => by
    dsimp at h
    simp only [Equiv_iff, WithBot.coe_ne_bot, ne_eq, Subtype.mk.injEq, coe_inj, Subtype.coe_inj,
      Subtype.exists, mem_Iio] at h
    obtain h | ⟨_, γ, _, hδγ, h⟩ | ⟨_, δ, _, hγδ, h⟩ |
      ⟨c, hc, γ, hcγ, hc', δ, hcδ, h⟩ := h
    · rw [Sigma.ext_iff] at h
      simp only [Subtype.mk.injEq, coe_inj, Subtype.coe_inj] at h
      obtain rfl := h.1
      suffices e₁ = e₂ by subst this; rfl
      refine' funext fun ε => _
      obtain rfl | hδε := eq_or_ne δ ε
      · exact eq_of_heq h.2.symm
      refine (hA₁ _ fun h => hδε (Iio.coe_injective h)).symm.trans
          (Eq.trans ?_ <| hA₂ _ fun h => hδε (Iio.coe_injective h))
      rw [eq_of_heq h.2]
    · rw [Sigma.ext_iff] at h
      simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, ne_eq] at h
      obtain rfl := h.1
      rw [eq_of_heq h.2] at even₁
      cases (even₂.cloudCode <| Iio.coe_injective.ne hδγ).not_isEven even₁
    · rw [Sigma.ext_iff] at h
      simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, ne_eq] at h
      obtain rfl := h.1
      rw [eq_of_heq h.2] at even₂
      cases (even₁.cloudCode <| Iio.coe_injective.ne hγδ).not_isEven even₂
    · rw [Sigma.ext_iff] at h
      simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, ne_eq] at h
      obtain rfl := h.2.1.1
      rw [eq_of_heq h.2.1.2] at even₁
      cases (hc.cloudCode hc').not_isEven even₁

/-- Extensionality in tangled type theory. Two semitangles are equal if their
`β`-extensions are equal for *any* choice of `γ < α`.
TODO: This proof can be golfed quite a bit just by cleaning up the `simp` calls. -/
theorem ext (t₁ t₂ : Semitangle α) (h : t₁.members γ = t₂.members γ) : t₁ = t₂ := by
  obtain ⟨xs, hxs⟩ := t₁
  obtain ⟨ys, hys⟩ := t₂
  dsimp only at h
  refine ext_code ?_
  obtain ⟨atoms₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs <;> obtain ⟨atoms₂, hA₂⟩ | ⟨δ, even₂, hA₂⟩ := hys
  · refine (Code.Equiv.cloud_right _ (Code.isEven_bot _) γ bot_ne_mk_coe).trans ?_
    simp only [Ne.def, IioBot.bot_ne_coe, not_false_iff, cloudCode_mk_ne, reprCode_base,
      Subtype.coe_mk]
    rw [hA₁ γ, h, ← hA₂ γ]
    exact Code.Equiv.cloud_left _ (Code.isEven_bot _) γ bot_ne_mk_coe
  · simp only [reprCode_base, Subtype.coe_mk, reprCode_proper]
    obtain rfl | hδγ := eq_or_ne δ γ
    · simp only [isEven_bot, mem_Iio, SetCoe.forall, Ne.def, Iio.coe_inj] at *
      have := hA₁ δ δ.prop
      rw [Subtype.coe_eta] at this
      rw [← h, ← this]
      exact Code.Equiv.cloud_right _ (Code.isEven_bot _) _ bot_ne_mk_coe
    · refine (Code.Equiv.cloud_right _ (Code.isEven_bot _) γ bot_ne_mk_coe).trans ?_
      simp only [Ne.def, IioBot.bot_ne_coe, not_false_iff, cloudCode_mk_ne]
      rw [hA₁ γ, h, ← hA₂ γ (Iio.coe_injective.ne hδγ), ← cloudCode_mk_ne]
      exact Code.Equiv.cloud_left _ even₂ γ (Iio.coe_injective.ne hδγ)
  · simp only [reprCode_proper, Subtype.coe_mk, reprCode_base]
    obtain rfl | hβγ := eq_or_ne β γ
    · dsimp only [mem_Iio, Ne.def, SetCoe.forall] at *
      rw [h, ← hA₂ β]
      exact Code.Equiv.cloud_left _ (Code.isEven_bot _) _ bot_ne_mk_coe
    · refine (Code.Equiv.cloud_right _ even₁ γ <| Iio.coe_injective.ne hβγ).trans ?_
      dsimp only [mem_Iio, Ne.def, SetCoe.forall] at *
      refine (Code.Equiv.of_eq <| cloudCode_mk_ne _ _ (Iio.coe_injective.ne hβγ) (xs β)).trans ?_
      rw [hA₁ γ (Iio.coe_injective.ne hβγ), h, ← hA₂ γ]
      exact Code.Equiv.cloud_left _ (Code.isEven_bot _) γ bot_ne_mk_coe
  · simp only [reprCode_proper, Subtype.coe_mk]
    obtain rfl | hβγ := eq_or_ne β γ
    · obtain rfl | hδβ := eq_or_ne δ β
      · rw [h]
      · have := cloudCode_ne β (Code.mk δ (ys δ)) (Iio.coe_injective.ne hδβ)
        dsimp only [mem_Iio, Ne.def, SetCoe.forall, Code.snd_mk] at *
        rw [h, ← hA₂ _ (Iio.coe_injective.ne hδβ), ← Code.mk_def, ← this]
        exact Code.Equiv.cloud_left _ even₂ _ (Iio.coe_injective.ne hδβ)
    obtain rfl | hδγ := eq_or_ne δ γ
    · have := cloudCode_ne δ (Code.mk β (xs β)) (Iio.coe_injective.ne hβγ)
      dsimp only [mem_Iio, Ne.def, SetCoe.forall, Code.snd_mk] at *
      simp_rw [← h, ← hA₁ _ (Iio.coe_injective.ne hβγ), ← Code.mk_def, ← this]
      exact Code.Equiv.cloud_right _ even₁ _ (Iio.coe_injective.ne hβγ)
    refine' (Code.Equiv.cloud_right _ even₁ γ <| Iio.coe_injective.ne hβγ).trans _
    have := cloudCode_ne γ (Code.mk (↑δ) (ys δ)) (Iio.coe_injective.ne hδγ)
    dsimp only [mem_Iio, Ne.def, SetCoe.forall, Code.snd_mk] at *
    rw [cloudCode_ne]
    rw [Code.snd_mk, hA₁ γ (Iio.coe_injective.ne hβγ), h, ← hA₂ γ (Iio.coe_injective.ne hδγ)]
    rw [← this]
    exact Code.Equiv.cloud_left _ even₂ γ (Iio.coe_injective.ne hδγ)

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all semitangles have a `⊥`-extension.
Therefore, the extensionality principle in this case applies to the `⊥`-extensions. -/
theorem ext_zero (t₁ t₂ : Semitangle α) (α_zero : IsMin α) (h : t₁.pref.atoms = t₂.pref.atoms) :
    t₁ = t₂ := by
  obtain ⟨xs, ⟨atoms₁, hA₁⟩ | ⟨γ, _, _⟩⟩ := t₁
  swap
  · cases α_zero.not_lt γ.2
  obtain ⟨ys, ⟨atoms₂, hA₂⟩ | ⟨γ, _, _⟩⟩ := t₂
  swap
  · cases α_zero.not_lt γ.2
  have : atoms₁ = atoms₂ := h
  subst this
  suffices xs = ys by subst this; rfl
  funext β
  cases α_zero.not_lt β.2

/-- Construct a semitangle from an even code. -/
def intro (s : Set (Tangle β)) (heven : (Code.mk β s : Code α).IsEven) : Semitangle α :=
  ⟨extension s,
    match β, s, heven with
    | ⟨⊥, _⟩, s, _ => Preference.base s fun β => rfl
    | ⟨(γ : Λ), hγ⟩, s, heven =>
      Preference.proper ⟨γ, coe_lt_coe.1 hγ⟩
        (by
          convert heven
          exact extension_self (show Set (Tangle <| iioCoe ⟨γ, _⟩) from s))
        fun δ hδ => by
          rw [extension_ne s δ hδ]
          congr
          refine congr_arg _ ?_
          exact extension_self (show Set (Tangle <| iioCoe ⟨γ, _⟩) from s)⟩

@[simp]
theorem exts_intro (s : Set (Tangle β)) (heven : IsEven (Code.mk β s)) :
    (intro s heven).members = extension s :=
  rfl

end Semitangle

open Semitangle

variable [TangleData α]

namespace NewAllowable

/-!
We now establish that allowable permutations can act on semitangles.
-/

variable {ρ : NewAllowable α} {e : Extensions α}

@[simp]
theorem smul_extension_apply (ρ : NewAllowable α) (s : Set (Tangle β)) :
    ρ.val γ • extension s γ = extension (ρ.val β • s) γ := by
  by_cases β = γ
  · subst h
    simp only [extension_eq, cast_eq]
  · rw [extension_ne _ _ h, extension_ne _ _ h, smul_cloud]

instance : MulAction (SemiallowablePerm α) (Extensions α)
    where
  smul ρ e γ := ρ γ • e γ
  one_smul e := by
    funext γ
    change (1 : SemiallowablePerm α) γ • e γ = e γ
    simp only [SemiallowablePerm.one_apply, one_smul]
  mul_smul ρ ρ' e := by
    funext γ
    change (ρ * ρ') γ • e γ = ρ γ • ρ' γ • e γ
    simp only [SemiallowablePerm.mul_apply, mul_smul]

@[simp]
theorem smul_extension (ρ : NewAllowable α) (s : Set (Tangle β)) :
    ρ • extension s = extension (ρ.val β • s) := by
  ext γ : 1
  rw [← smul_extension_apply]
  rfl

theorem smul_aux₁ {s : Set (Tangle (⊥ : IioBot α))}
    (h : ∀ γ : Iio α, cloud bot_ne_coe s = (e γ : Set (Tangle (iioCoe γ)))) (γ : Iio α) :
    cloud bot_ne_coe (ρ.val ⊥ • s) = (ρ • e) γ := by
  have := congr_arg (fun c => ρ.val γ • c) (h γ)
  dsimp only at this
  rw [smul_cloud] at this
  exact this

theorem smul_aux₂
    (h : ∀ (δ : Iio α) (hγδ : iioCoe γ ≠ δ), cloud hγδ (e γ) = (e δ : Set (Tangle (iioCoe δ))))
    (δ : Iio α) (hγδ : iioCoe γ ≠ δ) : cloud hγδ ((ρ • e) γ) = (ρ • e) δ := by
  have := congr_arg (fun c => ρ.val δ • c) (h δ hγδ)
  dsimp only at this
  rw [smul_cloud] at this
  exact this

/-- Allowable permutations act on semitangles. -/
noncomputable instance : SMul (NewAllowable α) (Semitangle α)
    where smul ρ t :=
    ⟨ρ • t.members, by
      obtain ⟨members, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩ := t
      · exact Preference.base (ρ.val ⊥ • s) (smul_aux₁ h)
      · exact Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩

@[simp]
theorem members_smul (ρ : NewAllowable α) (t : Semitangle α) : (ρ • t).members = ρ • t.members :=
  rfl

@[simp]
theorem smul_base (ρ : NewAllowable α) (e : Extensions α) (s h) :
    ρ • (⟨e, Preference.base s h⟩ : Semitangle α) =
      ⟨ρ • e, Preference.base (ρ.val ⊥ • s) (smul_aux₁ h)⟩ :=
  rfl

@[simp]
theorem smul_proper (ρ : NewAllowable α) (e : Extensions α) (γ ht h) :
    ρ • (⟨e, Preference.proper γ ht h⟩ : Semitangle α) =
      ⟨ρ • e, Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩ :=
  rfl

noncomputable instance mulActionSemitangle : MulAction (NewAllowable α) (Semitangle α)
    where
  one_smul := by
    rintro ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · rw [smul_base]
      simp only [one_smul, mk.injEq, true_and]
      refine Preference.base_heq_base ?_ ?_
      · rw [one_smul]
      · simp only [coe_one, SemiallowablePerm.one_apply, one_smul]
    · rw [smul_proper]
      simp only [one_smul, mk.injEq, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [one_smul]
  mul_smul := by
    rintro ρ ρ' ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · simp only [smul_base, mul_smul, mk.injEq, true_and]
      refine Preference.base_heq_base ?_ ?_
      · rw [mul_smul]
      · simp only [coe_mul, SemiallowablePerm.mul_apply, mul_smul]
    · simp only [smul_proper, mk.injEq, mul_smul, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [mul_smul]

end NewAllowable

variable (α)

/-- A tangle at the new level `α` is a semitangle supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def NewTangle :=
  { t : Semitangle α // Supported α (NewAllowable α) t }

variable {α}
variable {c d : Code α} {S : Set (SupportCondition α)}

open MulAction

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected theorem Code.Equiv.supports (hcd : c ≡ d) (hS : Supports (NewAllowable α) S c) :
    Supports (NewAllowable α) S d := fun ρ h => by
  have h₁ := hcd.smul (ρ := ρ)
  have h₂ := (Code.Equiv.of_eq <| hS ρ h).trans hcd
  exact (h₁.symm.trans h₂).unique rfl

theorem Code.Equiv.supports_iff (hcd : c ≡ d) :
    Supports (NewAllowable α) S c ↔ Supports (NewAllowable α) S d :=
  ⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
theorem Code.Equiv.supported_iff (hcd : c ≡ d) :
    Supported α (NewAllowable α) c ↔ Supported α (NewAllowable α) d :=
  ⟨fun ⟨⟨s, hs, h⟩⟩ => ⟨⟨s, hs, hcd.supports h⟩⟩,
    fun ⟨⟨s, hs, h⟩⟩ => ⟨⟨s, hs, hcd.symm.supports h⟩⟩⟩

@[simp]
theorem smul_intro (ρ : NewAllowable α) (s : Set (Tangle β)) (hs) :
    ρ • intro s hs = intro (ρ.val β • s) (isEven_smul.mpr hs) := by
  obtain ⟨β, hβ⟩ := β
  induction β using WithBot.recBotCoe
  · simp only [intro, NewAllowable.smul_base, mk.injEq, NewAllowable.smul_extension, true_and]
    refine Preference.base_heq_base ?_ rfl
    rw [NewAllowable.smul_extension]
  · simp only [intro, NewAllowable.smul_proper, mk.injEq, NewAllowable.smul_extension, true_and]
    refine Preference.proper_heq_proper ?_ rfl
    rw [NewAllowable.smul_extension]

-- TODO: Move next two lemmas elsewhere.
theorem allowableToStructPerm_bot (π : Allowable (⊥ : IioBot α)) :
    TangleData.allowableToStructPerm π = Structural.toBotIso.toMonoidHom π :=
  rfl

theorem _root_.ConNF.SemiallowablePerm.coe_apply_bot (ρ : SemiallowablePerm α) :
    (ρ : SemiallowablePerm α) ⊥ =
      SemiallowablePerm.toStructPerm ρ (Quiver.Hom.toPath (bot_lt_coe _)) := by
  rfl

theorem NewAllowable.smul_supportCondition {ρ : NewAllowable α} {c : SupportCondition α} :
    ρ • c = ⟨c.path, NewAllowable.toStructPerm ρ c.path • c.value⟩ :=
  rfl

@[simp]
theorem NewAllowable.smul_supportCondition_eq_iff {ρ : NewAllowable α} {c : SupportCondition α} :
    ρ • c = c ↔ NewAllowable.toStructPerm ρ c.path • c.value = c.value :=
  StructPerm.smul_supportCondition_eq_iff

@[simp]
theorem NewAllowable.smul_supportCondition_eq_smul_iff
    {ρ ρ' : NewAllowable α} {c : SupportCondition α} :
    ρ • c = ρ' • c ↔
    NewAllowable.toStructPerm ρ c.path • c.value =
      NewAllowable.toStructPerm ρ' c.path • c.value :=
  StructPerm.smul_supportCondition_eq_smul_iff

/-- For any near-litter `N`, the code `(α, ⊥, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def newTypedNearLitter (N : NearLitter) : NewTangle α :=
  ⟨intro (show Set (Tangle (⊥ : IioBot α)) from N.2.1) <| Code.isEven_bot _,
    ⟨⟨{⟨Quiver.Hom.toPath (bot_lt_coe _), Sum.inr N⟩}, small_singleton _, fun ρ h => by
        simp only [smul_intro]
        congr 1
        simp only [mem_singleton_iff, NewAllowable.smul_supportCondition_eq_iff, forall_eq,
          Sum.smul_inr, Sum.inr.injEq] at h
        apply_fun SetLike.coe at h
        refine Eq.trans ?_ h
        rw [NearLitterPerm.smul_nearLitter_coe]
        change _ '' _ = _ '' _
        simp_rw [SemiallowablePerm.coe_apply_bot]
        rfl⟩⟩⟩

namespace NewTangle

instance : Coe (NewTangle α) (Semitangle α)
    where
  coe := Subtype.val

theorem coe_injective : Injective (Subtype.val : NewTangle α → Semitangle α) :=
  Subtype.coe_injective

end NewTangle

namespace NewAllowable

/-- Allowable permutations act on `α`-tangles. -/
noncomputable instance hasSmulNewTangle : SMul (NewAllowable α) (NewTangle α) :=
  ⟨fun ρ t =>
    ⟨ρ • (t : Semitangle α),
      t.2.map fun (s : Support α (NewAllowable α) (t : Semitangle α)) =>
        { carrier := ρ • (s : Set (SupportCondition α))
          small := s.small.image
          supports := by
            intro ρ' h
            have := s.supports (ρ⁻¹ * ρ' * ρ) ?_
            · conv_rhs =>
                rw [← this, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_self, one_mul, mul_smul]
            · intro a ha
              rw [mul_smul, mul_smul, inv_smul_eq_iff]
              exact h (smul_mem_smul_set ha) }⟩⟩

@[simp, norm_cast]
theorem coe_smul_newTangle (ρ : NewAllowable α) (t : NewTangle α) :
    ((ρ • t) : Semitangle α) = ρ • (t : Semitangle α) :=
  rfl

noncomputable instance mulActionNewTangle : MulAction (NewAllowable α) (NewTangle α) :=
  NewTangle.coe_injective.mulAction Subtype.val coe_smul_newTangle

end NewAllowable

end ConNF
