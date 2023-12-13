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

variable [Params.{u}] [Level] [TangleDataLt]
  {β : TypeIndex} [LtLevel β] {γ : Λ} [LtLevel γ]

open Code

abbrev Extensions :=
  ∀ β : Λ, [LtLevel β] → Set (Tangle β)

@[ext]
theorem Extensions.ext {e₁ e₂ : Extensions} (h : ∀ β : Λ, [LtLevel β] → e₁ β = e₂ β) : e₁ = e₂ :=
  funext (fun β => funext (fun _ => h β))

namespace Semitangle

variable [PositionedTanglesLt] [TypedObjectsLt]

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. In particular, each non-preferred extension can be
obtained by applying the `cloud` map to the preferred extension. -/
inductive Preference (members : Extensions)
  | base (atoms : Set (Tangle ⊥)) :
    (∀ (γ : Λ), [LtLevel γ] → cloud bot_ne_coe atoms = members γ) → Preference members
  | proper (β : Λ) [LtLevel β] :
    (mk β (members β) : Code).IsEven →
    (∀ (γ : Λ) [LtLevel γ] (hβγ : (β : TypeIndex) ≠ γ), cloud hβγ (members β) = members γ) →
    Preference members

variable {members : Extensions}

/-- The `⊥`-extension associated with a given semitangle extension. -/
def Preference.atoms : Preference members → Set Atom
  | Preference.base atoms _ => (atoms : Set (Tangle ⊥))
  | Preference.proper _ _ _ => ∅

theorem Preference.base_heq_base {m₁ m₂ : Extensions} {s₁ s₂ h₁ h₂} (hm : m₁ = m₂)
    (hs : s₁ = s₂) :
    HEq (Preference.base s₁ h₁ : Preference m₁) (Preference.base s₂ h₂ : Preference m₂) := by
  cases hm
  cases hs
  rfl

theorem Preference.proper_heq_proper {m₁ m₂ : Extensions} {β₁ β₂ : Λ} [LtLevel β₁] [LtLevel β₂]
    {h₁ h₂ h₃ h₄} (hm : m₁ = m₂) (hs : β₁ = β₂) :
    HEq (Preference.proper β₁ h₁ h₂ : Preference m₁)
      (Preference.proper β₂ h₃ h₄ : Preference m₂) := by
  cases hm
  cases hs
  rfl

end Semitangle

open Semitangle

variable [PositionedTanglesLt] [TypedObjectsLt]

/-- A *semitangle* is a collection of `β`-tangles for each lower level `β < α`, together with
a preference for one of these extensions. -/
structure Semitangle where
  members : Extensions
  pref : Preference members

namespace Semitangle

/-- The even code associated to a semitangle. -/
def reprCode : Semitangle → Code
  | ⟨_, Preference.base atoms _⟩ => ⟨⊥, atoms⟩
  | ⟨exts, Preference.proper β _ _⟩ => ⟨β, exts β⟩

@[simp]
theorem reprCode_base (exts : Extensions) (atoms hA) :
    reprCode ⟨exts, Preference.base atoms hA⟩ = ⟨⊥, atoms⟩ :=
  rfl

@[simp]
theorem reprCode_proper (exts : Extensions) (β : Λ) [LtLevel β] (rep hA) :
    reprCode ⟨exts, Preference.proper β rep hA⟩ = ⟨β, exts β⟩ :=
  rfl

theorem reprCodeSpec : ∀ t : Semitangle, (reprCode t : Code).IsEven
  | ⟨_, Preference.proper _ rep _⟩ => rep
  | ⟨_, Preference.base _ _⟩ => isEven_bot _

theorem reprCode_members_ne :
    ∀ (t : Semitangle) (γ : Λ) [LtLevel γ] (_ : (reprCode t : Code).1 ≠ γ),
      (cloudCode γ (reprCode t)).members = t.members γ
  | ⟨exts, Preference.proper β rep hA⟩, γ, _, hcγ => by
      rw [snd_cloudCode]
      exact hA _ hcγ
  | ⟨_, Preference.base _ hA⟩, γ, _, _ => hA _

/-- One form of extensionality: If there is a proper type index `γ < α`, then two semitangles
with the same elements have the same preference.

Remark: This formulation of extensionality holds only for types larger than type zero, since
it doesn't take into account any `⊥`-extension. -/
theorem ext_core (t₁ t₂ : Semitangle) : Nonempty ((γ : Λ) ×' LtLevel γ) →
    t₁.members = t₂.members → t₁ = t₂ := by
  obtain ⟨xs, hxs⟩ := t₁
  obtain ⟨ys, hys⟩ := t₂
  rintro ⟨γ, _⟩ rfl
  simp only [mk.injEq, heq_eq_eq, true_and]
  obtain ⟨atoms₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs <;>
  obtain ⟨atoms₂, hA₂⟩ | ⟨γ, even₂, hA₂⟩ := hys
  · simp_rw [cloud_injective ((hA₁ γ).trans (hA₂ _).symm)]
  · cases (isEven_bot atoms₁).cloudCode_ne even₂ (bot_ne_coe (a := γ))
      (Code.ext _ _ rfl (heq_of_eq (hA₁ γ)))
  · cases (isEven_bot atoms₂).cloudCode_ne even₁ (bot_ne_coe (a := β))
      (Code.ext _ _ rfl (heq_of_eq (hA₂ β)))
  · simp only [Preference.proper.injEq]
    refine not_ne_iff.1 fun hβγ =>
      even₂.cloudCode_ne even₁ (WithBot.coe_injective.ne hβγ.symm) <|
        Code.ext _ _ rfl (heq_of_eq ?_)
    rw [snd_cloudCode]
    exact hA₂ β fun h => hβγ.symm (WithBot.coe_injective h)

/-- One useful form of extensionality in tangled type theory. Two semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
theorem ext_code : ∀ {t₁ t₂ : Semitangle}, reprCode t₁ ≡ reprCode t₂ → t₁ = t₂
  | ⟨e₁, Preference.base atoms₁ hA₁⟩, ⟨e₂, Preference.base atoms₂ hA₂⟩, h => by
    obtain rfl := Code.Equiv.bot_bot_iff.1 h
    obtain rfl : e₁ = e₂ := Extensions.ext fun γ => (hA₁ γ).symm.trans <| hA₂ _
    rfl
  | ⟨e₁, Preference.base s hA₁⟩, ⟨e₂, Preference.proper γ even₂ hA₂⟩, h => by
    change Code.mk _ _ ≡ Code.mk _ _ at h
    obtain ⟨δ, _, hδ⟩ :=
      (Code.Equiv.bot_left_iff.1 h).resolve_left (ne_of_apply_ne Code.β bot_ne_coe)
    rw [hδ] at even₂
    cases even₂.not_isOdd ((isEven_bot _).cloudCode bot_ne_coe)
  | ⟨e₁, Preference.proper γ even₁ hA₁⟩, ⟨e₂, Preference.base s hA₂⟩, h => by
    change Code.mk _ _ ≡ Code.mk _ _ at h
    obtain ⟨δ, _, hδ⟩ :=
      (Code.Equiv.bot_right_iff.1 h).resolve_left (ne_of_apply_ne Code.β bot_ne_coe.symm)
    rw [hδ] at even₁
    cases even₁.not_isOdd ((isEven_bot _).cloudCode bot_ne_coe)
  | ⟨e₁, Preference.proper γ even₁ hA₁⟩, ⟨e₂, Preference.proper δ even₂ hA₂⟩, h => by
    dsimp at h
    simp only [Equiv_iff, WithBot.coe_ne_bot, ne_eq, Subtype.mk.injEq, coe_inj, Subtype.coe_inj,
      Subtype.exists, mem_Iio] at h
    obtain h | ⟨_, γ, _, hδγ, h⟩ | ⟨_, δ, _, hγδ, h⟩ |
      ⟨c, hc, γ, hcγ, hc', δ, hcδ, h⟩ := h
    · rw [Code.ext_iff] at h
      simp only [Subtype.mk.injEq, coe_inj, Subtype.coe_inj] at h
      obtain rfl := h.1
      suffices e₁ = e₂ by subst this; rfl
      ext ε : 1
      obtain rfl | hδε := eq_or_ne δ ε
      · exact eq_of_heq h.2.symm
      refine (hA₁ _ fun h => hδε (WithBot.coe_injective h)).symm.trans
          (Eq.trans ?_ <| hA₂ _ fun h => hδε (WithBot.coe_injective h))
      rw [eq_of_heq h.2]
    · rw [Code.ext_iff] at h
      simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, ne_eq] at h
      obtain rfl := h.1
      rw [eq_of_heq h.2] at even₁
      cases (even₂.cloudCode <| WithBot.coe_injective.ne hδγ).not_isEven even₁
    · rw [Code.ext_iff] at h
      simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, ne_eq] at h
      obtain rfl := h.1
      rw [eq_of_heq h.2] at even₂
      cases (even₁.cloudCode <| WithBot.coe_injective.ne hγδ).not_isEven even₂
    · rw [Code.ext_iff] at h
      simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, ne_eq] at h
      obtain rfl := h.2.1.1
      rw [eq_of_heq h.2.1.2] at even₁
      cases (hc.cloudCode hc').not_isEven even₁

/-- Extensionality in tangled type theory. Two semitangles are equal if their
`β`-extensions are equal for *any* choice of `γ < α`.
TODO: This proof can be golfed quite a bit just by cleaning up the `simp` calls. -/
theorem ext (t₁ t₂ : Semitangle) (h : t₁.members γ = t₂.members γ) : t₁ = t₂ := by
  obtain ⟨xs, hxs⟩ := t₁
  obtain ⟨ys, hys⟩ := t₂
  dsimp only at h
  refine ext_code ?_
  obtain ⟨atoms₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs <;> obtain ⟨atoms₂, hA₂⟩ | ⟨δ, even₂, hA₂⟩ := hys
  · refine (Code.Equiv.cloud_right _ (Code.isEven_bot _) γ bot_ne_coe).trans ?_
    simp only [ne_eq, bot_ne_coe, not_false_eq_true, cloudCode_mk_ne, reprCode_base,
      Equiv.bot_right_iff, Code.mk.injEq, coe_ne_bot, false_and, coe_inj, exists_and_left,
      exists_eq_left', heq_eq_eq, false_or]
    rw [hA₁ γ, h, ← hA₂ γ]
    exact ⟨inferInstance, rfl⟩
  · simp only [reprCode_base, Subtype.coe_mk, reprCode_proper]
    obtain rfl | hδγ := eq_or_ne δ γ
    · simp only [coe_ne_bot, isEmpty_mk, ne_eq, coe_inj, Equiv.bot_left_iff, Code.mk.injEq,
        bot_ne_coe, false_and, exists_and_left, exists_eq_left', heq_eq_eq, false_or] at *
      rw [← h, ← hA₁ δ]
      exact ⟨inferInstance, rfl⟩
    · refine (Code.Equiv.cloud_right _ (Code.isEven_bot _) γ bot_ne_coe).trans ?_
      simp only [ne_eq, bot_ne_coe, not_false_eq_true, cloudCode_mk_ne]
      rw [hA₁ γ, h, ← hA₂ γ (WithBot.coe_injective.ne hδγ), ← cloudCode_mk_ne]
      exact Code.Equiv.cloud_left _ even₂ γ (WithBot.coe_injective.ne hδγ)
  · simp only [reprCode_proper, Subtype.coe_mk, reprCode_base]
    obtain rfl | hβγ := eq_or_ne β γ
    · dsimp only [mem_Iio, Ne.def, SetCoe.forall] at *
      rw [h, ← hA₂ β]
      exact Code.Equiv.cloud_left _ (Code.isEven_bot _) _ bot_ne_coe
    · refine (Code.Equiv.cloud_right _ even₁ γ <| WithBot.coe_injective.ne hβγ).trans ?_
      dsimp only [mem_Iio, Ne.def, SetCoe.forall] at *
      refine (Code.Equiv.of_eq <| cloudCode_mk_ne _ _ (WithBot.coe_injective.ne hβγ) (xs β)).trans ?_
      rw [hA₁ γ (WithBot.coe_injective.ne hβγ), h, ← hA₂ γ]
      exact Code.Equiv.cloud_left _ (Code.isEven_bot _) γ bot_ne_coe
  · simp only [reprCode_proper, Subtype.coe_mk]
    obtain rfl | hβγ := eq_or_ne β γ
    · obtain rfl | hδβ := eq_or_ne δ β
      · rw [h]
      · have := cloudCode_ne β (Code.mk δ (ys δ)) (WithBot.coe_injective.ne hδβ)
        dsimp only [mem_Iio, Ne.def, SetCoe.forall] at *
        rw [h, ← hA₂ _ (WithBot.coe_injective.ne hδβ), ← this]
        exact Code.Equiv.cloud_left _ even₂ _ (WithBot.coe_injective.ne hδβ)
    obtain rfl | hδγ := eq_or_ne δ γ
    · have := cloudCode_ne δ (Code.mk β (xs β)) (WithBot.coe_injective.ne hβγ)
      dsimp only [mem_Iio, Ne.def, SetCoe.forall] at *
      simp_rw [← h, ← hA₁ _ (WithBot.coe_injective.ne hβγ), ← this]
      exact Code.Equiv.cloud_right _ even₁ _ (WithBot.coe_injective.ne hβγ)
    refine' (Code.Equiv.cloud_right _ even₁ γ <| WithBot.coe_injective.ne hβγ).trans _
    have := cloudCode_ne γ (Code.mk (↑δ) (ys δ)) (WithBot.coe_injective.ne hδγ)
    dsimp only [mem_Iio, Ne.def, SetCoe.forall] at *
    rw [cloudCode_ne]
    rw [hA₁ γ (WithBot.coe_injective.ne hβγ), h, ← hA₂ γ (WithBot.coe_injective.ne hδγ)]
    rw [← this]
    exact Code.Equiv.cloud_left _ even₂ γ (WithBot.coe_injective.ne hδγ)

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all semitangles have a `⊥`-extension.
Therefore, the extensionality principle in this case applies to the `⊥`-extensions. -/
theorem ext_zero (t₁ t₂ : Semitangle) (α_zero : IsMin α) (h : t₁.pref.atoms = t₂.pref.atoms) :
    t₁ = t₂ := by
  obtain ⟨xs, ⟨atoms₁, hA₁⟩ | ⟨γ, _, _⟩⟩ := t₁
  swap
  · cases α_zero.not_lt (show γ < α from WithBot.coe_lt_coe.mp LtLevel.elim)
  obtain ⟨ys, ⟨atoms₂, hA₂⟩ | ⟨γ, _, _⟩⟩ := t₂
  swap
  · cases α_zero.not_lt (show γ < α from WithBot.coe_lt_coe.mp LtLevel.elim)
  subst h
  suffices xs = ys by
    subst this
    rfl
  ext β : 1
  cases α_zero.not_lt (show β < α from WithBot.coe_lt_coe.mp LtLevel.elim)

/-- Construct a semitangle from an even code. -/
def intro {β : TypeIndex} [inst : LtLevel β] (s : Set (Tangle β))
    (heven : (Code.mk β s).IsEven) : Semitangle :=
  ⟨extension s,
    match β, inst, s, heven with
    | ⊥, _, s, _ => Preference.base s fun β => rfl
    | (γ : Λ), _, s, heven =>
      Preference.proper γ
        (by
          convert heven
          exact extension_self s)
        fun δ _ hδ => by
          rw [extension_ne s δ]
          congr
          exact congr_arg _ (extension_self s)⟩

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

variable {ρ : NewAllowable} {e : Extensions}

@[simp]
theorem smul_extension_apply (ρ : NewAllowable) (s : Set (Tangle β)) :
    ρ.val γ • extension s γ = extension (ρ.val β • s) γ := by
  by_cases h : β = γ
  · subst h
    simp only [extension_eq, cast_eq]
  · rw [extension_ne _ _ h, extension_ne _ _ h, smul_cloud]

instance : MulAction SemiallowablePerm Extensions
    where
  smul ρ e γ := ρ γ • e γ
  one_smul e := by
    ext γ : 1
    change (1 : SemiallowablePerm) γ • e γ = e γ
    simp only [SemiallowablePerm.one_apply, one_smul]
  mul_smul ρ ρ' e := by
    ext γ : 1
    change (ρ * ρ') γ • e γ = ρ γ • ρ' γ • e γ
    simp only [SemiallowablePerm.mul_apply, mul_smul]

@[simp]
theorem smul_extension (ρ : NewAllowable) (s : Set (Tangle β)) :
    ρ • extension s = extension (ρ.val β • s) := by
  ext γ : 2
  rw [← smul_extension_apply]
  rfl

theorem smul_aux₁ {s : Set (Tangle ⊥)}
    (h : ∀ γ : Λ, [LtLevel γ] → cloud bot_ne_coe s = (e γ : Set (Tangle γ))) (γ : Λ) [LtLevel γ] :
    cloud bot_ne_coe (ρ.val ⊥ • s) = (ρ • e) γ := by
  have := congr_arg (fun c => ρ.val γ • c) (h γ)
  dsimp only at this
  rw [smul_cloud] at this
  exact this

theorem smul_aux₂
    (h : ∀ (δ : Λ) [LtLevel δ] (hγδ : (γ : TypeIndex) ≠ δ),
      cloud hγδ (e γ) = (e δ : Set (Tangle δ)))
    (δ : Λ) [LtLevel δ] (hγδ : (γ : TypeIndex) ≠ δ) : cloud hγδ ((ρ • e) γ) = (ρ • e) δ := by
  have := congr_arg (fun c => ρ.val δ • c) (h δ hγδ)
  dsimp only at this
  rw [smul_cloud] at this
  exact this

/-- Allowable permutations act on semitangles. -/
instance : SMul NewAllowable Semitangle where
  smul ρ t := ⟨ρ • t.members, by
    obtain ⟨members, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩ := t
    · exact Preference.base (ρ.val ⊥ • s) (smul_aux₁ h)
    · exact Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩

@[simp]
theorem members_smul' (ρ : NewAllowable) (t : Semitangle) : (ρ • t).members = ρ • t.members :=
  rfl

@[simp]
theorem smul_base (ρ : NewAllowable) (e : Extensions) (s h) :
    ρ • (⟨e, Preference.base s h⟩ : Semitangle) =
      ⟨ρ • e, Preference.base (ρ.val ⊥ • s) (smul_aux₁ h)⟩ :=
  rfl

@[simp]
theorem smul_proper (ρ : NewAllowable) (e : Extensions) (γ : Λ) [LtLevel γ] (ht h) :
    ρ • (⟨e, Preference.proper γ ht h⟩ : Semitangle) =
      ⟨ρ • e, Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩ :=
  rfl

instance mulActionSemitangle : MulAction NewAllowable Semitangle
    where
  one_smul := by
    rintro ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · rw [smul_base]
      simp only [coe_one, SemiallowablePerm.one_apply, one_smul, Semitangle.mk.injEq, true_and]
      refine Preference.base_heq_base ?_ ?_
      · rw [one_smul]
      · simp only [coe_one, SemiallowablePerm.one_apply, one_smul]
    · rw [smul_proper]
      simp only [Semitangle.mk.injEq, one_smul, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [one_smul]
  mul_smul := by
    rintro ρ ρ' ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · simp only [smul_base, coe_mul, SemiallowablePerm.mul_apply, mul_smul, Semitangle.mk.injEq,
      true_and]
      refine Preference.base_heq_base ?_ ?_
      · rw [mul_smul]
      · simp only [coe_mul, SemiallowablePerm.mul_apply, mul_smul]
    · simp only [smul_proper, Semitangle.mk.injEq, mul_smul, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [mul_smul]

end NewAllowable

/-- A tangle at the new level `α` is a semitangle supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def NewTangle :=
  { t : Semitangle // Supported α NewAllowable t }

variable {c d : Code} {S : Set (SupportCondition α)}

open MulAction

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected theorem Code.Equiv.supports (hcd : c ≡ d) (hS : Supports NewAllowable S c) :
    Supports NewAllowable S d := fun ρ h => by
  have h₁ := hcd.smul (ρ := ρ)
  have h₂ := (Code.Equiv.of_eq <| hS ρ h).trans hcd
  exact (h₁.symm.trans h₂).unique rfl

theorem Code.Equiv.supports_iff (hcd : c ≡ d) :
    Supports NewAllowable S c ↔ Supports NewAllowable S d :=
  ⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
theorem Code.Equiv.supported_iff (hcd : c ≡ d) :
    Supported α NewAllowable c ↔ Supported α NewAllowable d :=
  ⟨fun ⟨⟨s, hs, h⟩⟩ => ⟨⟨s, hs, hcd.supports h⟩⟩,
    fun ⟨⟨s, hs, h⟩⟩ => ⟨⟨s, hs, hcd.symm.supports h⟩⟩⟩

@[simp]
theorem smul_intro {β : TypeIndex} [inst : LtLevel β]  (ρ : NewAllowable) (s : Set (Tangle β)) (hs) :
    ρ • intro s hs = intro (ρ.val β • s) (isEven_smul.mpr hs) := by
  induction β using WithBot.recBotCoe generalizing inst
  · simp only [intro, NewAllowable.smul_base, Semitangle.mk.injEq, NewAllowable.smul_extension,
      true_and]
    refine Preference.base_heq_base ?_ rfl
    rw [NewAllowable.smul_extension]
  · simp only [intro, NewAllowable.smul_proper, Semitangle.mk.injEq, NewAllowable.smul_extension,
      true_and]
    refine Preference.proper_heq_proper ?_ rfl
    rw [NewAllowable.smul_extension]

theorem NewAllowable.smul_supportCondition {ρ : NewAllowable} {c : SupportCondition α} :
    ρ • c = ⟨c.path, NewAllowable.toStructPerm ρ c.path • c.value⟩ :=
  rfl

@[simp]
theorem NewAllowable.smul_supportCondition_eq_iff {ρ : NewAllowable} {c : SupportCondition α} :
    ρ • c = c ↔ NewAllowable.toStructPerm ρ c.path • c.value = c.value :=
  StructPerm.smul_supportCondition_eq_iff

@[simp]
theorem NewAllowable.smul_supportCondition_eq_smul_iff
    {ρ ρ' : NewAllowable} {c : SupportCondition α} :
    ρ • c = ρ' • c ↔
    NewAllowable.toStructPerm ρ c.path • c.value =
      NewAllowable.toStructPerm ρ' c.path • c.value :=
  StructPerm.smul_supportCondition_eq_smul_iff

/-- For any near-litter `N`, the code `(α, ⊥, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def newTypedNearLitter (N : NearLitter) : NewTangle :=
  ⟨intro (show Set (Tangle ⊥) from N.2.1) <| Code.isEven_bot _,
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

instance : Coe NewTangle Semitangle
    where
  coe := Subtype.val

theorem coe_injective : Injective (Subtype.val : NewTangle → Semitangle) :=
  Subtype.coe_injective

end NewTangle

namespace NewAllowable

/-- Allowable permutations act on `α`-tangles. -/
instance hasSmulNewTangle : SMul NewAllowable NewTangle :=
  ⟨fun ρ t =>
    ⟨ρ • (t : Semitangle),
      t.2.map fun (s : Support α NewAllowable (t : Semitangle)) =>
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
theorem coe_smul_newTangle (ρ : NewAllowable) (t : NewTangle) :
    ((ρ • t) : Semitangle) = ρ • (t : Semitangle) :=
  rfl

instance mulActionNewTangle : MulAction NewAllowable NewTangle :=
  NewTangle.coe_injective.mulAction Subtype.val coe_smul_newTangle

end NewAllowable

end ConNF
