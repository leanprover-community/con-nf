import Mathlib.GroupTheory.GroupAction.Option
import ConNF.Mathlib.GroupAction
import ConNF.Mathlib.Pointwise
import ConNF.Construction.NewAllowable

/-!
# Construction of t-sets

In this file, we construct the type of t-sets at level `α`, assuming they exist at all levels
`β < α`.

## Main declarations

* `ConNF.Extensions`: The type of extensions of a t-set at level `α`.
* `ConNF.Preference`: A preferred extension of a extensional set.
* `ConNF.ExtensionalSet`: An extension for each `β < α`, with one chosen as its preferred extension.
    The non-preferred extensions can be derived from the preferred extension.
* `ConNF.NewTangle`: The type of t-sets at level `α`.
-/

open Function Set WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [ModelDataLt]
  {β : TypeIndex} [LtLevel β] {γ : Λ} [LtLevel γ]

open Code

abbrev Extensions :=
  ∀ β : Λ, [LtLevel β] → Set (TSet β)

@[ext]
theorem Extensions.ext {e₁ e₂ : Extensions} (h : ∀ β : Λ, [LtLevel β] → e₁ β = e₂ β) : e₁ = e₂ :=
  funext (fun β => funext (fun _ => h β))

/-!
## Extensional sets
-/

namespace ExtensionalSet

variable [PositionedTanglesLt] [TypedObjectsLt]

/-- Keeps track of the preferred extension of a extensional set, along with coherence conditions
relating each extension of the extensional set. In particular, each non-preferred extension can be
obtained by applying the `cloud` map to the preferred extension. -/
inductive Preference (members : Extensions)
  | base (atoms : Set (Tangle ⊥)) :
    (∀ (γ : Λ), [LtLevel γ] → cloud bot_ne_coe atoms = members γ) → Preference members
  | proper (β : Λ) [LtLevel β] :
    (mk β (members β) : Code).IsEven →
    (∀ (γ : Λ) [LtLevel γ] (hβγ : (β : TypeIndex) ≠ γ), cloud hβγ (members β) = members γ) →
    Preference members

variable {members : Extensions}

/-- The `⊥`-extension in a given extensional set, if it exists. -/
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

end ExtensionalSet

open ExtensionalSet

variable [PositionedTanglesLt] [TypedObjectsLt] [PositionedObjectsLt]

/-- A *extensional set* is a collection of `β`-tangles for each lower level `β < α`, together with
a preference for one of these extensions. -/
structure ExtensionalSet where
  members : Extensions
  pref : Preference members

namespace ExtensionalSet

/-- The even code associated to a extensional set. -/
def reprCode : ExtensionalSet → Code
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

theorem reprCodeSpec : ∀ t : ExtensionalSet, (reprCode t : Code).IsEven
  | ⟨_, Preference.proper _ rep _⟩ => rep
  | ⟨_, Preference.base _ _⟩ => isEven_bot _

theorem reprCode_members_ne :
    ∀ (t : ExtensionalSet) (γ : Λ) [LtLevel γ] (_ : (reprCode t : Code).1 ≠ γ),
      (cloudCode γ (reprCode t)).members = t.members γ
  | ⟨exts, Preference.proper β rep hA⟩, γ, _, hcγ => by
      rw [snd_cloudCode]
      exact hA _ hcγ
  | ⟨_, Preference.base _ hA⟩, γ, _, _ => hA _

/-- One form of extensionality: If there is a proper type index `γ < α`, then two extensional sets
with the same elements have the same preference.

This formulation of extensionality holds only for types larger than type zero, since it doesn't take
into account any `⊥`-extension. -/
theorem ext_core (t₁ t₂ : ExtensionalSet) : Nonempty ((γ : Λ) ×' LtLevel γ) →
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

/-- One useful form of extensionality in tangled type theory. Two extensional sets are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
theorem ext_code : ∀ {t₁ t₂ : ExtensionalSet}, reprCode t₁ ≡ reprCode t₂ → t₁ = t₂
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
    simp only [equiv_iff, WithBot.coe_ne_bot, ne_eq, Subtype.mk.injEq, coe_inj, Subtype.coe_inj,
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

/-- Extensionality in tangled type theory. Two extensional sets are equal if their
`β`-extensions are equal for *any* choice of `γ < α`.
TODO: This proof can be golfed quite a bit just by cleaning up the `simp` calls. -/
theorem ext (t₁ t₂ : ExtensionalSet) (h : t₁.members γ = t₂.members γ) : t₁ = t₂ := by
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
At type 0, all extensional sets have a `⊥`-extension.
Therefore, the extensionality principle in this case applies to the `⊥`-extensions. -/
theorem ext_zero (t₁ t₂ : ExtensionalSet) (α_zero : IsMin α) (h : t₁.pref.atoms = t₂.pref.atoms) :
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

/-- Construct a extensional set from an even code. -/
def intro {β : TypeIndex} [inst : LtLevel β] (s : Set (TSet β))
    (heven : (Code.mk β s).IsEven) : ExtensionalSet :=
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
theorem exts_intro (s : Set (TSet β)) (heven : IsEven (Code.mk β s)) :
    (intro s heven).members = extension s :=
  rfl

/-- Construct an extensional set from any set of t-sets of a smaller level.
This uses choice to find the even code representing the given set. -/
noncomputable def intro' {β : TypeIndex} [inst : LtLevel β] (s : Set (TSet β)) : ExtensionalSet :=
  ⟨extension (exists_even_equiv (Code.mk β s)).choose.members,
    match (exists_even_equiv (Code.mk β s)).choose,
      (exists_even_equiv (Code.mk β s)).choose_spec with
    | Code.mk (γ : Λ) t, h => Preference.proper γ
        (by rw [extension_self]; exact h.2)
        (by intro δ _ hδ; rw [extension_self, extension_ne _ _ hδ])
    | Code.mk ⊥ t, _ => Preference.base t (fun δ => rfl)⟩

@[simp]
theorem ext_intro' {β : Λ} [LtLevel β] (s : Set (TSet β)) :
    (intro' s).members β = s := by
  rw [intro']
  dsimp only
  set c := (exists_even_equiv (Code.mk β s)).choose with hc
  clear_value c
  have hc' := (exists_even_equiv (Code.mk β s)).choose_spec
  rw [← hc] at hc'
  obtain ⟨h, hc'⟩ := hc'
  suffices : extension c.members β = s
  · cases hc
    exact this
  cases h with
  | refl => rw [extension_self]
  | cloud_left _ h₁ δ h₂ =>
    have := h₁.cloudCode h₂
    cases not_isOdd.mpr hc' this
  | cloud_right => rfl
  | cloud_cloud c h₁ δ h₂ _ h₃ =>
    have := h₁.cloudCode h₂
    cases not_isOdd.mpr hc' this

end ExtensionalSet

/-!
## Allowable permutations on extensional sets
-/

open ExtensionalSet

variable [ModelData α]

namespace NewAllowable

/-!
We now establish that allowable permutations can act on extensional sets.
-/

variable {ρ : NewAllowable} {e : Extensions}

@[simp]
theorem smul_extension_apply (ρ : NewAllowable) (s : Set (TSet β)) :
    ρ.val γ • extension s γ = extension (ρ.val β • s) γ := by
  by_cases h : β = γ
  · subst h
    simp only [extension_eq, cast_eq]
  · rw [extension_ne _ _ h, extension_ne _ _ h, smul_cloud]

instance : MulAction Derivatives Extensions
    where
  smul ρ e γ := ρ γ • e γ
  one_smul e := by
    ext γ : 1
    change (1 : Derivatives) γ • e γ = e γ
    simp only [Derivatives.one_apply, one_smul]
  mul_smul ρ ρ' e := by
    ext γ : 1
    change (ρ * ρ') γ • e γ = ρ γ • ρ' γ • e γ
    simp only [Derivatives.mul_apply, mul_smul]

@[simp]
theorem smul_extension (ρ : NewAllowable) (s : Set (TSet β)) :
    ρ • extension s = extension (ρ.val β • s) := by
  ext γ : 2
  rw [← smul_extension_apply]
  rfl

theorem smul_aux₁ {s : Set (TSet ⊥)}
    (h : ∀ γ : Λ, [LtLevel γ] → cloud bot_ne_coe s = (e γ : Set (TSet γ))) (γ : Λ) [LtLevel γ] :
    cloud bot_ne_coe (ρ.val ⊥ • s) = (ρ • e) γ := by
  have := congr_arg (fun c => ρ.val γ • c) (h γ)
  dsimp only at this
  rw [smul_cloud] at this
  exact this

theorem smul_aux₂
    (h : ∀ (δ : Λ) [LtLevel δ] (hγδ : (γ : TypeIndex) ≠ δ),
      cloud hγδ (e γ) = (e δ : Set (TSet δ)))
    (δ : Λ) [LtLevel δ] (hγδ : (γ : TypeIndex) ≠ δ) : cloud hγδ ((ρ • e) γ) = (ρ • e) δ := by
  have := congr_arg (fun c => ρ.val δ • c) (h δ hγδ)
  dsimp only at this
  rw [smul_cloud] at this
  exact this

instance : SMul NewAllowable ExtensionalSet where
  smul ρ t := ⟨ρ • t.members, by
    obtain ⟨members, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩ := t
    · exact Preference.base (ρ.val ⊥ • s) (smul_aux₁ h)
    · exact Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩

@[simp]
theorem members_smul' (ρ : NewAllowable) (t : ExtensionalSet) : (ρ • t).members = ρ • t.members :=
  rfl

@[simp]
theorem smul_base (ρ : NewAllowable) (e : Extensions) (s h) :
    ρ • (⟨e, Preference.base s h⟩ : ExtensionalSet) =
      ⟨ρ • e, Preference.base (ρ.val ⊥ • s) (smul_aux₁ h)⟩ :=
  rfl

@[simp]
theorem smul_proper (ρ : NewAllowable) (e : Extensions) (γ : Λ) [LtLevel γ] (ht h) :
    ρ • (⟨e, Preference.proper γ ht h⟩ : ExtensionalSet) =
      ⟨ρ • e, Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩ :=
  rfl

/-- Allowable permutations act on extensional sets. -/
instance : MulAction NewAllowable ExtensionalSet
    where
  one_smul := by
    rintro ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · rw [smul_base]
      simp only [coe_one, Derivatives.one_apply, one_smul, ExtensionalSet.mk.injEq, true_and]
      refine Preference.base_heq_base ?_ ?_
      · rw [one_smul]
      · simp only [coe_one, Derivatives.one_apply, one_smul]
    · rw [smul_proper]
      simp only [ExtensionalSet.mk.injEq, one_smul, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [one_smul]
  mul_smul := by
    rintro ρ ρ' ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · simp only [smul_base, coe_mul, Derivatives.mul_apply, mul_smul, ExtensionalSet.mk.injEq,
      true_and]
      refine Preference.base_heq_base ?_ ?_
      · rw [mul_smul]
      · simp only [coe_mul, Derivatives.mul_apply, mul_smul]
    · simp only [smul_proper, ExtensionalSet.mk.injEq, mul_smul, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [mul_smul]

end NewAllowable

namespace ExtensionalSet

/-- Extensional sets can easily be turned into structural sets. -/
protected def toStructSet (t : ExtensionalSet) : StructSet α :=
  StructSet.ofCoe.symm (fun β hβ => match β with
    | ⊥ => {a | ∃ s : Set Atom, ∃ h, t.pref = Preference.base s h ∧ a ∈ s}
    | (β : Λ) => letI : LtLevel β := ⟨hβ⟩; {p | ∃ s ∈ t.members β, toStructSet s = p})

theorem toStructSet_ofCoe (t : ExtensionalSet) :
    StructSet.ofCoe t.toStructSet = fun β hβ => match β with
      | ⊥ => {a | ∃ s : Set Atom, ∃ h, t.pref = Preference.base s h ∧ a ∈ s}
      | (β : Λ) => letI : LtLevel β := ⟨hβ⟩; {p | ∃ s ∈ t.members β, toStructSet s = p} := by
  rw [ExtensionalSet.toStructSet, Equiv.apply_symm_apply]

/-- The members of extensional sets are determined by their underlying structural sets. -/
theorem members_eq_of_toStructSet_eq (t₁ t₂ : ExtensionalSet)
    (h : t₁.toStructSet = t₂.toStructSet) :
    t₁.members = t₂.members := by
  simp only [ExtensionalSet.toStructSet, StructSet.ofCoe_symm, exists_and_right,
    EmbeddingLike.apply_eq_iff_eq] at h
  ext γ iγ u : 2
  obtain ⟨u, rfl⟩ := exists_tangle_lt u
  have := Set.ext_iff.mp (congr_fun₂ h γ iγ.elim) (toStructSet u.set_lt)
  dsimp only at this
  constructor
  · intro hu
    obtain ⟨v, hv, huv⟩ := this.mp ⟨u.set, hu, rfl⟩
    cases toStructSet.injective huv
    exact hv
  · intro hu
    obtain ⟨v, hv, huv⟩ := this.mpr ⟨u.set, hu, rfl⟩
    cases toStructSet.injective huv
    exact hv

theorem toStructSet_injective : Function.Injective ExtensionalSet.toStructSet := by
  rintro t₁ t₂ h
  have := members_eq_of_toStructSet_eq t₁ t₂ h
  by_cases hγ : Nonempty ((γ : Λ) ×' LtLevel γ)
  · exact ext_core t₁ t₂ hγ this
  refine ext_zero t₁ t₂ ?_ ?_
  · intro δ _
    by_contra! hδ'
    exact hγ ⟨δ, ⟨coe_lt_coe.mpr hδ'⟩⟩
  obtain ⟨m, p₁⟩ := t₁
  obtain ⟨m, p₂⟩ := t₂
  cases this
  obtain (⟨a₁, ha₁⟩ | ⟨γ, _⟩) := p₁
  swap
  · cases hγ ⟨γ, inferInstance⟩
  obtain (⟨a₂, ha₂⟩ | ⟨γ, _⟩) := p₂
  swap
  · cases hγ ⟨γ, inferInstance⟩
  simp only [ExtensionalSet.toStructSet, StructSet.ofCoe_symm, Preference.base.injEq, exists_and_left,
    exists_prop, exists_eq_left', EmbeddingLike.apply_eq_iff_eq] at h
  have := congr_fun₂ h ⊥ (bot_lt_coe _)
  dsimp only at this
  dsimp only [Preference.atoms]
  ext a : 1
  constructor
  · intro ha
    refine ((Set.ext_iff.mp this a).mp ⟨?_, ha⟩).2
    intro γ _
    cases hγ ⟨γ, inferInstance⟩
  · intro ha
    refine ((Set.ext_iff.mp this a).mpr ⟨?_, ha⟩).2
    intro γ _
    cases hγ ⟨γ, inferInstance⟩

theorem toStructSet_smul (ρ : NewAllowable) (t : ExtensionalSet) :
    ρ • t.toStructSet = (ρ • t).toStructSet := by
  rw [← StructSet.ofCoe_inj, ExtensionalSet.toStructSet, ExtensionalSet.toStructSet]
  rw [Equiv.apply_symm_apply]
  ext β hβ : 2
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    rw [← NewAllowable.coe_smul]
    erw [StructPerm.ofCoe_smul]
    rw [Equiv.apply_symm_apply]
    dsimp only
    ext a : 1
    rw [mem_smul_set_iff_inv_smul_mem]
    constructor
    · rintro ⟨s, h, hpref, ha⟩
      refine ⟨Tree.comp (Quiver.Hom.toPath hβ) (Derivatives.toStructPerm ρ.val) • s,
          ?_, ?_, ?_⟩
      · intro γ _
        have := NewAllowable.smul_cloud (β := ⊥) (γ := γ) ρ s bot_ne_coe
        rw [h] at this
        exact this.symm
      · obtain ⟨exts, pref | pref⟩ := t
        · cases hpref
          rfl
        · cases hpref
      · rw [mem_smul_set_iff_inv_smul_mem]
        exact ha
    · rintro ⟨s, h, hpref, ha⟩
      refine ⟨(Tree.comp (Quiver.Hom.toPath hβ) (Derivatives.toStructPerm ρ.val))⁻¹ • s,
          ?_, ?_, ?_⟩
      · intro γ _
        have := NewAllowable.smul_cloud (β := ⊥) (γ := γ) ρ
          ((Tree.comp (Quiver.Hom.toPath hβ) (Derivatives.toStructPerm ρ.val))⁻¹ • s)
          bot_ne_coe
        rw [Derivatives.comp_toPath_toStructPerm] at this
        erw [smul_inv_smul] at this
        rw [h, NewAllowable.members_smul'] at this
        erw [smul_left_cancel_iff] at this
        exact this
      · obtain ⟨exts, pref | pref⟩ := t
        · cases hpref
          simp only [Tree.comp_bot, Tree.toBot_inv_smul, Preference.base.injEq]
          erw [smul_inv_smul]
        · cases hpref
      · simp only [Tree.comp_bot, Tree.toBot_inv_smul, smul_mem_smul_set_iff]
        exact ha
  · intro β hβ
    have : LtLevel β := ⟨hβ⟩
    rw [← NewAllowable.coe_smul]
    erw [StructPerm.ofCoe_smul]
    rw [Equiv.apply_symm_apply]
    dsimp only
    ext s : 1
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨ρ.val β • s, smul_mem_smul_set hs, ?_⟩
      rw [ConNF.toStructSet_smul, Derivatives.comp_toPath_toStructPerm]
      rfl
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
      rw [ConNF.toStructSet_smul, Derivatives.comp_toPath_toStructPerm]
      rfl

theorem smul_intro' {β : Λ} [inst : LtLevel β] (s : Set (TSet β)) (ρ : NewAllowable) :
    intro' (ρ.val β • s) = ρ • intro' s := by
  refine ExtensionalSet.ext (γ := β) _ _ ?_
  rw [NewAllowable.members_smul']
  change _ = ρ.val β • (intro' s).members β
  simp only [ext_intro']

end ExtensionalSet

/-!
## Defining t-sets
-/

/-- A tangle at the new level `α` is a extensional set supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
abbrev NewTSet : Type u :=
  { t : ExtensionalSet // ∃ S : Support α, MulAction.Supports NewAllowable (S : Set (Address α)) t }

variable {c d : Code} {S : Set (Address α)}

open MulAction

/-- If a set of addresses supports a code, it supports all equivalent codes. -/
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
    (∃ S : Support α, MulAction.Supports NewAllowable (S : Set (Address α)) c) ↔
    ∃ S : Support α, MulAction.Supports NewAllowable (S : Set (Address α)) d := by
  constructor <;> rintro ⟨S, hS⟩
  · exact ⟨S, hcd.supports hS⟩
  · exact ⟨S, hcd.symm.supports hS⟩

@[simp]
theorem smul_intro {β : TypeIndex} [inst : LtLevel β]  (ρ : NewAllowable) (s : Set (TSet β)) (hs) :
    ρ • intro s hs = intro (ρ.val β • s) (isEven_smul.mpr hs) := by
  induction β using WithBot.recBotCoe generalizing inst
  · simp only [intro, NewAllowable.smul_base, ExtensionalSet.mk.injEq, NewAllowable.smul_extension,
      true_and]
    refine Preference.base_heq_base ?_ rfl
    rw [NewAllowable.smul_extension]
  · simp only [intro, NewAllowable.smul_proper, ExtensionalSet.mk.injEq, NewAllowable.smul_extension,
      true_and]
    refine Preference.proper_heq_proper ?_ rfl
    rw [NewAllowable.smul_extension]

theorem NewAllowable.smul_address {ρ : NewAllowable} {c : Address α} :
    ρ • c = ⟨c.path, NewAllowable.toStructPerm ρ c.path • c.value⟩ :=
  rfl

@[simp]
theorem NewAllowable.smul_address_eq_iff {ρ : NewAllowable} {c : Address α} :
    ρ • c = c ↔ NewAllowable.toStructPerm ρ c.path • c.value = c.value :=
  StructPerm.smul_address_eq_iff

@[simp]
theorem NewAllowable.smul_address_eq_smul_iff
    {ρ ρ' : NewAllowable} {c : Address α} :
    ρ • c = ρ' • c ↔
    NewAllowable.toStructPerm ρ c.path • c.value =
      NewAllowable.toStructPerm ρ' c.path • c.value :=
  StructPerm.smul_address_eq_smul_iff

/-- For any near-litter `N`, the code `(α, ⊥, N)` is a tangle at level `α`.
This is called a *typed near-litter*. -/
def newTypedNearLitter (N : NearLitter) : NewTSet :=
  ⟨intro (show Set (TSet ⊥) from N.2.1) <| Code.isEven_bot _,
    Enumeration.singleton ⟨Quiver.Hom.toPath (bot_lt_coe _), Sum.inr N⟩,
    by
      intro ρ h
      simp only [smul_intro]
      congr 1
      simp only [Enumeration.singleton_carrier, mem_singleton_iff, NewAllowable.smul_address_eq_iff,
        forall_eq, Sum.smul_inr, Sum.inr.injEq] at h
      apply_fun SetLike.coe at h
      refine Eq.trans ?_ h
      rw [BasePerm.smul_nearLitter_coe]
      change _ '' _ = _ '' _
      simp_rw [Derivatives.coe_apply_bot]
      rfl⟩

theorem preferenceBase_injective {a₁ a₂ : Set Atom}
    {e₁ e₂ : ∀ (γ : Λ), [LtLevel γ] → Set (TSet γ)} (he : e₁ = e₂)
    {h₁ : ∀ (γ : Λ), [LtLevel γ] → cloud bot_ne_coe a₁ = e₁ γ}
    {h₂ : ∀ (γ : Λ), [LtLevel γ] → cloud bot_ne_coe a₂ = e₂ γ}
    (h : HEq (Preference.base a₁ h₁) (Preference.base a₂ h₂)) : a₁ = a₂ := by
  cases he
  simp only [heq_eq_eq, Preference.base.injEq] at h
  exact h

theorem newTypedNearLitter_injective : Function.Injective newTypedNearLitter := by
  intro N₁ N₂ h
  simp only [newTypedNearLitter, intro] at h
  rw [Subtype.mk_eq_mk] at h
  simp only [ExtensionalSet.mk.injEq] at h
  have := preferenceBase_injective h.1 h.2
  simp only [singleton_eq_singleton_iff] at this
  exact NearLitter.ext this

def newSingleton' (β : TypeIndex) [i : LtLevel β] (t : Tangle β) : NewTSet :=
  ⟨intro {t.set_lt} (isEven_singleton t.set_lt),
    t.support.image (fun c => ⟨(Quiver.Hom.toPath i.elim).comp c.1, c.2⟩),
    by
      intro ρ h
      simp only [smul_intro, smul_set_singleton]
      congr 1
      rw [singleton_eq_singleton_iff]
      have := Tangle.support_supports_lt t (ρ.val β) ?_
      · refine Eq.trans ?_ (congr_arg Tangle.set_lt this)
        rw [Tangle.set_lt_smul]
      · rintro _ ⟨i, hi, rfl⟩
        have := h ⟨i, hi, rfl⟩
        simp only [Enumeration.image_f, NewAllowable.smul_address_eq_iff] at this
        rw [Allowable.smul_address_eq_iff, ← Derivatives.comp_toPath_toStructPerm]
        exact this⟩

noncomputable def newSingleton (β : TypeIndex) [LtLevel β] (t : TSet β) : NewTSet :=
  newSingleton' β (exists_tangle_lt t).choose

namespace NewAllowable

instance hasSmulNewTSet : SMul NewAllowable NewTSet :=
  ⟨fun ρ t =>
    ⟨ρ • (t : ExtensionalSet),
      by
        obtain ⟨S, hS⟩ := t.prop
        refine ⟨ρ • S, ?_⟩
        intro ρ' h
        have := hS (ρ⁻¹ * ρ' * ρ) ?_
        · conv_rhs =>
            rw [← this, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_self, one_mul, mul_smul]
        · intro a ha
          rw [mul_smul, mul_smul, inv_smul_eq_iff]
          exact h (Enumeration.smul_mem_smul ha ρ)⟩⟩

@[simp]
theorem coe_smul_newTangle (ρ : NewAllowable) (t : NewTSet) :
    ((ρ • t) : ExtensionalSet) = ρ • (t : ExtensionalSet) :=
  rfl

@[simp]
theorem smul_newTangle_t (ρ : NewAllowable) (t : NewTSet) :
    (ρ • t : NewTSet) = ρ • (t : ExtensionalSet) :=
  rfl

/-- Allowable permutations act on t-sets at level `α`. -/
instance : MulAction NewAllowable NewTSet where
  one_smul t := by
    refine Subtype.ext ?_
    simp only [smul_newTangle_t, one_smul]
  mul_smul ρ₁ ρ₂ t := by
    refine Subtype.ext ?_
    simp only [smul_newTangle_t, mul_smul]

theorem smul_newTypedNearLitter (N : NearLitter) (ρ : NewAllowable) :
    ρ • newTypedNearLitter N =
      newTypedNearLitter (NewAllowable.toStructPerm ρ (Quiver.Hom.toPath (bot_lt_coe _)) • N) := by
  refine Subtype.ext ?_
  have := BasePerm.smul_nearLitter_coe
    (NewAllowable.toStructPerm ρ (Quiver.Hom.toPath (bot_lt_coe _))) N
  simp only [newTypedNearLitter, smul_newTangle_t, smul_intro,
    BasePerm.smul_nearLitter_fst, toStructPerm, MonoidHom.coe_comp, comp_apply,
    coeHom_apply, Derivatives.coe_apply_bot ρ] at this ⊢
  congr 1
  exact this.symm

end NewAllowable

protected def NewTSet.toStructSet (t : NewTSet) : StructSet α :=
  t.val.toStructSet

theorem NewTSet.toStructSet_injective : Function.Injective NewTSet.toStructSet :=
  fun _ _ h => Subtype.ext (ExtensionalSet.toStructSet_injective h)

theorem NewTSet.toStructSet_smul (ρ : NewAllowable) (t : NewTSet) :
    (ρ • t).toStructSet = ρ • t.toStructSet :=
  (t.val.toStructSet_smul ρ).symm

/-- The t-sets at level `α` are extensional at all lower proper type indices. -/
theorem NewTSet.ext (γ : Λ) [iγ : LtLevel γ] (t₁ t₂ : NewTSet)
    (h : ∀ p, p ∈ StructSet.ofCoe t₁.toStructSet γ iγ.elim ↔
      p ∈ StructSet.ofCoe t₂.toStructSet γ iγ.elim) :
    t₁ = t₂ := by
  refine Subtype.ext (ExtensionalSet.ext (γ := γ) t₁ t₂ ?_)
  simp only [NewTSet.toStructSet, ExtensionalSet.toStructSet, StructSet.ofCoe_symm, exists_and_right,
    StructSet.ofCoe_toCoe] at h
  ext u
  constructor
  · intro hu
    obtain ⟨v, hv, huv⟩ := (h (toStructSet u)).mp ⟨u, hu, rfl⟩
    cases toStructSet.injective huv
    exact hv
  · intro hu
    obtain ⟨v, hv, huv⟩ := (h (toStructSet u)).mpr ⟨u, hu, rfl⟩
    cases toStructSet.injective huv
    exact hv

theorem NewTSet.newSingleton'_toStructSet
    (β : TypeIndex) [i : LtLevel β] (t : Tangle β) :
    StructSet.ofCoe (NewTSet.toStructSet (newSingleton' β t)) β i.elim =
    {toStructSet t.set_lt} := by
  rw [newSingleton', NewTSet.toStructSet, ExtensionalSet.toStructSet]
  simp only [StructSet.ofCoe_symm, exts_intro, exists_and_right, StructSet.ofCoe_toCoe]
  cases β
  · dsimp only
    ext p : 1
    constructor
    · rintro ⟨s, ⟨hs₁, hs₂⟩, hps⟩
      simp only [intro, Preference.base.injEq] at hs₂
      cases hs₂
      cases hps
      rfl
    · rintro rfl
      refine ⟨{p}, ⟨?_, rfl⟩, rfl⟩
      intro γ _
      rw [extension_ne]
      rfl
  · simp only [extension_self, mem_singleton_iff, exists_eq_left, setOf_eq_eq_singleton',
      singleton_eq_singleton_iff]
    rfl

theorem NewTSet.newSingleton_toStructSet
    (β : TypeIndex) [i : LtLevel β] (t : TSet β) :
    StructSet.ofCoe (NewTSet.toStructSet (newSingleton β t)) β i.elim = {toStructSet t} := by
  rw [newSingleton, newSingleton'_toStructSet, (exists_tangle_lt t).choose_spec]

/-- The main introduction rule for t-sets at level `α`. -/
noncomputable def NewTSet.intro {β : Λ} [LtLevel β] (s : Set (TSet β))
    (hs : ∃ S : Set (Address α), Small S ∧
      ∀ ρ : NewAllowable, (∀ c ∈ S, ρ • c = c) → ρ.val β • s = s) :
    NewTSet :=
  ⟨ExtensionalSet.intro' s, by
    obtain ⟨S, h₁, h₂⟩ := hs
    refine ⟨Enumeration.ofSet S h₁, ?_⟩
    intro ρ hρ
    refine ExtensionalSet.ext (γ := β) _ _ ?_
    rw [← smul_intro', ext_intro', ext_intro']
    refine h₂ ρ ?_
    intro c hc
    refine hρ ?_
    rw [Enumeration.ofSet_coe]
    exact hc⟩

@[simp]
theorem NewTSet.intro_members {β : Λ} [LtLevel β] (s : Set (TSet β))
    (hs : ∃ S : Set (Address α), Small S ∧
      ∀ ρ : NewAllowable, (∀ c ∈ S, ρ • c = c) → ρ.val β • s = s) :
    (intro s hs).val.members β = s :=
  ExtensionalSet.ext_intro' _

end ConNF
