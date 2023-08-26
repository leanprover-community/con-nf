import Mathlib.GroupTheory.GroupAction.Option
import ConNF.Mathlib.GroupAction
import ConNF.Mathlib.Pointwise
import ConNF.NewTangle.Allowable

open Function Set WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] [PositionData]

open Code IioBot

variable (α : Λ) [CoreTangleCumul α] {β : IioBot α} {γ : Iio α}

abbrev Extensions :=
  ∀ β : Iio α, Set (Tangle β)

namespace Semitangle

variable [PositionedTangleCumul α] [AlmostTangleCumul α]

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
inductive Preference (members : Extensions α)
  | base (atoms : Set (Tangle (⊥ : IioBot α))) :
    (∀ γ, cloud bot_ne_coe atoms = members γ) → Preference members
  | proper (β : Iio α) :
    (mk β (members β) : Code α).IsEven →
    (∀ (γ : Iio α) (hβγ : iioCoe β ≠ γ), cloud hβγ (members β) = members γ) →
    Preference members

variable {α}
variable {members : Extensions α}

/-- The `-1`-extension associated with a given semitangle extension. -/
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

variable [PositionedTangleCumul α] [AlmostTangleCumul α]

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`. -/
structure Semitangle where
  members : Extensions α
  pref : Preference α members

variable {α}

namespace Semitangle

/-- The membership relation for nonempty semitangles. -/
def Mem (t : Tangle γ) (s : Semitangle α) : Prop :=
  t ∈ s.members γ

notation:50 t " ∈ₛₜ " s:50 => Mem t s

/-- The even code associated to a nonempty semitangle. -/
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

theorem reprCodeSpec : ∀ s : Semitangle α, (reprCode s : Code α).IsEven
  | ⟨_, Preference.proper _ rep _⟩ => rep
  | ⟨_, Preference.base _ _⟩ => isEven_bot _

theorem reprCode_members_ne :
    ∀ (s : Semitangle α) (γ : Iio α) (_ : (reprCode s : Code α).1 ≠ γ),
      (cloudCode γ (reprCode s)).2 = s.members γ
  | ⟨exts, Preference.proper β rep hA⟩, γ, hcγ => by
      rw [snd_cloudCode]
      exact hA _ hcγ
  | ⟨_, Preference.base _ hA⟩, γ, _ => hA _

/-- Remark: This formulation of extensionality holds only for types larger than type zero, since
it doesn't take into account any `-1`-extension. -/
theorem ext_core (x y : Semitangle α) : (∃ γ, γ < α) → x.members = y.members → x = y := by
  obtain ⟨xs, hxs⟩ := x
  obtain ⟨ys, hys⟩ := y
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

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
theorem ext_code : ∀ {x y : Semitangle α}, (reprCode x : Code α) ≡ reprCode y → x = y
  | ⟨x, Preference.base atoms₁ hA₁⟩, ⟨y, Preference.base atoms₂ hA₂⟩, h => by
    obtain rfl := Code.Equiv.bot_bot_iff.1 h
    obtain rfl : x = y := funext fun γ => (hA₁ _).symm.trans <| hA₂ _
    rfl
  | ⟨x, Preference.base s hA₁⟩, ⟨y, Preference.proper γ even₂ hA₂⟩, h => by
    change Code.mk _ _ ≡ Code.mk _ _ at h
    obtain ⟨δ, hδ⟩ :=
      (Code.Equiv.bot_left_iff.1 h).resolve_left (ne_of_apply_ne Sigma.fst bot_ne_mk_coe)
    rw [hδ] at even₂
    cases even₂.not_isOdd ((isEven_bot _).cloudCode bot_ne_mk_coe)
  | ⟨x, Preference.proper γ even₁ hA₁⟩, ⟨y, Preference.base s hA₂⟩, h => by
    change Code.mk _ _ ≡ Code.mk _ _ at h
    obtain ⟨δ, hδ⟩ :=
      (Code.Equiv.bot_right_iff.1 h).resolve_left (ne_of_apply_ne Sigma.fst mk_coe_ne_bot)
    rw [hδ] at even₁
    cases even₁.not_isOdd ((isEven_bot _).cloudCode bot_ne_mk_coe)
  | ⟨x, Preference.proper γ even₁ hA₁⟩, ⟨y, Preference.proper δ even₂ hA₂⟩, h => by
    dsimp at h
    simp only [Equiv_iff, WithBot.coe_ne_bot, ne_eq, Subtype.mk.injEq, coe_inj, Subtype.coe_inj,
      Subtype.exists, mem_Iio] at h
    obtain h | ⟨_, γ, _, hδγ, h⟩ | ⟨_, δ, _, hγδ, h⟩ |
      ⟨c, hc, γ, hcγ, hc', δ, hcδ, h⟩ := h
    · rw [Sigma.ext_iff] at h
      simp only [Subtype.mk.injEq, coe_inj, Subtype.coe_inj] at h
      obtain rfl := h.1
      suffices x = y by subst this; rfl
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
    · --rw [hx.eq] at even₁
      rw [Sigma.ext_iff] at h
      simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, ne_eq] at h
      obtain rfl := h.2.1.1
      rw [eq_of_heq h.2.1.2] at even₁
      cases (hc.cloudCode hc').not_isEven even₁

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `γ < α`.
TODO: This proof can be golfed quite a bit just by cleaning up the `simp` calls. -/
theorem ext (x y : Semitangle α) (h : x.members γ = y.members γ) : x = y := by
  obtain ⟨xs, hxs⟩ := x
  obtain ⟨ys, hys⟩ := y
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

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
theorem ext' (x y : Semitangle α) (h : ∀ t : Tangle γ, t ∈ₛₜ x ↔ t ∈ₛₜ y) : x = y :=
  ext x y <| Set.ext h

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all nonempty semitangles have a `-1`-extension.
Therefore, the extensionality principle in this case applies to the `-1`-extensions. -/
theorem ext_zero (x y : Semitangle α) (α_zero : IsMin α) (h : x.pref.atoms = y.pref.atoms) :
    x = y := by
  obtain ⟨xs, ⟨atoms₁, hA₁⟩ | ⟨γ, _, _⟩⟩ := x
  swap
  · cases α_zero.not_lt γ.2
  obtain ⟨ys, ⟨atoms₂, hA₂⟩ | ⟨γ, _, _⟩⟩ := y
  swap
  · cases α_zero.not_lt γ.2
  have : atoms₁ = atoms₂ := h
  subst this
  suffices xs = ys by subst this; rfl
  funext β
  cases α_zero.not_lt β.2

/-- Construct a semitangle from an even nonempty code. -/
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
theorem exts_intro (s : Set (Tangle β)) (heven) : (intro s heven).members = extension s :=
  rfl

end Semitangle

open Semitangle

variable [CoreTangleData α]

namespace AllowablePerm

variable {f : AllowablePerm α} {e : Extensions α}

@[simp]
theorem smul_extension_apply (f : AllowablePerm α) (s : Set (Tangle β)) :
    f • extension s γ = extension (f • s) γ := by
  by_cases β = γ
  · subst h
    simp only [extension_eq, cast_eq]
  · rw [extension_ne _ _ h, extension_ne _ _ h, smul_cloud]

@[simp]
theorem smul_extension (f : AllowablePerm α) (s : Set (Tangle β)) :
    f • extension s = extension (f • s) := by
  ext γ : 1
  rw [← smul_extension_apply]
  rfl

theorem smul_aux₁ {s : Set (Tangle (⊥ : IioBot α))}
    (h : ∀ γ : Iio α, cloud bot_ne_coe s = (e γ : Set (Tangle (iioCoe γ)))) (γ : Iio α) :
    cloud bot_ne_coe (f • s) = (f • e) γ := by
  simpa only [smul_cloud] using congr_arg (fun c => f • c) (h γ)

theorem smul_aux₂
    (h : ∀ (δ : Iio α) (hγδ : iioCoe γ ≠ δ), cloud hγδ (e γ) = (e δ : Set (Tangle (iioCoe δ))))
    (δ : Iio α) (hγδ : iioCoe γ ≠ δ) : cloud hγδ ((f • e) γ) = (f • e) δ := by
  simpa only [smul_cloud] using congr_arg (fun c => f • c) (h δ hγδ)

/-- Allowable permutations act on semitangles. -/
noncomputable instance : SMul (AllowablePerm α) (Semitangle α)
    where smul f t :=
    ⟨f • t.members, by
      obtain ⟨members, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩ := t
      · exact Preference.base (f • s) (smul_aux₁ h)
      · exact Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩

@[simp]
theorem members_smul (f : AllowablePerm α) (s : Semitangle α) : (f • s).members = f • s.members :=
  rfl

@[simp]
theorem smul_base (f : AllowablePerm α) (e : Extensions α) (s h) :
    f • (⟨e, Preference.base s h⟩ : Semitangle α) =
      ⟨f • e, Preference.base (f • s) (smul_aux₁ h)⟩ :=
  rfl

@[simp]
theorem smul_proper (f : AllowablePerm α) (e : Extensions α) (γ ht h) :
    f • (⟨e, Preference.proper γ ht h⟩ : Semitangle α) =
      ⟨f • e, Preference.proper _ (isEven_smul.mpr ht) (smul_aux₂ h)⟩ :=
  rfl

noncomputable instance mulActionSemitangle : MulAction (AllowablePerm α) (Semitangle α)
    where
  one_smul := by
    rintro ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · rw [smul_base]
      simp only [one_smul, mk.injEq, true_and]
      refine Preference.base_heq_base ?_ rfl
      rw [one_smul]
    · rw [smul_proper]
      simp only [one_smul, mk.injEq, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [one_smul]
  mul_smul := by
    rintro f g ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · simp only [smul_base, mul_smul, mk.injEq, true_and]
      refine Preference.base_heq_base ?_ rfl
      rw [mul_smul]
    · simp only [smul_proper, mk.injEq, mul_smul, true_and]
      refine Preference.proper_heq_proper ?_ rfl
      rw [mul_smul]

end AllowablePerm

variable (α)

/-- A tangle at the new level `α` is a semitangle supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def NewTangle :=
  { s : Semitangle α // Supported α (AllowablePerm α) s }

variable {α}
variable {c d : Code α} {S : Set (SupportCondition α)}

open MulAction

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected theorem Code.Equiv.supports (hcd : c ≡ d) (hS : Supports (AllowablePerm α) S c) :
    Supports (AllowablePerm α) S d := fun f h =>
  (((f.2 _ _).mpr hcd).symm.trans <| (Code.Equiv.of_eq <| hS f h).trans hcd).unique rfl

theorem Code.Equiv.supports_iff (hcd : c ≡ d) :
    Supports (AllowablePerm α) S c ↔ Supports (AllowablePerm α) S d :=
  ⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
theorem Code.Equiv.supported_iff (hcd : c ≡ d) :
    Supported α (AllowablePerm α) c ↔ Supported α (AllowablePerm α) d :=
  ⟨fun ⟨⟨s, hs, h⟩⟩ => ⟨⟨s, hs, hcd.supports h⟩⟩,
    fun ⟨⟨s, hs, h⟩⟩ => ⟨⟨s, hs, hcd.symm.supports h⟩⟩⟩

@[simp]
theorem smul_intro (f : AllowablePerm α) (s : Set (Tangle β)) (hs) :
    f • intro s hs = intro (f • s) (isEven_smul.mpr hs) := by
  obtain ⟨β, hβ⟩ := β
  induction β using WithBot.recBotCoe
  · simp only [intro, AllowablePerm.smul_base, mk.injEq, AllowablePerm.smul_extension, true_and]
    refine Preference.base_heq_base ?_ rfl
    rw [AllowablePerm.smul_extension]
  · simp only [intro, AllowablePerm.smul_proper, mk.injEq, AllowablePerm.smul_extension, true_and]
    refine Preference.proper_heq_proper ?_ rfl
    rw [AllowablePerm.smul_extension]

-- TODO: Move next two lemmas elsewhere.
theorem allowableToStructPerm_bot (π : Allowable (⊥ : IioBot α)) :
    CoreTangleData.allowableToStructPerm π = StructPerm.toBotIso.toMonoidHom π :=
  rfl

theorem _root_.ConNF.SemiallowablePerm.coe_apply_bot (π : SemiallowablePerm α) :
    (π : SemiallowablePerm α) ⊥ =
      SemiallowablePerm.toStructPerm π (Quiver.Hom.toPath (bot_lt_coe _)) := by
  rfl

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def newTypedNearLitter (N : NearLitter) : NewTangle α :=
  ⟨intro (show Set (Tangle (⊥ : IioBot α)) from N.2.1) <| Code.isEven_bot _,
    ⟨⟨{(Sum.inr N, default)}, small_singleton _, fun π h => by
        simp only [smul_intro]
        congr 1
        have : Sum.inr _ = _ := congr_arg Prod.fst (h rfl)
        simp only [AllowablePerm.coeHom_apply, Sum.inr.injEq] at this
        apply_fun SetLike.coe at this
        refine Eq.trans ?_ this
        rw [NearLitterPerm.smul_nearLitter_coe]
        change (fun x => (π : SemiallowablePerm α) ⊥ • x) '' _ = (fun x => π • x) '' _
        simp_rw [SemiallowablePerm.coe_apply_bot]
        rfl⟩⟩⟩

/-- For any supported tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def supportedSingleton (x : Tangle β) (supp : Supported α (AllowablePerm α) x) : NewTangle α :=
  ⟨intro {x} (Code.isEven_singleton _), by
    obtain ⟨s, hs₁, hs₂⟩ := supp
    refine ⟨⟨s, hs₁, fun π h => ?_⟩⟩
    conv_rhs => rw [← hs₂ π h]
    simp only [smul_set_singleton, smul_nonempty_mk, Option.smul_some, smul_intro]⟩

/-- For any small set `B` of supported `β`-tangles, the code `(α, β, B)` is a tangle at level `α` if
it is even. -/
def supportedSet (s : Set (Tangle β)) (hs : Small s) (hc : (mk β s).IsEven)
    (symm : ∀ b ∈ s, Supported α (AllowablePerm α) b) : NewTangle α :=
  ⟨intro s hc, by
    have symm : ∀ b ∈ s, Support α (AllowablePerm α) b
    · intro b hb
      exact (symm b hb).some
    refine' ⟨⟨⋃ b ∈ s, symm b ‹_›, hs.bUnion fun i hi => (symm _ _).small, fun π h => _⟩⟩
    suffices π • s = s by simp only [Option.smul_some, smul_intro, Option.some_inj, this]
    have : ∀ x ∈ s, π • x = x := by
      intro x hx
      refine (symm x hx).supports π ?_
      intro a ha
      refine h ?_
      simp only [mem_iUnion, SetLike.mem_coe]
      exact ⟨x, hx, ha⟩
    ext t : 2
    refine ⟨fun ht => ?_, fun ht => ?_⟩
    · have := this (π⁻¹ • t) ?_
      · rw [smul_inv_smul] at this
        rw [this]
        rwa [← mem_smul_set_iff_inv_smul_mem]
      · rwa [← mem_smul_set_iff_inv_smul_mem]
    · rw [← this t ht]
      exact smul_mem_smul_set ht⟩

namespace NewTangle

instance : Coe (NewTangle α) (Semitangle α)
    where
  coe := Subtype.val

theorem coe_injective : Injective (Subtype.val : NewTangle α → Semitangle α) :=
  Subtype.coe_injective

end NewTangle

namespace AllowablePerm

--Yaël: I suspect we can generalize `supports.smul` so that it applies here
/-- Allowable permutations act on `α`-tangles. -/
noncomputable instance hasSmulNewTangle : SMul (AllowablePerm α) (NewTangle α) :=
  ⟨fun π t =>
    ⟨π • (t : Semitangle α),
      t.2.map fun (s : Support α (AllowablePerm α) (t : Semitangle α)) =>
        { carrier := π • (s : Set (SupportCondition α))
          small := s.small.image
          supports := by
            intro σ h
            have := s.supports (π⁻¹ * σ * π) ?_
            · conv_rhs =>
                rw [← this, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_self, one_mul, mul_smul]
            · intro a ha
              rw [mul_smul, mul_smul, inv_smul_eq_iff]
              exact h (smul_mem_smul_set ha) }⟩⟩

@[simp, norm_cast]
theorem coe_smul_newTangle (f : AllowablePerm α) (t : NewTangle α) :
    ((f • t) : Semitangle α) = f • (t : Semitangle α) :=
  rfl

noncomputable instance mulActionNewTangle : MulAction (AllowablePerm α) (NewTangle α) :=
  NewTangle.coe_injective.mulAction Subtype.val coe_smul_newTangle

end AllowablePerm

end ConNF
