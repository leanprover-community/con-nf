import Mathlib.GroupTheory.GroupAction.Option
import ConNF.Mathlib.GroupAction
import ConNF.Mathlib.Pointwise
import ConNF.Phase1.Allowable

#align_import phase1.tangle

noncomputable section

open Function Set WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] [PositionData]

open Code IioIndex

variable (α : Λ) [CoreTangleCumul α] {β : IioBot α} {γ : Iio α}

abbrev Extensions :=
  ∀ β : Iio α, Set (Tangle β)

namespace Semitangle

variable [PositionedTangleCumul α] [AlmostTangleCumul α]

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
@[nolint has_nonempty_instance]
inductive Preference (members : Extensions α)
  |
  base (atoms : Set (Tangle (⊥ : IioBot α))) :
    (∀ γ, aMap bot_ne_coe atoms = members γ) → preference
  |
  proper (β : Iio α) :
    (mk β (members β) : Code α).IsEven →
      (∀ (γ : Iio α) (hβγ : iioCoe β ≠ γ), aMap hβγ (members β) = members γ) → preference

variable {α} {members : Extensions α}

/-- The `-1`-extension associated with a given semitangle extension. -/
def Preference.atoms : Preference α members → Set Atom
  | preference.base atoms _ => (atoms : Set (Tangle ⊥))
  | preference.proper _ _ _ => ∅

theorem Preference.base_hEq_base {m₁ m₂ : Extensions α} {s₁ s₂ h₁ h₂} (hm : m₁ = m₂)
    (hs : s₁ = s₂) :
    HEq (Preference.base s₁ h₁ : Preference α m₁) (Preference.base s₂ h₂ : Preference α m₂) := by
  cases hm <;> cases hs <;> rfl

theorem Preference.proper_hEq_proper {m₁ m₂ : Extensions α} {β₁ β₂ h₁ h₂ h₃ h₄} (hm : m₁ = m₂)
    (hs : β₁ = β₂) :
    HEq (Preference.proper β₁ h₁ h₂ : Preference α m₁)
      (Preference.proper β₂ h₃ h₄ : Preference α m₂) :=
  by cases hm <;> cases hs <;> rfl

end Semitangle

open Semitangle

variable [PositionedTangleCumul α] [AlmostTangleCumul α]

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`. -/
@[nolint has_nonempty_instance]
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
  | ⟨exts, preference.base atoms hA⟩ => ⟨⊥, atoms⟩
  | ⟨exts, preference.proper β rep hA⟩ => ⟨β, exts β⟩

@[simp]
theorem reprCode_base (exts : Extensions α) (atoms hA) :
    reprCode ⟨exts, Preference.base atoms hA⟩ = ⟨⊥, atoms⟩ :=
  rfl

@[simp]
theorem reprCode_proper (exts : Extensions α) (β rep hA) :
    reprCode ⟨exts, Preference.proper β rep hA⟩ = ⟨β, exts β⟩ :=
  rfl

theorem reprCodeSpec : ∀ s : Semitangle α, (reprCode s : Code α).IsEven
  | ⟨exts, preference.proper β rep hA⟩ => rep
  | ⟨exts, preference.base atoms hA⟩ => isEvenBot _

theorem reprCode_members_ne :
    ∀ (s : Semitangle α) (γ : Iio α) (hcγ : (reprCode s : Code α).1 ≠ γ),
      (aMapCode γ (reprCode s)).2 = s.members γ
  | ⟨exts, preference.proper β rep hA⟩, γ, hcγ => by rw [snd_A_map_code] <;> exact hA _ hcγ
  | ⟨exts, preference.base atoms hA⟩, γ, hcγ => hA _

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
theorem ext_core (x y : Semitangle α) : (∃ γ, γ < α) → x.members = y.members → x = y :=
  by
  obtain ⟨xs, hxs⟩ := x
  obtain ⟨ys, hys⟩ := y
  dsimp
  rintro ⟨γ, hγ⟩ rfl
  have γ : Iio α := ⟨γ, hγ⟩
  refine' congr_arg (fun h => ⟨xs, h⟩) _
  obtain ⟨atoms₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs <;> obtain ⟨atoms₂, hA₂⟩ | ⟨γ, even₂, hA₂⟩ := hys
  · simp_rw [A_map_injective ((hA₁ γ).trans (hA₂ _).symm)]
  · cases (is_even_bot _).aMapCode_ne even₂ bot_ne_mk_coe (Sigma.ext_iff.2 ⟨rfl, (hA₁ γ).HEq⟩)
  · cases (is_even_bot _).aMapCode_ne even₁ bot_ne_mk_coe (Sigma.ext_iff.2 ⟨rfl, (hA₂ β).HEq⟩)
  · simp only
    refine'
      not_ne_iff.1 fun hβγ =>
        even₂.A_map_code_ne even₁ (Iio.coe_injective.ne hβγ.symm) <|
          Sigma.ext_iff.2 ⟨rfl, hEq_of_eq _⟩
    rw [snd_A_map_code]
    exact hA₂ β fun h => hβγ.symm (Iio.coe_injective h)

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
theorem ext_code : ∀ {x y : Semitangle α}, (reprCode x : Code α) ≡ reprCode y → x = y
  | ⟨x, preference.base atoms₁ hA₁⟩, ⟨y, preference.base atoms₂ hA₂⟩, h =>
    by
    obtain rfl := code.equiv.bot_bot_iff.1 h
    obtain rfl : x = y := funext fun γ => (hA₁ _).symm.trans <| hA₂ _
    rfl
  | ⟨x, preference.base s hA₁⟩, ⟨y, preference.proper γ even₂ hA₂⟩, h =>
    by
    change code.mk _ _ ≡ code.mk _ _ at h
    obtain ⟨δ, hδ⟩ :=
      (code.equiv.bot_left_iff.1 h).resolve_left (ne_of_apply_ne Sigma.fst bot_ne_mk_coe)
    rw [hδ] at even₂
    cases even₂.not_is_odd ((is_even_bot _).aMapCode bot_ne_mk_coe)
  | ⟨x, preference.proper γ even₁ hA₁⟩, ⟨y, preference.base s hA₂⟩, h =>
    by
    change code.mk _ _ ≡ code.mk _ _ at h
    obtain ⟨δ, hδ⟩ :=
      (code.equiv.bot_right_iff.1 h).resolve_left (ne_of_apply_ne Sigma.fst mk_coe_ne_bot)
    rw [hδ] at even₁
    cases even₁.not_is_odd ((is_even_bot _).aMapCode bot_ne_mk_coe)
  | ⟨x, preference.proper γ even₁ hA₁⟩, ⟨y, preference.proper δ even₂ hA₂⟩, h =>
    by
    dsimp at h
    simp only [code.equiv_iff, Sigma.ext_iff, mem_Iio, Iio.coe_inj, Ne.def, fst_A_map_code,
      snd_A_map_code, Iio.coe_mk] at h
    obtain ⟨rfl, h⟩ | ⟨-, γ, hδγ, rfl, h⟩ | ⟨-, δ, hγδ, rfl, h⟩ |
      ⟨c, hc, γ, hcγ, δ, hcδ, ⟨⟨rfl, hx'⟩, hx⟩, _⟩ := h
    · suffices x = y by subst this
      refine' funext fun ε => _
      obtain rfl | hδε := eq_or_ne δ ε
      · exact h.eq.symm
      refine'
        (hA₁ _ fun h => hδε (Iio.coe_injective h)).symm.trans
          (Eq.trans _ <| hA₂ _ fun h => hδε (Iio.coe_injective h))
      dsimp
      rw [h.eq]
    · rw [h.eq] at even₁
      cases (even₂.A_map_code <| Iio.coe_injective.ne hδγ).not_isEven even₁
    · rw [h.eq] at even₂
      cases (even₁.A_map_code <| Iio.coe_injective.ne hγδ).not_isEven even₂
    · rw [hx.eq] at even₁
      cases (hc.A_map_code hcγ).not_isEven even₁

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `γ < α`.
TODO: This proof can be golfed quite a bit just by cleaning up the `simp` calls. -/
theorem ext (x y : Semitangle α) (h : x.members γ = y.members γ) : x = y :=
  by
  obtain ⟨xs, hxs⟩ := x
  obtain ⟨ys, hys⟩ := y
  dsimp only at h
  refine' ext_code _
  obtain ⟨atoms₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs <;> obtain ⟨atoms₂, hA₂⟩ | ⟨δ, even₂, hA₂⟩ := hys
  · refine' (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _
    simp only [Ne.def, Iio_index.bot_ne_coe, not_false_iff, A_map_code_mk_ne, repr_code_base,
      Subtype.coe_mk]
    rw [hA₁ γ, h, ← hA₂ γ]
    exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe
  · simp only [repr_code_base, Subtype.coe_mk, repr_code_proper]
    obtain rfl | hδγ := eq_or_ne δ γ
    · simp only [is_even_bot, mem_Iio, Subtype.val_eq_coe, SetCoe.forall, Ne.def, Iio.coe_inj] at *
      have := hA₁ δ δ.prop
      rw [Subtype.coe_eta] at this
      rw [← h, ← this]
      exact code.equiv.A_map_right _ (code.is_even_bot _) _ bot_ne_mk_coe
    · refine' (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _
      simp only [Ne.def, Iio_index.bot_ne_coe, not_false_iff, A_map_code_mk_ne]
      rw [hA₁ γ, h, ← hA₂ γ (Iio.coe_injective.ne hδγ), ← A_map_code_mk_ne]
      exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ)
  · simp only [repr_code_proper, Subtype.coe_mk, repr_code_base]
    obtain rfl | hβγ := eq_or_ne β γ
    · dsimp only [mem_Iio, Ne.def, Subtype.val_eq_coe, SetCoe.forall] at *
      rw [h, ← hA₂ β]
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ bot_ne_mk_coe
    · refine' (code.equiv.A_map_right _ even₁ γ <| Iio.coe_injective.ne hβγ).trans _
      dsimp only [mem_Iio, Ne.def, Subtype.val_eq_coe, SetCoe.forall] at *
      rw [A_map_code_mk_ne _ _ (Iio.coe_injective.ne hβγ)]
      rw [hA₁ γ (Iio.coe_injective.ne hβγ), h, ← hA₂ γ]
      exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe
  · simp only [repr_code_proper, Subtype.coe_mk]
    obtain rfl | hβγ := eq_or_ne β γ
    · obtain rfl | hδβ := eq_or_ne δ β
      · rw [h]
      · have := A_map_code_ne β (code.mk δ (ys δ)) (Iio.coe_injective.ne hδβ)
        dsimp only [mem_Iio, Ne.def, Subtype.val_eq_coe, SetCoe.forall, code.snd_mk] at *
        rw [h, ← hA₂ _ (Iio.coe_injective.ne hδβ), ← code.mk_def, ← this]
        exact code.equiv.A_map_left _ even₂ _ (Iio.coe_injective.ne hδβ)
    obtain rfl | hδγ := eq_or_ne δ γ
    · have := A_map_code_ne δ (code.mk β (xs β)) (Iio.coe_injective.ne hβγ)
      dsimp only [mem_Iio, Ne.def, Subtype.val_eq_coe, SetCoe.forall, code.snd_mk] at *
      simp_rw [← h, ← hA₁ _ (Iio.coe_injective.ne hβγ), ← code.mk_def, ← this]
      exact code.equiv.A_map_right _ even₁ _ (Iio.coe_injective.ne hβγ)
    refine' (code.equiv.A_map_right _ even₁ γ <| Iio.coe_injective.ne hβγ).trans _
    have := A_map_code_ne γ (code.mk (↑δ) (ys δ)) (Iio.coe_injective.ne hδγ)
    dsimp only [mem_Iio, Ne.def, Subtype.val_eq_coe, SetCoe.forall, code.snd_mk] at *
    rw [A_map_code_ne]
    rw [code.snd_mk, hA₁ γ (Iio.coe_injective.ne hβγ), h, ← hA₂ γ (Iio.coe_injective.ne hδγ)]
    rw [← this]
    exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ)

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
theorem ext' (x y : Semitangle α) (h : ∀ t : Tangle γ, t ∈ₛₜ x ↔ t ∈ₛₜ y) : x = y :=
  ext x y <| Set.ext h

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all nonempty semitangles have a `-1`-extension.
Therefore, the extensionality principle in this case applies to the `-1`-extensions. -/
theorem ext_zero (x y : Semitangle α) (α_zero : IsMin α) (h : x.pref.atoms = y.pref.atoms) :
    x = y := by
  obtain ⟨xs, ⟨atoms₁, hA₁⟩ | ⟨γ, _, _⟩⟩ := x; swap
  · cases α_zero.not_lt γ.2
  obtain ⟨ys, ⟨atoms₂, hA₂⟩ | ⟨γ, _, _⟩⟩ := y; swap
  · cases α_zero.not_lt γ.2
  have : atoms₁ = atoms₂ := h
  subst this
  suffices xs = ys by subst this
  ext β -
  cases α_zero.not_lt β.2

/-- Construct a semitangle from an even nonempty code. -/
def intro (s : Set (Tangle β)) (heven : (Code.mk β s : Code α).IsEven) : Semitangle α :=
  ⟨extension s,
    match β, s, heven with
    | ⟨⊥, _⟩, s, _ => Preference.base s fun β => rfl
    | ⟨(γ : Λ), hγ⟩, s, heven =>
      Preference.proper ⟨γ, coe_lt_coe.1 hγ⟩
        (by convert heven; exact extension_self (show Set (tangle <| Iio_coe ⟨γ, _⟩) from s))
        fun δ hδ => by
        rw [extension_ne s δ hδ]; congr
        exact extension_self (show Set (tangle <| Iio_coe ⟨γ, _⟩) from s)⟩

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
    f • extension s γ = extension (f • s) γ :=
  by
  by_cases β = γ
  · subst h
    simp only [extension_eq, cast_eq]
  · simp only [extension_ne _ _ h, smul_A_map]

@[simp]
theorem smul_extension (f : AllowablePerm α) (s : Set (Tangle β)) :
    f • extension s = extension (f • s) := by
  ext γ : 1
  rw [← smul_extension_apply]
  rfl

theorem smul_aux₁ {s : Set (Tangle (⊥ : IioBot α))}
    (h : ∀ γ : Iio α, aMap bot_ne_coe s = (e γ : Set (Tangle (iioCoe γ)))) (γ : Iio α) :
    aMap bot_ne_coe (f • s) = (f • e) γ := by
  simpa only [smul_A_map] using congr_arg (fun c => f • c) (h γ)

theorem smul_aux₂
    (h : ∀ (δ : Iio α) (hγδ : iioCoe γ ≠ δ), aMap hγδ (e γ) = (e δ : Set (Tangle (iioCoe δ))))
    (δ : Iio α) (hγδ : iioCoe γ ≠ δ) : aMap hγδ ((f • e) γ) = (f • e) δ := by
  simpa only [smul_A_map] using congr_arg (fun c => f • c) (h δ hγδ)

/-- Allowable permutations act on nonempty semitangles. -/
noncomputable instance : SMul (AllowablePerm α) (Semitangle α)
    where smul f t :=
    ⟨f • t.members, by
      obtain ⟨members, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩ := t
      · exact preference.base (f • s) (smul_aux₁ h)
      · exact preference.proper _ ht.smul (smul_aux₂ h)⟩

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
      ⟨f • e, Preference.proper _ ht.smul (smul_aux₂ h)⟩ :=
  rfl

instance mulActionSemitangle : MulAction (AllowablePerm α) (Semitangle α)
    where
  one_smul := by
    rintro ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · rw [smul_base]
      simp only [one_smul, eq_self_iff_true, true_and_iff]
      refine' preference.base_heq_base _ _
      rw [one_smul]
      rfl
    · rw [smul_proper]
      simp only [one_smul, eq_self_iff_true, true_and_iff]
      refine' semitangle.preference.proper_heq_proper _ rfl
      rw [one_smul]
  hMul_smul := by
    rintro f g ⟨exts, ⟨s, h⟩ | ⟨γ, ht, h⟩⟩
    · simp only [smul_base, mul_smul, eq_self_iff_true, true_and_iff]
      refine' preference.base_heq_base _ _
      rw [mul_smul]
      rfl
    · simp only [smul_proper, mul_smul, eq_self_iff_true, true_and_iff]
      refine' semitangle.preference.proper_heq_proper _ rfl
      rw [mul_smul]

end AllowablePerm

variable (α)

/-- A tangle at the new level `α` is a semitangle supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
@[nolint has_nonempty_instance]
def NewTangle :=
  { s : Semitangle α // Supported α (AllowablePerm α) s }

variable {α} {c d : Code α} {S : Set (SupportCondition α)}

open MulAction

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected theorem Code.Equiv.supports (hcd : c ≡ d) (hS : Supports (AllowablePerm α) S c) :
    Supports (AllowablePerm α) S d := fun f h =>
  (hcd.symm.smul.trans <| (Code.Equiv.ofEq <| hS f h).trans hcd).unique rfl

theorem Code.Equiv.supports_iff (hcd : c ≡ d) :
    Supports (AllowablePerm α) S c ↔ Supports (AllowablePerm α) S d :=
  ⟨hcd.Supports, hcd.symm.Supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
theorem Code.Equiv.small_supported_iff (hcd : c ≡ d) :
    Supported α (AllowablePerm α) c ↔ Supported α (AllowablePerm α) d :=
  ⟨fun ⟨⟨s, hs, h⟩⟩ => ⟨⟨s, hs, hcd.Supports h⟩⟩, fun ⟨⟨s, hs, h⟩⟩ =>
    ⟨⟨s, hs, hcd.symm.Supports h⟩⟩⟩

@[simp]
theorem smul_intro (f : AllowablePerm α) (s : Set (Tangle β)) (hs) :
    f • intro s hs = intro (f • s) hs.smul := by
  cases β
  induction β_val using WithBot.recBotCoe
  · simp only [intro, allowable_perm.smul_base, allowable_perm.smul_extension, eq_self_iff_true,
      true_and_iff]
    refine' preference.base_heq_base _ rfl
    rw [allowable_perm.smul_extension]
  · simp only [intro, allowable_perm.smul_proper, allowable_perm.smul_extension, eq_self_iff_true,
      true_and_iff]
    refine' preference.proper_heq_proper _ rfl
    rw [allowable_perm.smul_extension]

-- TODO: Move next two lemmas elsewhere.
theorem allowableToStructPerm_bot (π : Allowable (⊥ : IioBot α)) :
    CoreTangleData.allowableToStructPerm π = StructPerm.toBotIso.toMonoidHom π :=
  rfl

theorem ConNF.SemiallowablePerm.toAllowable_bot (π : SemiallowablePerm α) :
    SemiallowablePerm.toAllowable ⊥ π =
      StructPerm.toNearLitterPerm (SemiallowablePerm.toStructPerm π) :=
  by
  unfold semiallowable_perm.to_allowable semiallowable_perm.to_StructPerm
    StructPerm.to_near_litter_perm StructPerm.lower allowable.to_StructPerm
  rw [dif_neg WithBot.bot_ne_coe]
  simp only [MonoidHom.coe_mk, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, comp_app,
    StructPerm.of_coe_to_coe, allowable_to_StructPerm_bot, MulEquiv.symm_apply_apply]
  rfl

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def newTypedNearLitter (N : NearLitter) : NewTangle α :=
  ⟨intro (show Set (Tangle (⊥ : IioBot α)) from N.2.1) <| Code.isEvenBot _,
    ⟨⟨{(Sum.inr N, default)}, small_singleton _, fun π h =>
        by
        simp only [Subtype.val_eq_coe, Option.smul_some, smul_intro, Option.some_inj]
        have :=
          show
            StructPerm.lower (bot_lt_coe α).le (semiallowable_perm.to_StructPerm ↑π) • Sum.inr N =
              Sum.inr N
            from congr_arg Prod.fst (h rfl)
        simp only [Sum.smul_inr] at this
        have : π • N = N := this
        conv_rhs => rw [← this]
        congr 1
        ext : 1
        simp only [coe_smul_nonempty, Subtype.coe_mk, allowable_perm.snd_smul_near_litter]
        unfold SMul.smul SMul.comp.smul
        simp only [semiallowable_perm.to_allowable_bot (allowable_perm.coe_hom π)]⟩⟩⟩

/-- For any supported tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def supportedSingleton (x : Tangle β) (supp : Supported α (AllowablePerm α) x) : NewTangle α :=
  ⟨intro {x} (Code.isEvenSingleton _),
    by
    obtain ⟨s, hs₁, hs₂⟩ := supp
    refine' ⟨⟨s, hs₁, fun π h => _⟩⟩
    conv_rhs => rw [← hs₂ π h]
    simp only [smul_set_singleton, smul_nonempty_mk, Option.smul_some, smul_intro]⟩

/-- For any small set `B` of supported `β`-tangles, the code `(α, β, B)` is a tangle at level `α` if
it is even. -/
def supportedSet (s : Set (Tangle β)) (hs : Small s) (hc : (mk β s).IsEven)
    (symm : ∀ b ∈ s, Supported α (AllowablePerm α) b) : NewTangle α :=
  ⟨intro s hc,
    by
    have symm : ∀ b ∈ s, support α (allowable_perm α) b := by intro b hb; exact (symm b hb).some
    refine' ⟨⟨⋃ b ∈ s, symm b ‹_›, hs.bUnion fun i hi => (symm _ _).Small, fun π h => _⟩⟩
    suffices π • s = s by simp only [Option.smul_some, smul_intro, Option.some_inj, this]
    have : ∀ x ∈ s, π • x = x := by
      intro x hx
      refine' (symm x hx).Supports π _
      intro a ha
      refine' h _
      simp only [mem_Union, SetLike.mem_coe]
      refine' ⟨x, hx, ha⟩
    ext : 2
    refine' ⟨fun hx => _, fun hx => _⟩
    · have := this (π⁻¹ • x) _
      · rw [smul_inv_smul] at this
        rw [this]
        rwa [← mem_smul_set_iff_inv_smul_mem]
      · rwa [← mem_smul_set_iff_inv_smul_mem]
    · rw [← this x hx]
      exact smul_mem_smul_set hx⟩

variable {α}

namespace NewTangle

instance : Coe (NewTangle α) (Semitangle α) :=
  coeSubtype

theorem coe_injective : Injective (coe : NewTangle α → Semitangle α) :=
  Subtype.coe_injective

end NewTangle

namespace AllowablePerm

--Yaël: I suspect we can generalize `supports.smul` so that it applies here
/-- Allowable permutations act on `α`-tangles. -/
instance hasSmulNewTangle : SMul (AllowablePerm α) (NewTangle α) :=
  ⟨fun π t =>
    ⟨π • t,
      t.2.map fun s =>
        { carrier := π • s
          Small := s.2.image
          Supports := by
            intro σ h
            have := s.supports (π⁻¹ * σ * π) _
            · conv_rhs =>
                rw [← Subtype.val_eq_coe, ← this, ← mul_smul, ← mul_assoc, ← mul_assoc,
                  mul_inv_self, one_mul, mul_smul]
              rfl
            · intro a ha
              rw [mul_smul, mul_smul, inv_smul_eq_iff]
              exact h (smul_mem_smul_set ha) }⟩⟩

@[simp, norm_cast]
theorem coe_smul_newTangle (f : AllowablePerm α) (t : NewTangle α) :
    (↑(f • t) : Semitangle α) = f • t :=
  rfl

instance mulActionNewTangle : MulAction (AllowablePerm α) (NewTangle α) :=
  NewTangle.coe_injective.MulAction _ coe_smul_newTangle

end AllowablePerm

end ConNF
