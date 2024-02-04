import ConNF.NewTangle.Cloud

/-!
# Equivalence of codes

Several codes will be identified to make one TTT object. A TTT object has extensions for all type
indices (except possibly `⊥`), so our equivalence classes must too.

One way to do this is to make an equivalence class out of a code and its image under each
`cloudCode` map. Thus we want to partition the big tree given by `↝₀` into trees of height `1` that
each contains all descendents of its root (this is a slight lie for empty codes as the one
equivalence class they form won't be a tree but rather a complete graph).

This is where code parity kicks in. We recursively pick out the small trees by noticing that codes
whose preimages under `cloud` maps are all in a small tree already (in particular, those that have
no preimage under an `cloud` map) must be the root of their own small tree, and that codes that are
an image of some root of a small tree must belong to that same tree. This motivates the following
definitions:

* A code is even if all its preimages under `cloudCode` maps are odd.
* A code is odd if one of its preimages under `cloudCode` maps are even.

If we replace "even" and "odd" by "winning" and "losing", we precisely get the rules for determining
whether a game position is winning or losing.

Note that for nonempty codes there is at most one preimage under `cloud` maps.

## Main declarations

* `ConNF.IsEven`, `ConNF.IsOdd`: Code parity.
* `ConNF.Code.Equiv`: Equivalence of codes.
* `ConNF.exists_even_equiv`: There is a unique even code in each equivalence class.
-/

open Set WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] {β : TypeIndex} [LtLevel β] {γ : Λ} [LtLevel γ]
  [TangleDataLt] [TypedObjectsLt] [PositionedTanglesLt]

namespace Code

variable {c d : Code}

/-! ### Parity of a code

Parity of codes. If we consider codes as states of a game and `↝₀` as the "leads to"
relation, then even codes are precisely losing codes and odd codes are precisely winning codes.
Parity of a nonempty code corresponds to the parity of its number of iterated preimages under
`cloudCode`. The only even empty code is `⊥`, all others are odd.
-/

mutual
/-- A code is even iff it only leads to odd codes. -/
  @[mk_iff]
  inductive IsEven : Code → Prop
    | intro : ∀ c, (∀ d, d ↝₀ c → IsOdd d) → IsEven c

  /-- A code is odd iff it leads to some even code. -/
  @[mk_iff]
  inductive IsOdd : Code → Prop
    | intro : ∀ c d, d ↝₀ c → IsEven d → IsOdd c
end

theorem isEven_of_forall_not (h : ∀ d, ¬d ↝₀ c) : IsEven c :=
  (isEven_iff c).2 fun _ hd => (h _ hd).elim

@[simp]
theorem isEven_of_eq_bot (c : Code) (hc : c.1 = ⊥) : c.IsEven :=
  isEven_of_forall_not <| by rintro d ⟨β, -⟩; exact coe_ne_bot hc

@[simp]
theorem isEven_bot (s : Set Atom) : IsEven (mk ⊥ s : Code) :=
  isEven_of_eq_bot _ rfl

theorem not_isOdd_bot (s : Set Atom) : ¬IsOdd (mk ⊥ s : Code) := by
  simp_rw [isOdd_iff, cloudRel_iff]
  rintro ⟨d, ⟨γ, _, h⟩, _⟩
  exact bot_ne_coe (congr_arg Code.β h.2)

/-- An empty code is even iff its extension is `⊥`. -/
@[simp]
theorem IsEmpty.isEven_iff (hc : c.IsEmpty) : IsEven c ↔ (c.1 : TypeIndex) = ⊥ := by
  refine ⟨?_, isEven_of_eq_bot _⟩
  intro h
  obtain ⟨_ | (β : Λ), s⟩ := c
  · rfl
  · simp [Code.IsEmpty] at hc
    cases hc
    have := not_isOdd_bot ∅ ((isEven_iff _).1 h ⟨⊥, ∅⟩ ?_)
    · cases this
    convert CloudRel.intro β _
    · aesop
    · simp only [ne_eq, Subtype.mk.injEq, WithBot.bot_ne_coe, not_false_eq_true]

@[simp]
theorem IsEmpty.isOdd_iff (hc : c.IsEmpty) : IsOdd c ↔ (c.1 : TypeIndex) ≠ ⊥ := by
  obtain ⟨β, s⟩ := c
  refine' ⟨_, fun h => (isOdd_iff _).2 ⟨mk ⊥ ∅, _, isEven_bot _⟩⟩
  · rintro h (rfl : β = _)
    exact not_isOdd_bot _ h
  · lift β to Λ using h
    refine (cloudRel_iff _ _).2 ⟨β, inferInstance, ?_⟩
    simp only [ne_eq, bot_ne_coe, not_false_eq_true, cloudCode_mk_ne, cloud_empty, mk.injEq,
      heq_eq_eq, true_and]
    exact hc

@[simp]
theorem isEven_empty_iff : IsEven (mk β ∅) ↔ (β : TypeIndex) = ⊥ :=
  IsEmpty.isEven_iff rfl

@[simp]
theorem isOdd_empty_iff : IsOdd (mk β ∅) ↔ (β : TypeIndex) ≠ ⊥ :=
  IsEmpty.isOdd_iff rfl

private theorem not_isOdd_nonempty : ∀ c : NonemptyCode, ¬c.1.IsOdd ↔ c.1.IsEven
  | c => by
    rw [isOdd_iff, isEven_iff]
    push_neg
    apply forall_congr' _
    intro d
    apply imp_congr_right _
    intro h
    rw [Iff.comm, ← not_iff_not, Classical.not_not]
    obtain hd | hd := d.members.eq_empty_or_nonempty
    · rw [IsEmpty.isOdd_iff hd, IsEmpty.isEven_iff hd, Classical.not_not]
    · let _ : ⟨d, hd⟩ ↝ c := cloudRel_coe_coe.1 h
      exact not_isOdd_nonempty ⟨d, hd⟩
termination_by c => c

/-- A code is not odd iff it is even. -/
@[simp]
theorem not_isOdd : ¬c.IsOdd ↔ c.IsEven := by
  obtain hc | hc := c.members.eq_empty_or_nonempty
  · rw [IsEmpty.isOdd_iff hc, IsEmpty.isEven_iff hc, Classical.not_not]
  · exact not_isOdd_nonempty ⟨c, hc⟩

/-- A code is not even iff it is odd. -/
@[simp]
theorem not_isEven : ¬c.IsEven ↔ c.IsOdd :=
  not_isOdd.symm.not_left

alias ⟨_, IsEven.not_isOdd⟩ := not_isOdd

alias ⟨_, IsOdd.not_isEven⟩ := not_isEven

/-- Any code is even or odd. -/
theorem isEven_or_isOdd (c : Code) : c.IsEven ∨ c.IsOdd := by
  rw [← not_isEven]
  exact em _

protected theorem _root_.ConNF.CloudRel.isOdd (hc : c.IsEven) (h : c ↝₀ d) : d.IsOdd :=
  (isOdd_iff d).2 ⟨_, h, hc⟩

protected theorem IsEven.cloudCode (hc : c.IsEven) (hcγ : c.1 ≠ γ) : (cloudCode γ c).IsOdd :=
  (CloudRel.intro _ hcγ).isOdd hc

protected theorem IsOdd.cloudCode (hc : c.IsOdd) (hc' : c.members.Nonempty) (hcγ : c.1 ≠ γ) :
    (cloudCode γ c).IsEven :=
  (isEven_iff _).2 fun d hd => by rwa [(cloudRel_cloudCode _ hc' hcγ).1 hd]

protected theorem IsEven.cloudCode_ne (hc : c.IsEven) (hd : d.IsEven) (hcγ : c.1 ≠ γ) :
    cloudCode γ c ≠ d := by rintro rfl; exact hd.not_isOdd (hc.cloudCode hcγ)

theorem cloudCode_ne_bot {s} : cloudCode γ c ≠ mk ⊥ s :=
  ne_of_apply_ne Code.β coe_ne_bot

/-- The cloud map cannot produce a singleton code. -/
theorem cloudCode_ne_singleton {t} (hcβ : c.1 ≠ β) : cloudCode γ c ≠ mk β {t} := by
  intro h
  rw [cloudCode, Code.ext_iff] at h
  simp only [ne_eq] at h
  obtain ⟨rfl, h⟩ := h
  refine' (Cardinal.one_lt_aleph0.trans_le
    (Params.κ_isRegular.aleph0_le.trans Params.κ_lt_μ.le)).not_le _
  rw [← Cardinal.mk_singleton t, ← h.eq]
  refine' μ_le_mk_cloudCode c hcβ ((cloudCode_nonempty (β := γ)).1 _)
  rw [cloudCode, eq_of_heq h]
  simp only [singleton_nonempty]

/-- Singleton codes are even. -/
@[simp]
theorem isEven_singleton (t) : (mk β {t}).IsEven := by
  refine' isEven_of_forall_not fun c hc => _
  obtain ⟨γ, _, h⟩ := (cloudRel_iff _ _).1 hc
  have := congr_arg Code.β h.2
  cases this
  exact cloudCode_ne_singleton h.1 h.2.symm

/-! ### Equivalence of codes -/

/-- Equivalence of codes. -/
@[mk_iff]
inductive Equiv : Code → Code → Prop
  | refl (c) : Equiv c c
  | cloud_left (c : Code) (hc : c.IsEven) (β : Λ) [LtLevel β] (hcβ : c.1 ≠ β) :
      Equiv (cloudCode β c) c
  | cloud_right (c : Code) (hc : c.IsEven) (β : Λ) [LtLevel β] (hcβ : c.1 ≠ β) :
      Equiv c (cloudCode β c)
  | cloud_cloud (c : Code) (hc : c.IsEven) (β : Λ) [LtLevel β] (hcβ : c.1 ≠ β)
      (γ : Λ) [LtLevel γ] (hcγ : c.1 ≠ γ) :
      Equiv (cloudCode β c) (cloudCode γ c)

/-! We declare new notation for code equivalence. -/

infixl:50 " ≡ " => Equiv

namespace Equiv

attribute [refl] refl

protected theorem rfl : c ≡ c :=
  refl _

theorem of_eq : c = d → c ≡ d := by rintro rfl; rfl

theorem symm : Symmetric ((· ≡ ·) : Code → Code → Prop)
  | _, _, refl _ => refl _
  | _, _, cloud_left c β hc hcβ => cloud_right c β hc hcβ
  | _, _, cloud_right c β hc hcβ => cloud_left c β hc hcβ
  | _, _, cloud_cloud c hc β hcβ γ hcγ => cloud_cloud c hc γ hcγ β hcβ

theorem comm : c ≡ d ↔ d ≡ c :=
  symm.iff _ _

/-- All empty codes are equivalent. -/
theorem empty_empty : ∀ (β γ : TypeIndex), [LtLevel β] → [LtLevel γ] → (⟨β, ∅⟩ : Code) ≡ ⟨γ, ∅⟩
  | ⊥, ⊥, _, _ => Equiv.rfl
  | ⊥, (γ : Λ), _, hγ => by
    convert cloud_right _ (isEven_bot _) γ bot_ne_coe
    simp only [ne_eq, bot_ne_coe, not_false_eq_true, snd_cloudCode, cloud_empty]
  | (β : Λ), ⊥, hβ, _ => by
    convert cloud_left _ (isEven_bot _) β bot_ne_coe
    simp only [ne_eq, bot_ne_coe, not_false_eq_true, snd_cloudCode, cloud_empty]
  | (β : Λ), (γ : Λ), hβ, hγ => by
    convert cloud_cloud _ (isEven_bot ∅) β bot_ne_coe γ bot_ne_coe <;>
    · simp only [ne_eq, bot_ne_coe, not_false_eq_true, snd_cloudCode]
      rw [cloud_empty]

protected theorem _root_.ConNF.Code.IsEmpty.equiv (hc : c.IsEmpty) (hd : d.IsEmpty) : c ≡ d := by
  obtain ⟨γ, c⟩ := c
  obtain ⟨δ, d⟩ := d
  change c = ∅ at hc
  change d = ∅ at hd
  subst hc
  subst hd
  exact empty_empty _ _

/-- Code equivalence is transitive. -/
theorem trans {c d e : Code} : c ≡ d → d ≡ e → c ≡ e := by
  rw [equiv_iff, equiv_iff]
  rintro (rfl | ⟨hc, β, _, hcβ, rfl⟩ | ⟨hc, β, _, hcβ, rfl⟩ | ⟨d, hd, γ, _, hdγ, ε, _, hdε, rfl, rfl⟩)
  · exact (equiv_iff _ _).2
  · rintro (rfl | ⟨hc', γ, _, hcγ, rfl⟩ | ⟨-, γ, _, hcγ, rfl⟩ | ⟨_, hc', γ, _, hcγ, ε, _, _, rfl, rfl⟩)
    · exact cloud_left _ hc β hcβ
    · cases (hc'.cloudCode hcγ).not_isEven hc
    · exact cloud_cloud _ hc _ hcβ _ hcγ
    · cases (hc'.cloudCode hcγ).not_isEven hc
  · rintro (rfl | ⟨_, γ, _, hcγ, hce⟩ | ⟨hc', γ, _, _, rfl⟩ | ⟨e, he, γ, _, hcγ, ε, _, heε, hce, rfl⟩)
    · exact cloud_right _ hc β hcβ
    · obtain h | h := c.members.eq_empty_or_nonempty
      · refine' IsEmpty.equiv h _
        rwa [← cloudCode_isEmpty (β := γ), ← hce, cloudCode_isEmpty, Code.IsEmpty]
      · exact of_eq (eq_of_cloudCode h hcβ hcγ hce)
    · cases (hc.cloudCode hcβ).not_isEven hc'
    · obtain h | h := c.members.eq_empty_or_nonempty
      · refine' IsEmpty.equiv h _
        rwa [cloudCode_isEmpty, ← cloudCode_isEmpty (β := γ), ← hce, cloudCode_isEmpty, Code.IsEmpty]
      · rw [eq_of_cloudCode h hcβ hcγ hce]
        exact cloud_right _ he _ heε
  · rintro (rfl | ⟨_, γ, _, heγ, hde⟩ | ⟨hd', γ, _, -, rfl⟩ | ⟨e, he, ι, _, heι, κ, _, heκ, hde, rfl⟩)
    · exact cloud_cloud _ hd _ hdγ _ hdε
    · obtain h | h := e.members.eq_empty_or_nonempty
      · refine' IsEmpty.equiv _ h
        rwa [cloudCode_isEmpty, ← cloudCode_isEmpty (β := ε), hde, cloudCode_isEmpty, Code.IsEmpty]
      · rw [eq_of_cloudCode h heγ hdε hde.symm]
        exact cloud_left _ hd _ hdγ
    · cases (hd.cloudCode hdε).not_isEven hd'
    · obtain h | h := d.members.eq_empty_or_nonempty
      · refine' (IsEmpty.cloudCode h).equiv _
        rwa [cloudCode_isEmpty, ← cloudCode_isEmpty (β := ι), ← hde, cloudCode_isEmpty, Code.IsEmpty]
      · have := eq_of_cloudCode h hdε heι hde
        subst this
        exact cloud_cloud _ hd _ hdγ _ heκ

/-- Code equivalence is an equivalence relation. -/
theorem equiv_equivalence : Equivalence ((· ≡ ·) : Code → Code → Prop) :=
  ⟨refl, fun {_ _} h => symm h, fun {_ _ _} h₁ h₂ => trans h₁ h₂⟩

/-- If two codes are equal, they are either both empty or both nonempty. -/
theorem nonempty_iff : ∀ {c d : Code}, c ≡ d → (c.members.Nonempty ↔ d.members.Nonempty)
  | _, _, refl _ => Iff.rfl
  | _, _, cloud_left _ _ _ _ => cloudCode_nonempty
  | _, _, cloud_right _ _ _ _ => cloudCode_nonempty.symm
  | _, _, cloud_cloud _ _ _ _ _ _ => cloudCode_nonempty.trans cloudCode_nonempty.symm

/-- If two codes at the same level are equivalent, they are equal. -/
theorem ext : ∀ {c d : Code}, c ≡ d → c.1 = d.1 → c = d
  | _, _, refl _, _ => rfl
  | _, _, cloud_left c _ β h, H => (h H.symm).elim
  | _, _, cloud_right c _ β h, H => (h H).elim
  | _, _, cloud_cloud c _ β _ γ hcγ, H => by
    simp only [fst_cloudCode, Subtype.mk.injEq, coe_inj, Subtype.coe_inj] at H
    subst H
    rfl

@[simp]
theorem bot_left_iff {s} :
    mk ⊥ s ≡ c ↔ mk ⊥ s = c ∨ ∃ β : Λ, ∃ _ : LtLevel β, c = mk β (cloud bot_ne_coe s) := by
  simp [equiv_iff, cloudCode_ne_bot.symm]
  rw [eq_comm]

@[simp]
theorem bot_right_iff {s} :
    c ≡ mk ⊥ s ↔ c = mk ⊥ s ∨ ∃ β : Λ, ∃ _ : LtLevel β, c = mk β (cloud bot_ne_coe s) := by
  simp [equiv_iff, cloudCode_ne_bot.symm]
  rw [eq_comm]

@[simp]
theorem bot_bot_iff {s t} : (mk ⊥ s : Code) ≡ mk ⊥ t ↔ s = t := by
  constructor
  · rw [bot_left_iff]
    rintro (h | ⟨β, _, h⟩)
    · simp only [mk.injEq, heq_eq_eq, true_and] at h
      exact h
    · simp only [mk.injEq, bot_ne_coe, false_and] at h
  · rintro rfl
    rfl

theorem singleton (hβγ : β ≠ γ) (g : Tangle β) :
    mk β {g} ≡ mk γ (typedNearLitter '' localCardinal (fuzz hβγ g)) := by
  convert Equiv.cloud_right (mk β {g}) (isEven_singleton _) _ hβγ
  aesop

theorem singleton_iff {g} :
    c ≡ mk β {g} ↔
    c = mk β {g} ∨ ∃ γ : Λ, ∃ _ : LtLevel γ,
      (c.1 : TypeIndex) = (γ : Λ) ∧ β ≠ γ ∧ c = cloudCode γ (mk β {g}) := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · rw [equiv_iff] at h
    simp only [isEven_singleton, ne_eq, exists_and_left, true_and] at h
    obtain rfl | ⟨γ, hβγ, _, _, rfl⟩ | ⟨_, γ, γne, _, h⟩ | ⟨d, -, γ, _, _, δ, δne, _, _, h⟩ :=
      h
    · exact Or.inl rfl
    · simp only [Subtype.coe_mk, SetCoe.exists, exists_and_left]
      exact Or.inr ⟨_, rfl, hβγ, inferInstance, rfl⟩
    · cases congr_arg Code.β h
      cases cloudCode_ne_singleton γne h.symm
    · cases congr_arg Code.β h
      cases cloudCode_ne_singleton δne h.symm
  · rintro (rfl | ⟨γ, _, hc, hβγ, rfl⟩)
    · rfl
    · convert (singleton hβγ g).symm
      simp only [cloudCode, ne_eq, extension_ne _ _ hβγ, cloud_singleton]

end Equiv

theorem extension_eq_of_singleton_equiv_singleton {γ : TypeIndex} [LtLevel γ]
    {a : Tangle β} {b : Tangle γ}
    (h : (⟨β, {a}⟩ : Code) ≡ ⟨γ, {b}⟩) : β = γ := by
  obtain h | ⟨ε, _, hc, hβε, hA⟩ := Equiv.singleton_iff.1 h
  · exact ((Code.ext_iff _ _).1 h).1
  · exfalso
    refine cloudCode_ne_singleton ?_ hA.symm
    cases congr_arg Code.β hA
    exact hβε

theorem IsEven.unique : ∀ {c d : Code}, c.IsEven → d.IsEven → c ≡ d → c = d
  | c, _, _, _, Equiv.refl _ => rfl
  | _, _, _, _, Equiv.cloud_left d hd β hdβ => by cases (hd.cloudCode hdβ).not_isEven ‹_›
  | _, _, _, _, Equiv.cloud_right d hd β hcβ => by cases (hd.cloudCode hcβ).not_isEven ‹_›
  | _, _, _, _, Equiv.cloud_cloud e he β hcβ γ _ => by cases (he.cloudCode hcβ).not_isEven ‹_›

/-- There is a unique even code in each equivalence class. -/
theorem exists_even_equiv : ∀ c : Code, ∃ d : Code, d ≡ c ∧ d.IsEven := by
  rintro ⟨β, s⟩
  obtain rfl | _ := s.eq_empty_or_nonempty
  · exact ⟨_, Equiv.empty_empty _ _, isEven_bot _⟩
  obtain heven | hodd := isEven_or_isOdd ⟨β, s⟩
  · exact ⟨_, Equiv.rfl, heven⟩
  simp_rw [isOdd_iff, cloudRel_iff] at hodd
  obtain ⟨d, ⟨γ, _, hdγ, hc⟩, hd⟩ := id hodd
  exact ⟨d, (Equiv.cloud_right _ hd _ hdγ).trans (Equiv.of_eq hc.symm), hd⟩

protected theorem IsEven.exists_equiv_extension_eq (heven : c.IsEven) :
    ∃ d : Code, d ≡ c ∧ d.1 = γ := by
  by_cases h : c.1 = γ
  · exact ⟨c, Equiv.rfl, h⟩
  · exact ⟨cloudCode γ c, Equiv.cloud_left _ heven _ h, rfl⟩

theorem exists_equiv_extension_eq : ∀ c : Code, ∃ d : Code, d ≡ c ∧ d.1 = γ := by
  intro c
  obtain ⟨d, hd₁, hd₂⟩ := exists_even_equiv c
  obtain ⟨e, he₁, he₂⟩ : ∃ e : Code, e ≡ d ∧ e.1 = γ := hd₂.exists_equiv_extension_eq
  exact ⟨e, he₁.trans hd₁, he₂⟩

theorem Equiv.unique : ∀ {c d : Code}, c ≡ d → c.1 = d.1 → c = d
  | c, _, Equiv.refl _, _ => rfl
  | _, _, Equiv.cloud_left d _ β hdβ, h => by cases hdβ h.symm
  | _, _, Equiv.cloud_right d _ β hcβ, h => by cases hcβ h
  | _, _, Equiv.cloud_cloud e _ β _ γ _, h => by cases h; rfl

theorem equiv_bot_subsingleton (d e : Code)
    (hdc : d ≡ c) (hec : e ≡ c) (hd : d.1 = ⊥) (he : e.1 = ⊥) : d = e :=
  (hdc.trans hec.symm).unique (hd.trans he.symm)

end Code

end ConNF
