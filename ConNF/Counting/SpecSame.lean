import ConNF.FOA
import ConNF.Counting.Spec

/-!
# Supports with the same specification
-/

open Quiver Set Sum WithBot

open scoped symmDiff

universe u

namespace PFun

variable {α β : Type _}

noncomputable def ofGraph (g : α → β → Prop)
    (_hg : ∀ a b b', g a b → g a b' → b = b') : α →. β :=
  fun a => ⟨∃ b, g a b, fun h => h.choose⟩

variable {g : α → β → Prop} {hg : ∀ a b b', g a b → g a b' → b = b'}

theorem get_eq (a : α) (b : β) (h : g a b) :
    (ofGraph g hg a).get ⟨b, h⟩ = b := by
  have : ∃ b, g a b := ⟨b, h⟩
  refine hg a _ _ this.choose_spec h

@[simp]
theorem ofGraph_dom : (ofGraph g hg).Dom = {a | ∃ b, g a b} := rfl

end PFun

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]
  {S T : Support β} {hS : S.Strong} {hT : T.Strong}
  {σ : Spec β} (hσS : σ.Specifies S hS) (hσT : σ.Specifies T hT)

def ConvertAtom (S T : Support β) (A : ExtendedIndex β) (aS aT : Atom) : Prop :=
  ∃ (i : κ) (hiS : i < S.max) (hiT : i < T.max), S.f i hiS = ⟨A, inl aS⟩ ∧ T.f i hiT = ⟨A, inl aT⟩

def ConvertNearLitter (S T : Support β) (A : ExtendedIndex β) (NS NT : NearLitter) : Prop :=
  ∃ (i : κ) (hiS : i < S.max) (hiT : i < T.max), S.f i hiS = ⟨A, inr NS⟩ ∧ T.f i hiT = ⟨A, inr NT⟩

theorem convertAtom_subsingleton (A : ExtendedIndex β) (aS aT aT' : Atom)
    (h : ConvertAtom S T A aS aT) (h' : ConvertAtom S T A aS aT') : aT = aT' := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have h₁ := (hσS.atom_spec i hiS₁ A aS hiS₂).symm.trans (hσT.atom_spec i hiT₁ A aT hiT₂)
  have h₂ := (hσS.atom_spec i' hiS₁' A aS hiS₂').symm.trans (hσT.atom_spec i' hiT₁' A aT' hiT₂')
  simp only [SpecCondition.atom.injEq, true_and] at h₁ h₂
  have := h₁.1.symm.trans h₂.1
  rw [Set.ext_iff] at this
  obtain ⟨_, h⟩ := (this i).mp ⟨hiT₁, hiT₂⟩
  have := hiT₂.symm.trans h
  cases this
  rfl

theorem convert_flexible {A : ExtendedIndex β} {NS NT : NearLitter} (h : Flexible A NS.1)
    {i : κ} (hiS : i < S.max) (hiT : i < T.max)
    (hiNS : S.f i hiS = ⟨A, inr NS⟩) (hiNT : T.f i hiT = ⟨A, inr NT⟩) : Flexible A NT.1 := by
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' A NT.1
  · exact hN
  · have h₁ := hσS.flexible_spec i hiS A NS h hiNS
    have h₂ := hσT.inflexibleBot_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂
  · have h₁ := hσS.flexible_spec i hiS A NS h hiNS
    have h₂ := hσT.inflexibleCoe_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂

theorem convertNearLitter_subsingleton_flexible (A : ExtendedIndex β) (NS NT NT' : NearLitter)
    (h : ConvertNearLitter S T A NS NT) (h' : ConvertNearLitter S T A NS NT')
    (hN : Flexible A NS.1) : NT = NT' := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have h₁ := hσS.flexible_spec i hiS₁ A NS hN hiS₂
  have h₂ := hσS.flexible_spec i' hiS₁' A NS hN hiS₂'
  have h₃ := hσT.flexible_spec i hiT₁ A NT
    (convert_flexible hσS hσT hN hiS₁ hiT₁ hiS₂ hiT₂) hiT₂
  have h₄ := hσT.flexible_spec i' hiT₁' A NT'
    (convert_flexible hσS hσT  hN hiS₁' hiT₁' hiS₂' hiT₂') hiT₂'
  have h₅ := h₁.symm.trans h₃
  have h₆ := h₂.symm.trans h₄
  simp only [and_true, exists_const, SpecCondition.flexible.injEq, true_and] at h₅ h₆
  have := h₅.symm.trans h₆
  rw [Set.ext_iff] at this
  obtain ⟨_, h⟩ := (this i).mp ⟨hiT₁, hiT₂⟩
  have := hiT₂.symm.trans h
  cases this
  rfl

theorem convert_inflexibleCoe {A : ExtendedIndex β} {NS NT : NearLitter} (P : InflexibleCoePath A)
    (t : Tangle P.δ) (hNS : NS.1 = fuzz P.hδε t)
    {i : κ} (hiS : i < S.max) (hiT : i < T.max)
    (hiNS : S.f i hiS = ⟨A, inr NS⟩) (hiNT : T.f i hiT = ⟨A, inr NT⟩) :
    ∃ t', NT.1 = fuzz P.hδε t' := by
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨P', t', hNT⟩⟩) := flexible_cases' A NT.1
  · have h₁ := hσS.inflexibleCoe_spec i hiS A NS ⟨P, t, hNS⟩ hiNS
    have h₂ := hσT.flexible_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂
  · have h₁ := hσS.inflexibleCoe_spec i hiS A NS ⟨P, t, hNS⟩ hiNS
    have h₂ := hσT.inflexibleBot_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂
  · have h₁ := hσS.inflexibleCoe_spec i hiS A NS ⟨P, t, hNS⟩ hiNS
    have h₂ := hσT.inflexibleCoe_spec i hiT A NT ⟨P', t', hNT⟩ hiNT
    have := h₁.symm.trans h₂
    simp only [SpecCondition.inflexibleCoe.injEq, heq_eq_eq, true_and] at this
    cases this.1
    exact ⟨t', hNT⟩

theorem convert_inflexibleBot {A : ExtendedIndex β} {NS NT : NearLitter} (P : InflexibleBotPath A)
    (a : Atom) (hNS : NS.1 = fuzz (bot_ne_coe (a := P.ε)) a)
    {i : κ} (hiS : i < S.max) (hiT : i < T.max)
    (hiNS : S.f i hiS = ⟨A, inr NS⟩) (hiNT : T.f i hiT = ⟨A, inr NT⟩) :
    ∃ (a' : Atom), NT.1 = fuzz (bot_ne_coe (a := P.ε)) a' := by
  obtain (hN | ⟨⟨P', a', hNT⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' A NT.1
  · have h₁ := hσS.inflexibleBot_spec i hiS A NS ⟨P, a, hNS⟩ hiNS
    have h₂ := hσT.flexible_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂
  · have h₁ := hσS.inflexibleBot_spec i hiS A NS ⟨P, a, hNS⟩ hiNS
    have h₂ := hσT.inflexibleBot_spec i hiT A NT ⟨P', a', hNT⟩ hiNT
    have := h₁.symm.trans h₂
    simp only [SpecCondition.inflexibleBot.injEq, heq_eq_eq, true_and] at this
    cases this.1
    exact ⟨a', hNT⟩
  · have h₁ := hσS.inflexibleBot_spec i hiS A NS ⟨P, a, hNS⟩ hiNS
    have h₂ := hσT.inflexibleCoe_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂

theorem comp_eq_same {i : κ} (hiS : i < S.max) {γ : Λ} (A : Path (β : TypeIndex) γ)
    (c : Address γ) (hc : S.f i hiS = ⟨A.comp c.1, c.2⟩) :
    ∃ d : Address γ, T.f i (hiS.trans_eq (hσS.max_eq_max.trans hσT.max_eq_max.symm)) =
      ⟨A.comp d.1, d.2⟩ := by
  obtain ⟨B, a | N⟩ := c
  · have := hσS.atom_spec i hiS (A.comp B) a hc
    obtain ⟨a', ha'⟩ := hσT.of_eq_atom this
    exact ⟨⟨B, inl a'⟩, ha'⟩
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' (A.comp B) N.1
  · have := hσS.flexible_spec i hiS (A.comp B) N hN hc
    obtain ⟨N', -, hN'₂⟩ := hσT.of_eq_flexible this
    exact ⟨⟨B, inr N'⟩, hN'₂⟩
  · have := hσS.inflexibleBot_spec i hiS (A.comp B) N hN hc
    obtain ⟨N', hN'₁, -, hN'₃⟩ := hσT.of_eq_inflexibleBot this
    exact ⟨⟨B, inr N'⟩, hN'₃⟩
  · have := hσS.inflexibleCoe_spec i hiS (A.comp B) N hN hc
    obtain ⟨N', hN'₁, -, hN'₃⟩ := hσT.of_eq_inflexibleCoe this
    exact ⟨⟨B, inr N'⟩, hN'₃⟩

theorem convertNearLitter_subsingleton_inflexibleCoe (A : ExtendedIndex β) (NS NT NT' : NearLitter)
    (h : ConvertNearLitter S T A NS NT) (h' : ConvertNearLitter S T A NS NT')
    (hNS : InflexibleCoe A NS.1) : NT = NT' := by
  obtain ⟨P, t, hNS⟩ := hNS
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have h₁ := hσS.inflexibleCoe_spec i hiS₁ A NS ⟨P, t, hNS⟩ hiS₂
  have h₂ := hσS.inflexibleCoe_spec i' hiS₁' A NS ⟨P, t, hNS⟩ hiS₂'
  obtain ⟨u, hNT⟩ := convert_inflexibleCoe hσS hσT P t hNS hiS₁ hiT₁ hiS₂ hiT₂
  obtain ⟨u', hNT'⟩ := convert_inflexibleCoe hσS hσT P t hNS hiS₁' hiT₁' hiS₂' hiT₂'
  have h₃ := hσT.inflexibleCoe_spec i hiT₁ A NT ⟨P, u, hNT⟩ hiT₂
  have h₄ := hσT.inflexibleCoe_spec i' hiT₁' A NT' ⟨P, u', hNT'⟩ hiT₂'
  have h₅ := h₁.symm.trans h₃
  have h₆ := h₂.symm.trans h₄
  clear h₁ h₂ h₃ h₄
  simp only [SpecCondition.inflexibleCoe.injEq, heq_eq_eq, CodingFunction.code_eq_code_iff,
    true_and] at h₅ h₆
  obtain ⟨⟨ρ, h₅, rfl⟩, h₅'⟩ := h₅
  obtain ⟨⟨ρ', h₆, rfl⟩, -⟩ := h₆
  have : ρ • t = ρ' • t
  · clear h₅'
    have := support_supports t (ρ'⁻¹ * ρ) ?_
    · conv_rhs => rw [← this]
      rw [mul_smul, smul_smul, mul_right_inv, one_smul]
    intro c hc
    rw [mul_smul, inv_smul_eq_iff]
    have : ∃ (j : κ) (hj : j < S.max), j < i ∧ j < i' ∧ S.f j hj = ⟨(P.B.cons P.hδ).comp c.1, c.2⟩
    · by_cases hii' : i < i'
      · have h₇ := Support.Precedes.fuzz A NS ⟨P, t, hNS⟩ _ hc
        rw [← P.hA, ← hiS₂] at h₇
        obtain ⟨j, hj, hji, hjc⟩ := hS.precedes hiS₁ _ h₇
        exact ⟨j, hj, hji, hji.trans hii', hjc⟩
      · have h₇ := Support.Precedes.fuzz A NS ⟨P, t, hNS⟩ _ hc
        rw [← P.hA, ← hiS₂'] at h₇
        obtain ⟨j, hj, hji, hjc⟩ := hS.precedes hiS₁' _ h₇
        exact ⟨j, hj, hji.trans_le (le_of_not_lt hii'), hji, hjc⟩
    obtain ⟨j, hj, hji, hji', hjc⟩ := this
    have h₇ := support_f_congr h₅.symm j ?_
    swap
    · rw [Enumeration.smul_max, Support.comp_max_eq_of_canComp]
      exact hji
      exact ⟨j, hji, c, hjc⟩
    have h₈ := support_f_congr h₆.symm j ?_
    swap
    · rw [Enumeration.smul_max, Support.comp_max_eq_of_canComp]
      exact hji'
      exact ⟨j, hji', c, hjc⟩
    simp only [Enumeration.smul_f, Support.comp_f_eq] at h₇ h₈
    obtain ⟨d, hd⟩ := comp_eq_same hσS hσT hj (P.B.cons P.hδ) c hjc
    rw [Support.comp_decomp_eq _ _ (by exact hjc),
      Support.comp_decomp_eq _ _ (by exact hd)] at h₇ h₈
    exact h₇.trans h₈.symm
  clear h₅ h₆
  have hNTT' : NT.fst = NT'.fst
  · rw [hNT, hNT', this]
  refine NearLitter.ext ?_
  rw [← symmDiff_eq_bot, bot_eq_empty, eq_empty_iff_forall_not_mem]
  intro a ha
  obtain ⟨j, hj, -, -, hja⟩ :=
    hT.interferes hiT₁ hiT₁' hiT₂ hiT₂' (Support.Interferes.symmDiff hNTT' ha)
  simp only [Function.funext_iff, Set.ext_iff] at h₅'
  obtain ⟨_, _, a', NS', _, ha', hS', -⟩ :=
    (h₅' i' j).mpr ⟨hiT₁', hj, a, NT', hNTT'.symm, ha, hiT₂', hja⟩
  cases hiS₂'.symm.trans hS'
  simp only [symmDiff_self, bot_eq_empty, mem_empty_iff_false] at ha'

theorem convertNearLitter_subsingleton_inflexibleBot (A : ExtendedIndex β) (NS NT NT' : NearLitter)
    (h : ConvertNearLitter S T A NS NT) (h' : ConvertNearLitter S T A NS NT')
    (hNS : InflexibleBot A NS.1) : NT = NT' := by
  obtain ⟨P, a, hNS⟩ := hNS
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have h₁ := hσS.inflexibleBot_spec i hiS₁ A NS ⟨P, a, hNS⟩ hiS₂
  have h₂ := hσS.inflexibleBot_spec i' hiS₁' A NS ⟨P, a, hNS⟩ hiS₂'
  obtain ⟨u, hNT⟩ := convert_inflexibleBot hσS hσT P a hNS hiS₁ hiT₁ hiS₂ hiT₂
  obtain ⟨u', hNT'⟩ := convert_inflexibleBot hσS hσT P a hNS hiS₁' hiT₁' hiS₂' hiT₂'
  have h₃ := hσT.inflexibleBot_spec i hiT₁ A NT ⟨P, u, hNT⟩ hiT₂
  have h₄ := hσT.inflexibleBot_spec i' hiT₁' A NT' ⟨P, u', hNT'⟩ hiT₂'
  have h₅ := h₁.symm.trans h₃
  have h₆ := h₂.symm.trans h₄
  simp only [SpecCondition.inflexibleBot.injEq, heq_eq_eq, true_and] at h₅ h₆
  obtain ⟨h₅, h₅'⟩ := h₅
  obtain ⟨h₆, -⟩ := h₆
  clear h₁ h₂ h₃ h₄
  have : u = u'
  · clear h₅'
    have : ∃ (j : κ) (hj : j < S.max), j < i ∧ j < i' ∧ S.f j hj = ⟨P.B.cons (bot_lt_coe _), inl a⟩
    · by_cases hii' : i < i'
      · have h₇ := Support.Precedes.fuzzBot A NS ⟨P, a, hNS⟩
        rw [← P.hA, ← hiS₂] at h₇
        obtain ⟨j, hj, hji, hjc⟩ := hS.precedes hiS₁ _ h₇
        exact ⟨j, hj, hji, hji.trans hii', hjc⟩
      · have h₇ := Support.Precedes.fuzzBot A NS ⟨P, a, hNS⟩
        rw [← P.hA, ← hiS₂'] at h₇
        obtain ⟨j, hj, hji, hjc⟩ := hS.precedes hiS₁' _ h₇
        exact ⟨j, hj, hji.trans_le (le_of_not_lt hii'), hji, hjc⟩
    obtain ⟨j, hj, hji, hji', ha⟩ := this
    rw [Set.ext_iff] at h₅ h₆
    obtain ⟨_, hj₁⟩ := (h₅ j).mp ⟨hj, ha⟩
    obtain ⟨_, hj₂⟩ := (h₆ j).mp ⟨hj, ha⟩
    cases hj₁.symm.trans hj₂
    rfl
  have hNTT' : NT.fst = NT'.fst
  · rw [hNT, hNT', this]
  refine NearLitter.ext ?_
  rw [← symmDiff_eq_bot, bot_eq_empty, eq_empty_iff_forall_not_mem]
  intro a ha
  obtain ⟨j, hj, -, -, hja⟩ :=
    hT.interferes hiT₁ hiT₁' hiT₂ hiT₂' (Support.Interferes.symmDiff hNTT' ha)
  simp only [Function.funext_iff, Set.ext_iff] at h₅'
  obtain ⟨_, _, a', NS', _, ha', hS', -⟩ :=
    (h₅' i' j).mpr ⟨hiT₁', hj, a, NT', hNTT'.symm, ha, hiT₂', hja⟩
  cases hiS₂'.symm.trans hS'
  simp only [symmDiff_self, bot_eq_empty, mem_empty_iff_false] at ha'

theorem convertNearLitter_subsingleton (A : ExtendedIndex β) (NS NT NT' : NearLitter)
    (h : ConvertNearLitter S T A NS NT) (h' : ConvertNearLitter S T A NS NT') : NT = NT' := by
  obtain (hNS | ⟨⟨hNS⟩⟩ | ⟨⟨hNS⟩⟩) := flexible_cases' A NS.1
  · exact convertNearLitter_subsingleton_flexible hσS hσT A NS NT NT' h h' hNS
  · exact convertNearLitter_subsingleton_inflexibleBot hσS hσT A NS NT NT' h h' hNS
  · exact convertNearLitter_subsingleton_inflexibleCoe hσS hσT A NS NT NT' h h' hNS

theorem convertAtom_dom_small (A : ExtendedIndex β) :
    Small {a | ∃ a', ConvertAtom S T A a a'} := by
  have : Small {i | i < S.max} := Cardinal.card_typein_lt (· < ·) S.max Params.κ_ord.symm
  refine (this.pFun_image
    (f := fun i => ⟨∃ a hi, S.f i hi = ⟨A, inl a⟩, fun h => h.choose⟩)).mono ?_
  rintro a ⟨b, i, hiS, hiT, hiS', _⟩
  have : ∃ a hi, S.f i hi = ⟨A, inl a⟩ := ⟨a, hiS, hiS'⟩
  refine ⟨i, hiS, this, ?_⟩
  have := this.choose_spec.choose_spec
  rw [hiS'] at this
  cases this
  rfl

theorem convertNearLitter_dom_small (A : ExtendedIndex β) :
    Small {N | ∃ N', ConvertNearLitter S T A N N'} := by
  have : Small {i | i < S.max} := Cardinal.card_typein_lt (· < ·) S.max Params.κ_ord.symm
  refine (this.pFun_image
    (f := fun i => ⟨∃N hi, S.f i hi = ⟨A, inr N⟩, fun h => h.choose⟩)).mono ?_
  rintro N ⟨N', i, hiS, hiT, hiS', _⟩
  have : ∃ N hi, S.f i hi = ⟨A, inr N⟩ := ⟨N, hiS, hiS'⟩
  refine ⟨i, hiS, this, ?_⟩
  have := this.choose_spec.choose_spec
  rw [hiS'] at this
  cases this
  rfl

noncomputable def convert : StructBehaviour β :=
  fun A => {
    atomMap :=
      PFun.ofGraph (ConvertAtom S T A) (convertAtom_subsingleton hσS hσT A)
    nearLitterMap :=
      PFun.ofGraph (ConvertNearLitter S T A) (convertNearLitter_subsingleton hσS hσT A)
    atomMap_dom_small := convertAtom_dom_small A
    nearLitterMap_dom_small := convertNearLitter_dom_small A
  }

end ConNF
