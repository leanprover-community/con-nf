import ConNF.Mathlib.PFun
import ConNF.FOA
import ConNF.Counting.Spec

/-!
# Supports with the same specification
-/

open Quiver Set Sum WithBot

open scoped symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions] {β : Λ} [LeLevel β]
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
  simp only [SpecCondition.flexible.injEq, true_and] at h₅ h₆
  obtain ⟨h₅, h₅'⟩ := h₅
  obtain ⟨h₆, -⟩ := h₆
  have := h₅.symm.trans h₆
  rw [Set.ext_iff] at this
  obtain ⟨_, N', h₁, h₂⟩ := (this i).mp ⟨hiT₁, NT, hiT₂, rfl⟩
  cases hiT₂.symm.trans h₁
  -- TODO: Abstract away the last bit of the proof since it's repeated for the other cases.
  refine NearLitter.ext ?_
  rw [← symmDiff_eq_bot, bot_eq_empty, eq_empty_iff_forall_not_mem]
  intro a ha
  obtain ⟨j, hj, -, -, hja⟩ :=
    hT.interferes hiT₁ hiT₁' hiT₂ hiT₂' (Support.Interferes.symmDiff h₂ ha)
  simp only [Function.funext_iff, Set.ext_iff] at h₅'
  obtain ⟨_, _, a', NS', _, ha', hS', -⟩ :=
    (h₅' i' j).mpr ⟨hiT₁', hj, a, NT', h₂.symm, ha, hiT₂', hja⟩
  cases hiS₂'.symm.trans hS'
  simp only [symmDiff_self, bot_eq_empty, mem_empty_iff_false] at ha'

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

theorem support_tangle_ext (hS : S.Strong) {A : ExtendedIndex β} (P : InflexibleCoePath A)
    (t₁ t₂ : Tangle P.δ)
    (h₁ : t₁.set = t₂.set)
    (h₂ : t₁.support.max = t₂.support.max)
    (h₃ :
      (fun j => {k | ∃ (hj : j < t₁.support.max) (hk : k < S.max),
        ⟨(P.B.cons P.hδ).comp (t₁.support.f j hj).1, (t₁.support.f j hj).2⟩ =
          S.f k hk}) =
      (fun j => {k | ∃ (hj : j < t₂.support.max) (hk : k < S.max),
        ⟨(P.B.cons P.hδ).comp (t₂.support.f j hj).1, (t₂.support.f j hj).2⟩ =
          S.f k hk}))
    {i : κ} (hi₁ : i < S.max) {N : NearLitter}
    (hi₂ : S.f i hi₁ = ⟨A, inr N⟩) (hi₃ : N.1 = fuzz P.hδε t₁) :
    t₁ = t₂ := by
  refine Tangle.ext _ _ h₁ ?_
  refine Enumeration.ext' h₂ ?_
  intro k hku hku'
  have := hS.precedes hi₁ ⟨(P.B.cons P.hδ).comp (t₁.support.f k hku).1, (t₁.support.f k hku).2⟩ ?_
  swap
  · have := Support.Precedes.fuzz _ N ⟨P, t₁, hi₃⟩ (t₁.support.f k hku) ⟨k, hku, rfl⟩
    rw [← P.hA, ← hi₂] at this
    exact this
  obtain ⟨j, hjT, _, hjeq⟩ := this
  obtain ⟨_, _, hjeq'⟩ := (Set.ext_iff.mp (congr_fun h₃ k) j).mp ⟨hku, hjT, hjeq.symm⟩
  have := hjeq'.trans hjeq
  simp only [Address.mk.injEq] at this
  exact Address.ext _ _ (Path.comp_inj_right.mp this.1).symm this.2.symm

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
  have h₁₃ := h₁.symm.trans h₃
  have h₂₄ := h₂.symm.trans h₄
  clear h₁ h₂ h₃ h₄
  simp only [SpecCondition.inflexibleCoe.injEq, heq_eq_eq, CodingFunction.code_eq_code_iff,
    true_and] at h₁₃ h₂₄
  obtain ⟨⟨ρ, h₅, h₆⟩, h₇, h₈, h₉⟩ := h₁₃
  obtain ⟨⟨ρ', h₅', h₆'⟩, _, h₈', h₉'⟩ := h₂₄
  have h₈'' := h₈.symm.trans h₈'
  have h₉'' := h₉.symm.trans h₉'
  clear h₈ h₈' h₉ h₉'
  have : ρ • t = ρ' • t
  · have := support_supports t (ρ'⁻¹ * ρ) ?_
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
    have h₈ := support_f_congr h₅'.symm j ?_
    swap
    · rw [Enumeration.smul_max, Support.comp_max_eq_of_canComp]
      exact hji'
      exact ⟨j, hji', c, hjc⟩
    simp only [Enumeration.smul_f, Support.comp_f_eq] at h₇ h₈
    obtain ⟨d, hd⟩ := comp_eq_same hσS hσT hj (P.B.cons P.hδ) c hjc
    rw [Support.comp_decomp_eq _ _ (by exact hjc),
      Support.comp_decomp_eq _ _ (by exact hd)] at h₇ h₈
    exact h₇.trans h₈.symm
  have : u = u'
  · refine support_tangle_ext hT P u u' ?_ h₈'' h₉'' hiT₁ hiT₂ hNT
    rw [h₆, h₆', ← Tangle.smul_set, this, ← Tangle.smul_set]
  cases this
  have hNTT' : NT.fst = NT'.fst
  · rw [hNT, hNT']
  refine NearLitter.ext ?_
  rw [← symmDiff_eq_bot, bot_eq_empty, eq_empty_iff_forall_not_mem]
  intro a ha
  obtain ⟨j, hj, -, -, hja⟩ :=
    hT.interferes hiT₁ hiT₁' hiT₂ hiT₂' (Support.Interferes.symmDiff hNTT' ha)
  simp only [Function.funext_iff, Set.ext_iff] at h₇
  obtain ⟨_, _, a', NS', _, ha', hS', -⟩ :=
    (h₇ i' j).mpr ⟨hiT₁', hj, a, NT', hNTT'.symm, ha, hiT₂', hja⟩
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

theorem convIndex {i : κ} (h : i < S.max) : i < T.max :=
  h.trans_eq (hσS.max_eq_max.trans hσT.max_eq_max.symm)

theorem convert_atomMap_eq {A : ExtendedIndex β} {a b : Atom} (h : ConvertAtom S T A a b) :
    ((convert hσS hσT A).atomMap a).get ⟨b, h⟩ = b :=
  PFun.get_eq (hg := (convertAtom_subsingleton hσS hσT A)) _ _ h

theorem convert_nearLitterMap_eq {A : ExtendedIndex β} {N₁ N₂ : NearLitter}
    (h : ConvertNearLitter S T A N₁ N₂) :
    ((convert hσS hσT A).nearLitterMap N₁).get ⟨N₂, h⟩ = N₂ :=
  PFun.get_eq (hg := (convertNearLitter_subsingleton hσS hσT A)) _ _ h

theorem convertAtom_dom {A : ExtendedIndex β} {a : Atom} (h : ⟨A, inl a⟩ ∈ S) :
    ∃ b, ConvertAtom S T A a b := by
  obtain ⟨i, hiS, hc⟩ := h
  have := hσS.atom_spec i hiS A a hc.symm
  obtain ⟨b, hb⟩ := hσT.of_eq_atom this
  exact ⟨b, i, hiS, (convIndex hσS hσT hiS), hc.symm, hb⟩

theorem convertNearLitter_dom {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ S) :
    ∃ N', ConvertNearLitter S T A N N' := by
  obtain ⟨i, hiS, hc⟩ := h
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' A N.1
  · have := hσS.flexible_spec i hiS A N hN hc.symm
    obtain ⟨N', -, hN'₂⟩ := hσT.of_eq_flexible this
    exact ⟨N', i, hiS, (convIndex hσS hσT hiS), hc.symm, hN'₂⟩
  · have := hσS.inflexibleBot_spec i hiS A N hN hc.symm
    obtain ⟨N', hN'₁, -, hN'₃⟩ := hσT.of_eq_inflexibleBot this
    exact ⟨N', i, hiS, (convIndex hσS hσT hiS), hc.symm, hN'₃⟩
  · have := hσS.inflexibleCoe_spec i hiS A N hN hc.symm
    obtain ⟨N', hN'₁, -, hN'₃⟩ := hσT.of_eq_inflexibleCoe this
    exact ⟨N', i, hiS, (convIndex hσS hσT hiS), hc.symm, hN'₃⟩

theorem convertAtom_injective {A : ExtendedIndex β} {a b c : Atom}
    (ha : ConvertAtom S T A a c) (hb : ConvertAtom S T A b c) : a = b := by
  obtain ⟨i, hiS, hiT, hiS', hiT'⟩ := ha
  obtain ⟨j, hjS, hjT, hjS', hjT'⟩ := hb
  have := (hσS.atom_spec i hiS A a hiS').symm.trans (hσT.atom_spec i hiT A c hiT')
  rw [SpecCondition.atom.injEq] at this
  obtain ⟨_, h⟩ := (Set.ext_iff.mp this.2.1 j).mpr ⟨hjT, hjT'⟩
  have := hjS'.symm.trans h
  cases this
  rfl

theorem convertAtom_mem_convertLitter_iff {A : ExtendedIndex β}
    {a a' : Atom} {N N' : NearLitter}
    (ha : ConvertAtom S T A a a') (hb : ConvertNearLitter S T A N N') :
    a' ∈ N' ↔ a ∈ N := by
  obtain ⟨i, hiS, hiT, hiS', hiT'⟩ := ha
  obtain ⟨j, hjS, hjT, hjS', hjT'⟩ := hb
  have := (hσS.atom_spec i hiS A a hiS').symm.trans (hσT.atom_spec i hiT A a' hiT')
  rw [SpecCondition.atom.injEq] at this
  constructor
  · intro h
    obtain ⟨_, _, hS', hN'⟩ := (Set.ext_iff.mp this.2.2 j).mpr ⟨hjT, N', hjT', h⟩
    cases hjS'.symm.trans hS'
    exact hN'
  · intro h
    obtain ⟨_, _, hT', hN'⟩ := (Set.ext_iff.mp this.2.2 j).mp ⟨hjS, N, hjS', h⟩
    cases hjT'.symm.trans hT'
    exact hN'

theorem support_tangle_ext' (hT : T.Strong)
    {A : ExtendedIndex β} (P : InflexibleCoePath A)
    (t₁ t₂ : Tangle P.δ) (ρ : Allowable P.δ)
    (h₁ : t₁.set = ρ • t₂.set)
    (h₂ : t₁.support.max = t₂.support.max)
    (h₃ :
      (fun j => {k | ∃ (hj : j < t₁.support.max) (hk : k < T.max),
        ⟨(P.B.cons P.hδ).comp (t₁.support.f j hj).1, (t₁.support.f j hj).2⟩ =
          T.f k hk}) =
      (fun j => {k | ∃ (hj : j < t₂.support.max) (hk : k < S.max),
        ⟨(P.B.cons P.hδ).comp (t₂.support.f j hj).1, (t₂.support.f j hj).2⟩ =
          S.f k hk}))
    {i : κ} (hi₁ : i < S.max) (hi₂ : i < T.max) {N : NearLitter}
    (hi₃ : T.f i hi₂ = ⟨A, inr N⟩) (hi₄ : N.1 = fuzz P.hδε t₁)
    (hi₅ : (T.before i hi₂).comp (P.B.cons P.hδ) = ρ • (S.before i hi₁).comp (P.B.cons P.hδ)) :
    t₁ = ρ • t₂ := by
  suffices : t₁.support = ρ • t₂.support
  · refine Tangle.ext _ _ ?_ ?_
    · rw [Tangle.smul_set, h₁]
    · rw [smul_support, this]
  refine Enumeration.ext' h₂ ?_
  intro k hku hku'
  have := hT.precedes hi₂ ⟨(P.B.cons P.hδ).comp (t₁.support.f k hku).1, (t₁.support.f k hku).2⟩ ?_
  swap
  · have := Support.Precedes.fuzz _ N ⟨P, t₁, hi₄⟩ (t₁.support.f k hku) ⟨k, hku, rfl⟩
    rw [← P.hA, ← hi₃] at this
    exact this
  obtain ⟨j, hjT, hji, hjeq⟩ := this
  obtain ⟨_, hjS, hjeq'⟩ := (Set.ext_iff.mp (congr_fun h₃ k) j).mp ⟨hku, hjT, hjeq.symm⟩
  have hccS : (S.before i hi₁).CanComp (P.B.cons P.hδ) := ⟨j, hji, _, hjeq'.symm⟩
  have hccT : (T.before i hi₂).CanComp (P.B.cons P.hδ) := ⟨j, hji, _, hjeq⟩
  have := support_f_congr hi₅ j (Support.comp_max_eq_of_canComp hccT ▸ hji)
  rw [Support.comp_f_eq, Support.comp_decomp_eq hccT hji hjeq,
    Enumeration.smul_f, Support.comp_f_eq, Support.comp_decomp_eq hccS hji hjeq'.symm] at this
  exact this

theorem convertNearLitter_fst {A : ExtendedIndex β} {N₁ N₂ N₃ N₄ : NearLitter}
    (h₁ : ConvertNearLitter S T A N₁ N₃) (h₂ : ConvertNearLitter S T A N₂ N₄)
    (h : N₁.1 = N₂.1) : N₃.1 = N₄.1 := by
  obtain ⟨i, hiS, hiT, hiS', hiT'⟩ := h₁
  obtain ⟨j, hjS, hjT, hjS', hjT'⟩ := h₂
  obtain (hN | ⟨⟨P, a₁, hN⟩⟩ | ⟨⟨P, t₁, hN⟩⟩) := flexible_cases' A N₁.1
  · have h₁ := hσS.flexible_spec i hiS A N₁ hN hiS'
    obtain ⟨N', hN₃, hN'₃⟩ := hσT.of_eq_flexible h₁
    cases hiT'.symm.trans hN'₃
    have h₂ := hσS.flexible_spec j hjS A N₂ (h ▸ hN) hjS'
    obtain ⟨N', hN₄, hN'₄⟩ := hσT.of_eq_flexible h₂
    cases hjT'.symm.trans hN'₄
    have h₃ := hσT.flexible_spec i hiT A N₃ hN₃ hiT'
    have := h₁.symm.trans h₃
    rw [SpecCondition.flexible.injEq] at this
    obtain ⟨_, N', h₁, h₂⟩ := (Set.ext_iff.mp this.2.1 j).mp ⟨hjS, N₂, hjS', h.symm⟩
    cases hjT'.symm.trans h₁
    exact h₂.symm
  · have h₁ := hσS.inflexibleBot_spec i hiS A N₁ ⟨P, a₁, hN⟩ hiS'
    obtain ⟨N', a₃, hN₃, hN'₃⟩ := hσT.of_eq_inflexibleBot h₁
    cases hiT'.symm.trans hN'₃
    have h₂ := hσS.inflexibleBot_spec j hjS A N₂ ⟨P, a₁, h ▸ hN⟩ hjS'
    obtain ⟨N', a₄, hN₄, hN'₄⟩ := hσT.of_eq_inflexibleBot h₂
    cases hjT'.symm.trans hN'₄
    have h₃ := hσT.inflexibleBot_spec i hiT A N₃ ⟨P, a₃, hN₃⟩ hiT'
    have h₄ := hσT.inflexibleBot_spec j hjT A N₄ ⟨P, a₄, hN₄⟩ hjT'
    have h₁₃ := h₁.symm.trans h₃
    have h₂₄ := h₂.symm.trans h₄
    rw [SpecCondition.inflexibleBot.injEq] at h₁₃ h₂₄
    clear h₁ h₂ h₃ h₄
    have h₁' := Support.Precedes.fuzzBot A N₁ ⟨P, a₁, hN⟩
    rw [← P.hA, ← hiS'] at h₁'
    obtain ⟨j₁, hj₁S, -, hj₁S'⟩ := hS.precedes hiS ⟨P.B.cons (bot_lt_coe _), inl a₁⟩ h₁'
    obtain ⟨_, hj₁T⟩ := (Set.ext_iff.mp h₁₃.2.2.1 j₁).mp ⟨hj₁S, hj₁S'⟩
    obtain ⟨_, hj₂T⟩ := (Set.ext_iff.mp h₂₄.2.2.1 j₁).mp ⟨hj₁S, hj₁S'⟩
    cases hj₁T.symm.trans hj₂T
    rw [hN₃, hN₄]
  · have h₁ := hσS.inflexibleCoe_spec i hiS A N₁ ⟨P, t₁, hN⟩ hiS'
    obtain ⟨N', t₃, hN₃, hN'₃⟩ := hσT.of_eq_inflexibleCoe h₁
    cases hiT'.symm.trans hN'₃
    have h₂ := hσS.inflexibleCoe_spec j hjS A N₂ ⟨P, t₁, h ▸ hN⟩ hjS'
    obtain ⟨N', t₄, hN₄, hN'₄⟩ := hσT.of_eq_inflexibleCoe h₂
    cases hjT'.symm.trans hN'₄
    have h₃ := hσT.inflexibleCoe_spec i hiT A N₃ ⟨P, t₃, hN₃⟩ hiT'
    have h₄ := hσT.inflexibleCoe_spec j hjT A N₄ ⟨P, t₄, hN₄⟩ hjT'
    have h₁₃ := h₁.symm.trans h₃
    have h₂₄ := h₂.symm.trans h₄
    rw [SpecCondition.inflexibleCoe.injEq] at h₁₃ h₂₄
    suffices : t₃ = t₄
    · rw [hN₃, hN₄, this]
    have h₁₃' := eq_of_heq h₁₃.2.2.1
    have h₂₄' := eq_of_heq h₂₄.2.2.1
    simp only [CodingFunction.code_eq_code_iff] at h₁₃' h₂₄'
    obtain ⟨ρ, hρ, h₁₃'⟩ := h₁₃'
    obtain ⟨ρ', hρ', h₂₄'⟩ := h₂₄'
    have h₁₃'' := h₁₃.2.2.2.2
    have h₂₄'' := h₂₄.2.2.2.2
    clear h₁ h₂ h₃ h₄ h₁₃ h₂₄ hN'₃ hN'₄
    have : t₃ = ρ • t₁ :=
      support_tangle_ext' hT P t₃ t₁ ρ h₁₃' h₁₃''.1.symm h₁₃''.2.symm hiS hiT hiT' hN₃ hρ
    cases this
    have : t₄ = ρ' • t₁ :=
      support_tangle_ext' hT P t₄ t₁ ρ' h₂₄' h₂₄''.1.symm h₂₄''.2.symm hjS hjT hjT' hN₄ hρ'
    cases this
    have := support_supports t₁ (ρ'⁻¹ * ρ) ?_
    · rw [mul_smul, inv_smul_eq_iff] at this
      exact this
    intro c hc
    rw [mul_smul, inv_smul_eq_iff]
    have : ∃ k hk, k < i ∧ k < j ∧ S.f k hk = ⟨(P.B.cons P.hδ).comp c.1, c.2⟩
    · by_cases hij : i < j
      · have hc' := Support.Precedes.fuzz A N₁ ⟨P, t₁, hN⟩ c hc
        rw [← P.hA, ← hiS'] at hc'
        obtain ⟨k, hk, hki, hkS⟩ := hS.precedes hiS _ hc'
        exact ⟨k, hk, hki, hki.trans hij, hkS⟩
      · have hc' := Support.Precedes.fuzz A N₂ ⟨P, t₁, h ▸ hN⟩ c hc
        rw [← P.hA, ← hjS'] at hc'
        obtain ⟨k, hk, hki, hkS⟩ := hS.precedes hjS _ hc'
        exact ⟨k, hk, hki.trans_le (le_of_not_lt hij), hki, hkS⟩
    obtain ⟨k, hk, hki, hkj, hkS⟩ := this
    obtain ⟨d, hd⟩ := comp_eq_same hσS hσT hk (P.B.cons P.hδ) c hkS
    have h₁' := support_f_congr hρ k ?_
    swap
    · rw [Support.comp_max_eq_of_canComp]
      exact hki
      exact ⟨k, hki, d, hd⟩
    rw [Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hd),
      Enumeration.smul_f, Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hkS)] at h₁'
    have h₂' := support_f_congr hρ' k ?_
    swap
    · rw [Support.comp_max_eq_of_canComp]
      exact hkj
      exact ⟨k, hkj, d, hd⟩
    rw [Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hd),
      Enumeration.smul_f, Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hkS)] at h₂'
    rw [← h₁', ← h₂']

theorem convertNearLitter_fst' {A : ExtendedIndex β} {N₁ N₂ N₃ N₄ : NearLitter}
    (h₁ : ConvertNearLitter S T A N₁ N₃) (h₂ : ConvertNearLitter S T A N₂ N₄)
    (h : N₃.1 = N₄.1) : N₁.1 = N₂.1 := by
  obtain ⟨i, hiS, hiT, hiS', hiT'⟩ := h₁
  obtain ⟨j, hjS, hjT, hjS', hjT'⟩ := h₂
  obtain (hN | ⟨⟨P, a₁, hN⟩⟩ | ⟨⟨P, t₁, hN⟩⟩) := flexible_cases' A N₁.1
  · have h₁ := hσS.flexible_spec i hiS A N₁ hN hiS'
    obtain ⟨N', hN₃, hN'₃⟩ := hσT.of_eq_flexible h₁
    cases hiT'.symm.trans hN'₃
    have h₄ := hσT.flexible_spec j hjT A N₄ (h ▸ hN₃) hjT'
    obtain ⟨N', hN₂, hN'₂⟩ := hσS.of_eq_flexible h₄
    cases hjS'.symm.trans hN'₂
    have h₂ := hσS.flexible_spec j hjS A N₂ hN₂ hjS'
    have := h₂.symm.trans h₄
    rw [SpecCondition.flexible.injEq] at this
    obtain ⟨_, N', h₁, h₂⟩ := (Set.ext_iff.mp this.2.1 i).mpr ⟨hiT, N₃, hiT', h⟩
    cases hiS'.symm.trans h₁
    exact h₂
  · have h₁ := hσS.inflexibleBot_spec i hiS A N₁ ⟨P, a₁, hN⟩ hiS'
    obtain ⟨N', a₃, hN₃, hN'₃⟩ := hσT.of_eq_inflexibleBot h₁
    cases hiT'.symm.trans hN'₃
    have h₄ := hσT.inflexibleBot_spec j hjT A N₄ ⟨P, a₃, h ▸ hN₃⟩ hjT'
    obtain ⟨N', a₂, hN₂, hN'₂⟩ := hσS.of_eq_inflexibleBot h₄
    cases hjS'.symm.trans hN'₂
    have h₂ := hσS.inflexibleBot_spec j hjS A N₂ ⟨P, a₂, hN₂⟩ hjS'
    have h₃ := hσT.inflexibleBot_spec i hiT A N₃ ⟨P, a₃, hN₃⟩ hiT'
    have h₁₃ := h₁.symm.trans h₃
    have h₂₄ := h₂.symm.trans h₄
    rw [SpecCondition.inflexibleBot.injEq] at h₁₃ h₂₄
    clear h₁ h₂ h₃ h₄
    have h₃' := Support.Precedes.fuzzBot A N₃ ⟨P, a₃, hN₃⟩
    rw [← P.hA, ← hiT'] at h₃'
    obtain ⟨j₁, hj₁S, -, hj₁S'⟩ := hT.precedes hiT ⟨P.B.cons (bot_lt_coe _), inl a₃⟩ h₃'
    obtain ⟨_, hj₁T⟩ := (Set.ext_iff.mp h₁₃.2.2.1 j₁).mpr ⟨hj₁S, hj₁S'⟩
    obtain ⟨_, hj₂T⟩ := (Set.ext_iff.mp h₂₄.2.2.1 j₁).mpr ⟨hj₁S, hj₁S'⟩
    cases hj₁T.symm.trans hj₂T
    rw [hN, hN₂]
  · have h₁ := hσS.inflexibleCoe_spec i hiS A N₁ ⟨P, t₁, hN⟩ hiS'
    obtain ⟨N', t₃, hN₃, hN'₃⟩ := hσT.of_eq_inflexibleCoe h₁
    cases hiT'.symm.trans hN'₃
    have h₄ := hσT.inflexibleCoe_spec j hjT A N₄ ⟨P, t₃, h ▸ hN₃⟩ hjT'
    obtain ⟨N', t₂, hN₂, hN'₂⟩ := hσS.of_eq_inflexibleCoe h₄
    cases hjS'.symm.trans hN'₂
    have h₂ := hσS.inflexibleCoe_spec j hjS A N₂ ⟨P, t₂, hN₂⟩ hjS'
    have h₃ := hσT.inflexibleCoe_spec i hiT A N₃ ⟨P, t₃, hN₃⟩ hiT'
    have h₁₃ := h₁.symm.trans h₃
    have h₂₄ := h₂.symm.trans h₄
    rw [SpecCondition.inflexibleCoe.injEq] at h₁₃ h₂₄
    suffices : t₁ = t₂
    · rw [hN, hN₂, this]
    have h₁₃' := eq_of_heq h₁₃.2.2.1
    have h₂₄' := eq_of_heq h₂₄.2.2.1
    simp only [CodingFunction.code_eq_code_iff] at h₁₃' h₂₄'
    obtain ⟨ρ, hρ, hρ₂⟩ := h₁₃'
    obtain ⟨ρ', hρ', hρ'₂⟩ := h₂₄'
    have ht₃₁ : t₃ = ρ • t₁ :=
      support_tangle_ext' hT P t₃ t₁ ρ hρ₂
        h₁₃.2.2.2.2.1.symm h₁₃.2.2.2.2.2.symm hiS hiT hiT' hN₃ hρ
    have ht₃₂ : t₃ = ρ' • t₂ :=
      support_tangle_ext' hT P t₃ t₂ ρ' hρ'₂
        h₂₄.2.2.2.2.1.symm h₂₄.2.2.2.2.2.symm hjS hjT hjT' (h ▸ hN₃) hρ'
    cases ht₃₁
    rw [← inv_smul_eq_iff, smul_smul] at ht₃₂
    subst ht₃₂
    clear h₁ h₂ h₃ h₄ h₁₃ h₂₄ hN'₃
    have := support_supports (ρ • t₁) (ρ' * ρ⁻¹) ?_
    · rw [mul_smul, inv_smul_smul] at this
      rw [mul_smul, ← smul_eq_iff_eq_inv_smul]
      exact this
    intro c hc
    rw [mul_smul]
    have : ∃ k hk, k < i ∧ k < j ∧ T.f k hk = ⟨(P.B.cons P.hδ).comp c.1, c.2⟩
    · by_cases hij : i < j
      · have hc' := Support.Precedes.fuzz A N₃ ⟨P, ρ • t₁, hN₃⟩ c hc
        rw [← P.hA, ← hiT'] at hc'
        obtain ⟨k, hk, hki, hkT⟩ := hT.precedes hiT _ hc'
        exact ⟨k, hk, hki, hki.trans hij, hkT⟩
      · have hc' := Support.Precedes.fuzz A N₄ ⟨P, ρ • t₁, h ▸ hN₃⟩ c hc
        rw [← P.hA, ← hjT'] at hc'
        obtain ⟨k, hk, hki, hkT⟩ := hT.precedes hjT _ hc'
        exact ⟨k, hk, hki.trans_le (le_of_not_lt hij), hki, hkT⟩
    obtain ⟨k, hk, hki, hkj, hkT⟩ := this
    obtain ⟨d, hd⟩ := comp_eq_same hσT hσS hk (P.B.cons P.hδ) c hkT
    have h₁' := support_f_congr hρ.symm k ?_
    swap
    · rw [Enumeration.smul_max, Support.comp_max_eq_of_canComp]
      exact hki
      exact ⟨k, hki, d, hd⟩
    rw [Enumeration.smul_f, Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hd),
      Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hkT)] at h₁'
    have h₂' := support_f_congr hρ'.symm k ?_
    swap
    · rw [Enumeration.smul_max, Support.comp_max_eq_of_canComp]
      exact hkj
      exact ⟨k, hkj, d, hd⟩
    rw [Enumeration.smul_f, Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hd),
      Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hkT)] at h₂'
    rw [← h₁', inv_smul_smul, h₂', h₁']

theorem convert_lawful : (convert hσS hσT).Lawful := by
  intro A
  constructor
  case atomMap_injective =>
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩ h
    rw [convert_atomMap_eq hσS hσT ha, convert_atomMap_eq hσS hσT hb] at h
    subst h
    exact convertAtom_injective hσS hσT ha hb
  case atom_mem_iff =>
    rintro a ⟨a', ha⟩ N ⟨N', hN⟩
    rw [convert_atomMap_eq hσS hσT ha, convert_nearLitterMap_eq hσS hσT hN]
    exact convertAtom_mem_convertLitter_iff hσS hσT ha hN
  case dom_of_mem_symmDiff =>
    rintro a N₁ N₂ hN ⟨N₁', i, hiS, hiT, hiS', -⟩ ⟨N₂', j, hjS, hjT, hjS', -⟩ ha
    obtain ⟨k, hkS, -, -, hk⟩ :=
      hS.interferes hiS hjS hiS' hjS' (Support.Interferes.symmDiff hN ha)
    exact convertAtom_dom hσS hσT ⟨k, hkS, hk.symm⟩
  case dom_of_mem_inter =>
    rintro a N₁ N₂ hN ⟨N₁', i, hiS, hiT, hiS', -⟩ ⟨N₂', j, hjS, hjT, hjS', -⟩ ha
    obtain ⟨k, hkS, -, -, hk⟩ :=
      hS.interferes hiS hjS hiS' hjS' (Support.Interferes.inter hN ha)
    exact convertAtom_dom hσS hσT ⟨k, hkS, hk.symm⟩
  case ran_of_mem_symmDiff =>
    rintro a N₁ N₂ hN ⟨N₁', i, hiS, hiT, hiS', hiT'⟩ ⟨N₂', j, hjS, hjT, hjS', hjT'⟩ ha
    rw [convert_nearLitterMap_eq hσS hσT ⟨i, hiS, hiT, hiS', hiT'⟩,
      convert_nearLitterMap_eq hσS hσT ⟨j, hjS, hjT, hjS', hjT'⟩] at ha
    obtain ⟨k, hkT, -, -, hk⟩ := hT.interferes hiT hjT hiT' hjT'
      (Support.Interferes.symmDiff
        (convertNearLitter_fst hσS hσT ⟨i, hiS, hiT, hiS', hiT'⟩ ⟨j, hjS, hjT, hjS', hjT'⟩ hN) ha)
    have := hσT.atom_spec k hkT A a hk
    obtain ⟨a', ha'⟩ := hσS.of_eq_atom this
    refine ⟨a', convertAtom_dom hσS hσT ⟨k, convIndex hσT hσS hkT, ha'.symm⟩, ?_⟩
    rw [convert_atomMap_eq hσS hσT ⟨k, convIndex hσT hσS hkT, hkT, ha', hk⟩]
  case ran_of_mem_inter =>
    rintro a N₁ N₂ hN ⟨N₁', i, hiS, hiT, hiS', hiT'⟩ ⟨N₂', j, hjS, hjT, hjS', hjT'⟩ ha
    rw [convert_nearLitterMap_eq hσS hσT ⟨i, hiS, hiT, hiS', hiT'⟩,
      convert_nearLitterMap_eq hσS hσT ⟨j, hjS, hjT, hjS', hjT'⟩] at ha
    obtain ⟨k, hkT, -, -, hk⟩ := hT.interferes hiT hjT hiT' hjT'
      (Support.Interferes.inter
        (hN ∘ convertNearLitter_fst' hσS hσT
          ⟨i, hiS, hiT, hiS', hiT'⟩ ⟨j, hjS, hjT, hjS', hjT'⟩) ha)
    have := hσT.atom_spec k hkT A a hk
    obtain ⟨a', ha'⟩ := hσS.of_eq_atom this
    refine ⟨a', convertAtom_dom hσS hσT ⟨k, convIndex hσT hσS hkT, ha'.symm⟩, ?_⟩
    rw [convert_atomMap_eq hσS hσT ⟨k, convIndex hσT hσS hkT, hkT, ha', hk⟩]

theorem convert_coherentDom : (convert hσS hσT).CoherentDom := by
  constructor
  case mapFlexible =>
    rintro A N ⟨N', hN₁⟩ hN₂
    rw [convert_nearLitterMap_eq hσS hσT hN₁]
    obtain ⟨i, hiS, hiT, hiS', hiT'⟩ := hN₁
    have := hσS.flexible_spec i hiS A N hN₂ hiS'
    obtain ⟨_, hN₃, h⟩ := hσT.of_eq_flexible this
    cases hiT'.symm.trans h
    exact hN₃
  case atom_bot_dom =>
    rintro γ _ A ε _ hε a Nt hNt ⟨N', i, hiS, hiT, hiS', -⟩
    have := Support.Precedes.fuzzBot _ Nt ⟨⟨γ, ε, hε, A, rfl⟩, a, hNt⟩
    rw [← hiS'] at this
    obtain ⟨j, hj, -, hjS⟩ := hS.precedes hiS _ this
    obtain ⟨a', ha'⟩ := hσT.of_eq_atom (hσS.atom_spec j hj _ a hjS)
    exact ⟨a', j, hj, convIndex hσS hσT hj, hjS, ha'⟩
  case atom_dom =>
    rintro γ _ A δ _ ε _ hδ hε hδε t B a Nt hNt ha ⟨N', i, hiS, hiT, hiS', -⟩
    have := Support.Precedes.fuzz _ Nt ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, hNt⟩ _ ha
    rw [← hiS'] at this
    obtain ⟨j, hj, -, hjS⟩ := hS.precedes hiS _ this
    obtain ⟨a', ha'⟩ := hσT.of_eq_atom (hσS.atom_spec j hj _ a hjS)
    exact ⟨a', j, hj, convIndex hσS hσT hj, hjS, ha'⟩
  case nearLitter_dom =>
    rintro γ _ A δ _ ε _ hδ hε hδε t B N Nt hNt hN ⟨N', i, hiS, hiT, hiS', -⟩
    have := Support.Precedes.fuzz _ Nt ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, hNt⟩ _ hN
    rw [← hiS'] at this
    obtain ⟨j, hj, -, hjS⟩ := hS.precedes hiS _ this
    obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' ((A.cons hδ).comp B) N.1
    · obtain ⟨N', -, h₂⟩ := hσT.of_eq_flexible (hσS.flexible_spec j hj _ N hN hjS)
      exact ⟨N', j, hj, convIndex hσS hσT hj, hjS, h₂⟩
    · obtain ⟨N', h₁, -, h₂⟩ := hσT.of_eq_inflexibleBot (hσS.inflexibleBot_spec j hj _ N hN hjS)
      exact ⟨N', j, hj, convIndex hσS hσT hj, hjS, h₂⟩
    · obtain ⟨N', h₁, -, h₂⟩ := hσT.of_eq_inflexibleCoe (hσS.inflexibleCoe_spec j hj _ N hN hjS)
      exact ⟨N', j, hj, convIndex hσS hσT hj, hjS, h₂⟩

theorem convert_coherent : (convert hσS hσT).Coherent := by
  constructor
  case toCoherentDom => exact convert_coherentDom hσS hσT
  case coherent_coe =>
    rintro γ _ A δ _ ε _ hδ hε hδε t Nt hNt ⟨Nt', h⟩ ρ h₁ h₂
    rw [convert_nearLitterMap_eq hσS hσT h]
    obtain ⟨i, hiS, hiT, hiS', hiT'⟩ := h
    have hiS'' := hσS.inflexibleCoe_spec i hiS
      ((A.cons hε).cons (bot_lt_coe _)) Nt ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, hNt⟩ hiS'
    obtain ⟨Nt'', t', hNt', h⟩ := hσT.of_eq_inflexibleCoe hiS''
    cases hiT'.symm.trans h
    have hiT'' := hσT.inflexibleCoe_spec i hiT
      ((A.cons hε).cons (bot_lt_coe _)) Nt' ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t', hNt'⟩ hiT'
    suffices : t' = Allowable.comp (Hom.toPath hδ) ρ • t
    · rw [hNt', this]
    have := hiS''.symm.trans hiT''
    simp only [SpecCondition.inflexibleCoe.injEq, heq_eq_eq, CodingFunction.code_eq_code_iff,
      true_and] at this
    obtain ⟨ρ', hρ', hρ''⟩ := this.1
    have : t' = ρ' • t :=
      support_tangle_ext' (S := S) hT ⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩ t' t ρ' hρ''
        this.2.2.1.symm this.2.2.2.symm hiS hiT hiT' hNt' hρ'
    cases this
    clear hiS'' hiT'' this
    have := support_supports t (ρ'⁻¹ * Allowable.comp (Hom.toPath hδ) ρ) ?_
    · rw [mul_smul, inv_smul_eq_iff] at this
      exact this.symm
    intro c hc
    rw [mul_smul, inv_smul_eq_iff]
    have : ∃ k hk, k < i ∧ S.f k hk = ⟨(A.cons hδ).comp c.1, c.2⟩
    · have hc' := Support.Precedes.fuzz _ Nt ⟨⟨γ, δ, ε, hδ, hε, hδε, A, rfl⟩, t, hNt⟩ c hc
      rw [← hiS'] at hc'
      obtain ⟨k, hk, hki, hkS⟩ := hS.precedes hiS _ hc'
      exact ⟨k, hk, hki, hkS⟩
    obtain ⟨k, hk, hki, hkS⟩ := this
    have h' := support_f_congr hρ'.symm k ?_
    swap
    · rw [Enumeration.smul_max, Support.comp_max_eq_of_canComp]
      exact hki
      exact ⟨k, hki, c, hkS⟩
    obtain ⟨d, hd⟩ := comp_eq_same hσS hσT hk (A.cons hδ) c hkS
    rw [Enumeration.smul_f, Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hkS),
      Support.comp_f_eq, Support.comp_decomp_eq _ _ (by exact hd)] at h'
    subst h'
    obtain ⟨B, a | N⟩ := c
    · obtain ⟨a', ha'⟩ := (convert_coherentDom hσS hσT).atom_dom A hδ hε hδε hNt hc
        ⟨Nt', i, hiS, hiT, hiS', hiT'⟩
      have := h₁ B a hc
      rw [convert_atomMap_eq hσS hσT ha'] at this
      have : ConvertAtom S T ((A.cons hδ).comp B) a (Allowable.toStructPerm ρ' B • a) :=
        ⟨k, hk, convIndex hσS hσT hk, hkS, hd⟩
      cases convertAtom_subsingleton hσS hσT _ _ _ _ ha' this
      refine Address.ext _ _ rfl ?_
      simp only [Allowable.smul_address, Allowable.toStructPerm_comp, Tree.comp_apply, smul_inl,
        inl.injEq]
      exact this.symm
    · obtain ⟨N', hN'⟩ := (convert_coherentDom hσS hσT).nearLitter_dom A hδ hε hδε hNt hc
        ⟨Nt', i, hiS, hiT, hiS', hiT'⟩
      have := h₂ B N hc
      rw [convert_nearLitterMap_eq hσS hσT hN'] at this
      have : ConvertNearLitter S T ((A.cons hδ).comp B) N (Allowable.toStructPerm ρ' B • N) :=
        ⟨k, hk, convIndex hσS hσT hk, hkS, hd⟩
      cases convertNearLitter_subsingleton hσS hσT _ _ _ _ hN' this
      refine Address.ext _ _ rfl ?_
      simp only [Allowable.smul_address, Allowable.toStructPerm_comp, Tree.comp_apply, smul_inr,
        inr.injEq]
      exact this.symm
  case coherent_bot =>
    intro γ _ A ε _ hε a Nt hNt ⟨Nt', hNt'⟩ ρ h
    rw [convert_nearLitterMap_eq hσS hσT hNt']
    obtain ⟨i, hiS, hiT, hiS', hiT'⟩ := hNt'
    have hiS'' := hσS.inflexibleBot_spec i hiS
      ((A.cons hε).cons (bot_lt_coe _)) Nt ⟨⟨γ, ε, hε, A, rfl⟩, a, hNt⟩ hiS'
    obtain ⟨Nt'', a', hNt', h'⟩ := hσT.of_eq_inflexibleBot hiS''
    cases hiT'.symm.trans h'
    have hiT'' := hσT.inflexibleBot_spec i hiT
      ((A.cons hε).cons (bot_lt_coe _)) Nt' ⟨⟨γ, ε, hε, A, rfl⟩, a', hNt'⟩ hiT'
    suffices : a' = Allowable.toStructPerm ρ (Hom.toPath (bot_lt_coe _)) • a
    · simp only [hNt', this, ofBot_smul, Allowable.toStructPerm_apply]
    have : ∃ k hk, k < i ∧ S.f k hk = ⟨A.cons (bot_lt_coe _), inl a⟩
    · have hc' := Support.Precedes.fuzzBot _ Nt ⟨⟨γ, ε, hε, A, rfl⟩, a, hNt⟩
      rw [← hiS'] at hc'
      obtain ⟨k, hk, hki, hkS⟩ := hS.precedes hiS _ hc'
      exact ⟨k, hk, hki, hkS⟩
    obtain ⟨k, hk, -, hkS⟩ := this
    rw [← h, convert_atomMap_eq hσS hσT]
    refine ⟨k, hk, convIndex hσS hσT hk, hkS, ?_⟩
    have := hiS''.symm.trans hiT''
    simp only [SpecCondition.inflexibleBot.injEq, heq_eq_eq, true_and] at this
    obtain ⟨_, h⟩ := (Set.ext_iff.mp this.1 k).mp ⟨hk, hkS⟩
    exact h

noncomputable def convertAllowable : Allowable β :=
  ((convert hσS hσT).freedom_of_action (convert_lawful hσS hσT) (convert_coherent hσS hσT)).choose

theorem convertAllowable_spec :
    (convert hσS hσT).Approximates (Allowable.toStructPerm <| convertAllowable hσS hσT) :=
  ((convert hσS hσT).freedom_of_action
    (convert_lawful hσS hσT) (convert_coherent hσS hσT)).choose_spec

theorem convert_atomMap_get {A : ExtendedIndex β} {a : Atom} {i : κ} (hiS : i < S.max)
    (h : S.f i hiS = ⟨A, inl a⟩) :
    T.f i (convIndex hσS hσT hiS) =
      ⟨A, inl (((convert hσS hσT A).atomMap a).get
        (convertAtom_dom hσS hσT ⟨i, hiS, h.symm⟩))⟩ := by
  have h₁ := hσS.atom_spec i hiS A a h
  obtain ⟨b, hb⟩ := hσT.of_eq_atom h₁
  have : ConvertAtom S T A a b := ⟨i, hiS, convIndex hσS hσT hiS, h, hb⟩
  rw [convert_atomMap_eq hσS hσT this]
  exact hb

theorem convert_nearLitterMap_get {A : ExtendedIndex β} {N : NearLitter} {i : κ} (hiS : i < S.max)
    (h : S.f i hiS = ⟨A, inr N⟩) :
    T.f i (convIndex hσS hσT hiS) =
      ⟨A, inr (((convert hσS hσT A).nearLitterMap N).get
        (convertNearLitter_dom hσS hσT ⟨i, hiS, h.symm⟩))⟩ := by
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' A N.1
  · have := hσS.flexible_spec i hiS A N hN h
    obtain ⟨N', -, hN'₂⟩ := hσT.of_eq_flexible this
    have : ConvertNearLitter S T A N N' := ⟨i, hiS, convIndex hσS hσT hiS, h, hN'₂⟩
    rw [convert_nearLitterMap_eq hσS hσT this]
    exact hN'₂
  · have := hσS.inflexibleBot_spec i hiS A N hN h
    obtain ⟨N', hN'₁, -, hN'₃⟩ := hσT.of_eq_inflexibleBot this
    have : ConvertNearLitter S T A N N' := ⟨i, hiS, convIndex hσS hσT hiS, h, hN'₃⟩
    rw [convert_nearLitterMap_eq hσS hσT this]
    exact hN'₃
  · have := hσS.inflexibleCoe_spec i hiS A N hN h
    obtain ⟨N', hN'₁, -, hN'₃⟩ := hσT.of_eq_inflexibleCoe this
    have : ConvertNearLitter S T A N N' := ⟨i, hiS, convIndex hσS hσT hiS, h, hN'₃⟩
    rw [convert_nearLitterMap_eq hσS hσT this]
    exact hN'₃

theorem convertAllowable_smul' (i : κ) (hiS : i < S.max) (hiT : i < T.max) :
    convertAllowable hσS hσT • S.f i hiS = T.f i hiT := by
  set c := S.f i hiS with hc
  obtain ⟨A, a | N⟩ := c
  · have := (convertAllowable_spec hσS hσT A).map_atom a (convertAtom_dom hσS hσT ⟨i, hiS, hc⟩)
    rw [Allowable.smul_address, smul_inl, this, convert_atomMap_get hσS hσT hiS hc.symm]
  · have := (convertAllowable_spec hσS hσT A).map_nearLitter N
      (convertNearLitter_dom hσS hσT ⟨i, hiS, hc⟩)
    rw [Allowable.smul_address, smul_inr, this, convert_nearLitterMap_get hσS hσT hiS hc.symm]

theorem convertAllowable_smul : convertAllowable hσS hσT • S = T := by
  refine Enumeration.ext' (hσS.max_eq_max.trans hσT.max_eq_max.symm) ?_
  exact convertAllowable_smul' hσS hσT

end ConNF
