import ConNF.Foa.Basic.Flexible

/-!
# Reductions of supports
-/

universe u

open MulAction Quiver Set Sum WithBot

open scoped Cardinal Pointwise

namespace ConNF

variable [Params.{u}] (α : Λ) [BasePositions] [Phase2Assumptions α]
variable {β : Λ} {G : Type _} {τ : Type _} [SMul G (SupportCondition β)] [SMul G τ] {x : τ}

/-- A support condition is *reduced* if it is an atom or a litter. -/
@[mk_iff]
inductive Reduced {β : TypeIndex} : SupportCondition β → Prop
  | mkAtom (a : Atom) (B : ExtendedIndex β) : Reduced (inl a, B)
  | mkLitter (L : Litter) (B : ExtendedIndex β) : Reduced (inr L.toNearLitter, B)

/-- The *reduction* of a set of support conditions is the downward closure of the set under
the constrains relation, but we only keep reduced conditions. -/
def reduction (S : Set (SupportCondition β)) : Set (SupportCondition β) :=
  {c | ∃ d ∈ S, c ≤[α] d} ∩ setOf Reduced

theorem mem_reduction_of_reduced (S : Set (SupportCondition β)) (c : SupportCondition β)
    (hc₁ : Reduced c) (hc₂ : c ∈ S) : c ∈ reduction α S :=
  ⟨⟨c, hc₂, Relation.ReflTransGen.refl⟩, hc₁⟩

theorem mem_reduction_of_reduced_constrains (S : Set (SupportCondition β))
    (c d : SupportCondition β) (hc : Reduced c) (hcd : c ≺[α] d) (hd : d ∈ S) : c ∈ reduction α S :=
  ⟨⟨d, hd, Relation.ReflTransGen.single hcd⟩, hc⟩

def nthReduction (S : Set (SupportCondition β)) : ℕ → Set (SupportCondition β)
  | 0 => S
  | n + 1 => {c | ∃ d, d ∈ nthReduction S n ∧ c ≺[α] d}

theorem small_nthReduction {S : Set (SupportCondition β)} {n : ℕ} (h : Small S) :
    Small (nthReduction α S n) := by
  induction' n with n hn
  exact h
  rw [nthReduction]
  simp_rw [← exists_prop, Subtype.exists', setOf_exists]
  refine' small_iUnion hn _
  rintro ⟨c, _⟩
  exact small_constrains c

theorem mem_nthReduction_iff {S : Set (SupportCondition β)} {n : ℕ} {c : SupportCondition β} :
    c ∈ nthReduction α S n ↔
      ∃ l,
        List.Chain (Constrains α β) c l ∧
          l.length = n ∧ (c::l).getLast (List.cons_ne_nil _ _) ∈ S := by
  induction' n with n hn generalizing c
  · rw [nthReduction]
    constructor
    · intro h
      exact ⟨[], List.Chain.nil, rfl, h⟩
    · rintro ⟨l, h₁, h₂, h₃⟩
      rw [List.length_eq_zero] at h₂
      cases h₂
      exact h₃
  · simp only [nthReduction, mem_setOf_eq]
    constructor
    · rintro ⟨d, hd₁, hd₂⟩
      obtain ⟨l, hl₁, hl₂, hl₃⟩ := hn.mp hd₁
      refine' ⟨d::l, List.Chain.cons hd₂ hl₁, _, _⟩
      · rw [List.length_cons, hl₂]
      · rw [List.getLast_cons]
        exact hl₃
    · rintro ⟨_ | ⟨d, l⟩, hl₁, hl₂, hl₃⟩
      · cases hl₂
      obtain _ | ⟨hcd, hl₁⟩ := hl₁
      rw [List.getLast_cons] at hl₃
      have := hn.mpr ⟨l, hl₁, Nat.succ.inj hl₂, hl₃⟩
      exact ⟨d, this, hcd⟩

theorem reduction_eq_iUnion {S : Set (SupportCondition β)} :
    {c | ∃ d ∈ S, c ≤[α] d} = ⋃ n, nthReduction α S n := by
  refine' subset_antisymm _ _
  · rintro c ⟨d, hdS, hd⟩
    obtain ⟨l, hl, rfl⟩ := List.exists_chain_of_relationReflTransGen hd
    rw [mem_iUnion]
    refine' ⟨l.length, _⟩
    rw [mem_nthReduction_iff]
    refine' ⟨l, hl, rfl, hdS⟩
  · intro c hc
    rw [mem_iUnion] at hc
    obtain ⟨i, hc⟩ := hc
    rw [mem_nthReduction_iff] at hc
    obtain ⟨l, hl₁, _hl₂, hl₃⟩ := hc
    exact
      ⟨(c::l).getLast (List.cons_ne_nil _ _), hl₃,
        List.relationReflTransGen_of_exists_chain l hl₁ rfl⟩

theorem reduction_small' {S : Set (SupportCondition β)} (h : Small S) :
    Small {c | ∃ d ∈ S, c ≤[α] d} := by
  rw [reduction_eq_iUnion]
  have : Small (⋃ n : ULift ℕ, nthReduction α S n.down)
  · refine' small_iUnion _ fun _ => small_nthReduction α h
    rw [Cardinal.mk_denumerable]
    exact Λ_isLimit.aleph0_le.trans_lt Λ_lt_κ
  convert this using 1
  ext x : 1
  simp only [mem_iUnion, ULift.exists]

theorem reduction_small'' {S : Set (SupportCondition β)} (h : Small S) :
    Small {c | ∃ d ∈ S, c <[α] d} :=
  by
  refine' lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset _) (reduction_small' α h)
  rintro c ⟨d, hd₁, hd₂⟩
  exact ⟨d, hd₁, hd₂.to_reflTransGen⟩

theorem reduction_small {S : Set (SupportCondition β)} (h : Small S) : Small (reduction α S) :=
  lt_of_le_of_lt (Cardinal.mk_subtype_le_of_subset fun _c hc => hc.1) (reduction_small' α h)

theorem reduction_designatedSupport_supports [TangleData β] (t : Tangle β) :
    Supports (Allowable β) (reduction α (designatedSupport t : Set (SupportCondition β))) t := by
  intro π h₁
  refine' (designatedSupport t).supports π _
  rintro ⟨a | N, B⟩ h₂
  · exact h₁ (mem_reduction_of_reduced α _ _ (Reduced.mkAtom a B) h₂)
  · by_cases N.IsLitter
    · obtain ⟨L, rfl⟩ := h.exists_litter_eq
      exact h₁ (mem_reduction_of_reduced α _ _ (Reduced.mkLitter L B) h₂)
    · have h := NearLitter.not_isLitter h
      have h₃ :=
        congr_arg Prod.fst
          (h₁
            (mem_reduction_of_reduced_constrains α _ _ _ (Reduced.mkLitter N.fst B)
              (Constrains.nearLitter N h B) h₂))
      have h₄ := fun a ha =>
        congr_arg Prod.fst
          (h₁
            (mem_reduction_of_reduced_constrains α _ _ _ (Reduced.mkAtom a B)
              (Constrains.symmDiff N a ha B) h₂))
      refine' Prod.ext _ rfl
      change inr _ = inr _ at h₃
      change ∀ a ha, inl _ = inl _ at h₄
      change inr _ = inr _
      simp only [inr.injEq, inl.injEq] at h₃ h₄ ⊢
      refine' SetLike.coe_injective _
      refine' (NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul _ N).trans _
      rw [h₃]
      refine' Eq.trans _ (symmDiff_symmDiff_cancel_left (litterSet N.fst) _)
      refine' congr_arg _ _
      ext a : 1
      constructor
      · rintro ⟨b, hb, rfl⟩
        dsimp only
        rw [h₄ b hb]
        exact hb
      · intro ha
        refine' ⟨a, ha, _⟩
        exact h₄ a ha

noncomputable def reducedSupport [TangleData β] (t : Tangle β) : Support β (Allowable β) t
    where
  carrier := reduction α (designatedSupport t : Set (SupportCondition β))
  small := reduction_small α (designatedSupport t).small
  supports := reduction_designatedSupport_supports α t

theorem mem_reducedSupport_iff [TangleData β] (t : Tangle β) (c : SupportCondition β) :
    c ∈ reducedSupport α t ↔ c ∈ reduction α (designatedSupport t : Set (SupportCondition β)) :=
  Iff.rfl

theorem mem_reduction_designated_support {β γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ)
    (hε : (ε : Λ) < γ) (hδε : δ ≠ ε) (B : Path (β : TypeIndex) γ) (t : Tangle δ)
    (c : SupportCondition δ) (h : c ∈ reducedSupport α t) :
    (c.fst, (B.cons (coe_lt hδ)).comp c.snd) <[α]
      (inr (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
        (B.cons (coe_lt hε)).cons (bot_lt_coe _)) := by
  obtain ⟨⟨d, hd, hcd⟩, _⟩ := h
  refine' Relation.TransGen.tail' _ (Constrains.fuzz hδ hε hδε B t d hd)
  exact reflTransGen_constrains_comp hcd _

end ConNF
