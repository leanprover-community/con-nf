import Project.Phase2.Flexible

#align_import phase2.reduction

/-!
# Reductions of supports
-/


universe u

open MulAction Quiver Set Sum WithBot

open scoped Cardinal

namespace ConNf

variable [Params.{u}] (α : Λ) [PositionData] [Phase2Assumptions α]

variable {β : Λ} {G : Type _} {τ : Type _} [SMul G (SupportCondition β)] [SMul G τ]

variable {β G} {x : τ}

/-- A support condition is *reduced* if it is an atom or a litter. -/
@[mk_iff]
inductive Reduced {β : TypeIndex} : SupportCondition β → Prop
  | mk_atom (a : Atom) (B : ExtendedIndex β) : reduced (inl a, B)
  | mk_litter (L : Litter) (B : ExtendedIndex β) : reduced (inr L.toNearLitter, B)

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
  | n + 1 => {c | ∃ d, d ∈ nth_reduction n ∧ c ≺[α] d}

theorem small_nthReduction {S : Set (SupportCondition β)} {n : ℕ} (h : Small S) :
    Small (nthReduction α S n) := by
  induction' n with n hn
  exact h
  rw [nth_reduction]
  simp_rw [← exists_prop, Subtype.exists', set_of_exists]
  refine' small_Union hn _
  rintro ⟨c, hc⟩
  exact small_constrains c

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_nthReduction_iff {S : Set (SupportCondition β)} {n : ℕ} {c : SupportCondition β} :
    c ∈ nthReduction α S n ↔
      ∃ l,
        List.Chain (Constrains α β) c l ∧
          l.length = n ∧ (c::l).getLast (List.cons_ne_nil _ _) ∈ S :=
  by
  induction' n with n hn generalizing c
  · rw [nth_reduction]
    constructor
    · intro h
      exact ⟨[], List.Chain.nil, rfl, h⟩
    · rintro ⟨l, h₁, h₂, h₃⟩
      rw [List.length_eq_zero] at h₂ 
      cases h₂
      exact h₃
  · simp only [nth_reduction, mem_set_of_eq]
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

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem reduction_eq_iUnion {S : Set (SupportCondition β)} :
    {c | ∃ d ∈ S, c ≤[α] d} = ⋃ n, nthReduction α S n :=
  by
  refine' subset_antisymm _ _
  · rintro c ⟨d, hdS, hd⟩
    obtain ⟨l, hl, rfl⟩ := List.exists_chain_of_relationReflTransGen hd
    rw [mem_Union]
    refine' ⟨l.length, _⟩
    rw [mem_nth_reduction_iff]
    refine' ⟨l, hl, rfl, hdS⟩
  · intro c hc
    rw [mem_Union] at hc 
    obtain ⟨i, hc⟩ := hc
    rw [mem_nth_reduction_iff] at hc 
    obtain ⟨l, hl₁, hl₂, hl₃⟩ := hc
    exact
      ⟨(c::l).getLast (List.cons_ne_nil _ _), hl₃,
        List.relationReflTransGen_of_exists_chain l hl₁ rfl⟩

theorem reduction_small' {S : Set (SupportCondition β)} (h : Small S) :
    Small {c | ∃ d ∈ S, c ≤[α] d} := by
  rw [reduction_eq_Union]
  have : Small (⋃ n : ULift ℕ, nth_reduction α S n.down) :=
    by
    refine' small_Union _ fun _ => small_nth_reduction α h
    rw [Cardinal.mk_denumerable]
    exact Λ_limit.aleph_0_le.trans_lt Λ_lt_κ
  · convert this using 1
    ext x : 1
    simp only [mem_Union, ULift.exists]

theorem reduction_small'' {S : Set (SupportCondition β)} (h : Small S) :
    Small {c | ∃ d ∈ S, c <[α] d} :=
  by
  refine' lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset _) (reduction_small' α h)
  rintro c ⟨d, hd₁, hd₂⟩
  exact ⟨d, hd₁, hd₂.to_refl⟩

theorem reduction_small {S : Set (SupportCondition β)} (h : Small S) : Small (reduction α S) :=
  lt_of_le_of_lt (Cardinal.mk_subtype_le_of_subset fun c hc => hc.1) (reduction_small' α h)

theorem reduction_designatedSupport_supports [CoreTangleData β] (t : Tangle β) :
    Supports (Allowable β) (reduction α (designatedSupport t : Set (SupportCondition β))) t :=
  by
  intro π h₁
  refine' (designated_support t).Supports π _
  rintro ⟨a | N, B⟩ h₂
  · exact h₁ (mem_reduction_of_reduced α _ _ (reduced.mk_atom a B) h₂)
  · by_cases N.is_litter
    · obtain ⟨L, rfl⟩ := h.exists_litter_eq
      exact h₁ (mem_reduction_of_reduced α _ _ (reduced.mk_litter L B) h₂)
    · have h := near_litter.not_is_litter h
      have h₃ :=
        congr_arg Prod.fst
          (h₁
            (mem_reduction_of_reduced_constrains α _ _ _ (reduced.mk_litter N.fst B)
              (constrains.near_litter N h B) h₂))
      have h₄ := fun a ha =>
        congr_arg Prod.fst
          (h₁
            (mem_reduction_of_reduced_constrains α _ _ _ (reduced.mk_atom a B)
              (constrains.symm_diff N a ha B) h₂))
      refine' Prod.ext _ rfl
      change inr _ = inr _ at h₃ 
      change ∀ a ha, inl _ = inl _ at h₄ 
      change inr _ = inr _
      simp only at h₃ h₄ ⊢
      apply_fun SetLike.coe at h₃ 
      refine' SetLike.coe_injective _
      refine' (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ N).trans _
      change _ • (_ : Set atom) = _ at h₃ 
      simp only [struct_perm.to_near_litter_perm_smul_set, h₃]
      refine' Eq.trans _ (symmDiff_symmDiff_cancel_left (litter_set N.fst) _)
      refine' congr_arg _ _
      ext a : 1
      constructor
      · rintro ⟨b, hb, rfl⟩
        rw [h₄ b hb]
        exact hb
      · intro ha
        refine' ⟨a, ha, _⟩
        exact h₄ a ha

noncomputable def reducedSupport [CoreTangleData β] (t : Tangle β) : Support β (Allowable β) t
    where
  carrier := reduction α (designatedSupport t : Set (SupportCondition β))
  Small := reduction_small α (designatedSupport t).Small
  Supports := reduction_designatedSupport_supports α t

theorem mem_reducedSupport_iff [CoreTangleData β] (t : Tangle β) (c : SupportCondition β) :
    c ∈ reducedSupport α t ↔ c ∈ reduction α (designatedSupport t : Set (SupportCondition β)) :=
  Iff.rfl

theorem mem_reduction_designated_support {β γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ)
    (hε : (ε : Λ) < γ) (hδε : δ ≠ ε) (B : Path (β : TypeIndex) γ) (t : Tangle δ)
    (c : SupportCondition δ) (h : c ∈ reducedSupport α t) :
    (c.fst, (B.cons (coe_lt hδ)).comp c.snd) <[α]
      (inr (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
        (B.cons (coe_lt hε)).cons (bot_lt_coe _)) :=
  by
  obtain ⟨⟨d, hd, hcd⟩, hc⟩ := h
  refine' Relation.TransGen.tail' _ (constrains.f_map hδ hε hδε B t d hd)
  exact refl_trans_gen_constrains_comp hcd _

end ConNf

