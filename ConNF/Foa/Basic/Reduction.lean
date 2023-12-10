import ConNF.Foa.Basic.Constrains

/-!
# Reductions of supports

We say that a support condition is *reduced* if it is an atom or a litter.
In this file, we show how we can convert a support into an equivalent support where all of its
support conditions are reduced.

## Main declarations
* `ConNF.Reduced`: A support condition is *reduced* if it is an atom or a litter.
* `ConNF.reflTransClosure` and `ConNF.transClosure`: The (reflexive) transitive closure of a set
    of support conditions under the constrains relation.
* `ConNF.reduction`: The downward closure of the set under the constrains relation, but we only keep
    reduced conditions.
* `ConNF.reduction_small` and its variants: The reduction of a support is small.
* `ConNF.reducedSupport`: A reduced support for each tangle.
-/

universe u

open MulAction Quiver Set Sum WithBot

open scoped Cardinal Pointwise

namespace ConNF

variable [Params.{u}] (α : Λ) [BasePositions] [FoaAssumptions α]
variable {β : Λ} {G : Type _} {τ : Type _} [SMul G (SupportCondition β)] [SMul G τ] {x : τ}

/-- A support condition is *reduced* if it is an atom or a litter. -/
@[mk_iff]
inductive Reduced : Atom ⊕ NearLitter → Prop
  | mkAtom (a : Atom) : Reduced (inl a)
  | mkLitter (L : Litter) : Reduced (inr L.toNearLitter)

theorem isLitter_of_reduced {N : NearLitter} (h : Reduced (inr N)) : N.IsLitter := by
  cases h
  exact NearLitter.IsLitter.mk _

/-- The reflexive transitive closure of a set of support conditions. -/
def reflTransClosure (S : Set (SupportCondition β)) : Set (SupportCondition β) :=
  {c | ∃ d ∈ S, c ≤[α] d}

theorem mem_reflTransClosure_of_mem (S : Set (SupportCondition β)) (c : SupportCondition β)
    (hc : c ∈ S) : c ∈ reflTransClosure α S :=
  ⟨c, hc, Relation.ReflTransGen.refl⟩

/-- The transitive closure of a set of support conditions. -/
def transClosure (S : Set (SupportCondition β)) : Set (SupportCondition β) :=
  {c | ∃ d ∈ S, c <[α] d}

/-- The *reduction* of a set of support conditions is the downward closure of the set under
the constrains relation, but we only keep reduced conditions. -/
def reduction (S : Set (SupportCondition β)) : Set (SupportCondition β) :=
  reflTransClosure α S ∩ {c | Reduced c.value}

theorem mem_reduction_of_reduced (S : Set (SupportCondition β)) (c : SupportCondition β)
    (hc₁ : Reduced c.value) (hc₂ : c ∈ S) : c ∈ reduction α S :=
  ⟨mem_reflTransClosure_of_mem α S c hc₂, hc₁⟩

theorem mem_reduction_of_reduced_constrains (S : Set (SupportCondition β))
    (c d : SupportCondition β) (hc : Reduced c.value) (hcd : c ≺ d) (hd : d ∈ S) :
    c ∈ reduction α S :=
  ⟨⟨d, hd, Relation.ReflTransGen.single hcd⟩, hc⟩

/-- Gadget that helps us prove that the `reflTransClosure` of a small set is small. -/
def nthClosure (S : Set (SupportCondition β)) : ℕ → Set (SupportCondition β)
  | 0 => S
  | n + 1 => {c | ∃ d, d ∈ nthClosure S n ∧ c ≺ d}

/-- The `nthClosure` of a small set is small. -/
theorem small_nthReduction {S : Set (SupportCondition β)} {n : ℕ} (h : Small S) :
    Small (nthClosure α S n) := by
  induction' n with n hn
  exact h
  rw [nthClosure]
  simp_rw [← exists_prop, Subtype.exists', setOf_exists]
  refine' small_iUnion hn _
  rintro ⟨c, _⟩
  exact small_constrains c

theorem mem_nthClosure_iff {S : Set (SupportCondition β)} {n : ℕ} {c : SupportCondition β} :
    c ∈ nthClosure α S n ↔
      ∃ l, List.Chain (Constrains α β) c l ∧
        l.length = n ∧ (c::l).getLast (List.cons_ne_nil _ _) ∈ S := by
  induction' n with n hn generalizing c
  · rw [nthClosure]
    constructor
    · intro h
      exact ⟨[], List.Chain.nil, rfl, h⟩
    · rintro ⟨l, h₁, h₂, h₃⟩
      rw [List.length_eq_zero] at h₂
      cases h₂
      exact h₃
  · simp only [nthClosure, mem_setOf_eq]
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

/-- The `reflTransClosure` of a set is the `ℕ`-indexed union of the `n`th closures. -/
theorem reflTransClosure_eq_iUnion_nthClosure {S : Set (SupportCondition β)} :
    reflTransClosure α S = ⋃ n, nthClosure α S n := by
  refine' subset_antisymm _ _
  · rintro c ⟨d, hdS, hd⟩
    obtain ⟨l, hl, rfl⟩ := List.exists_chain_of_relationReflTransGen hd
    rw [mem_iUnion]
    refine' ⟨l.length, _⟩
    rw [mem_nthClosure_iff]
    refine' ⟨l, hl, rfl, hdS⟩
  · intro c hc
    rw [mem_iUnion] at hc
    obtain ⟨i, hc⟩ := hc
    rw [mem_nthClosure_iff] at hc
    obtain ⟨l, hl₁, _hl₂, hl₃⟩ := hc
    exact
      ⟨(c::l).getLast (List.cons_ne_nil _ _), hl₃,
        List.relationReflTransGen_of_exists_chain l hl₁ rfl⟩

/-- The `reflTransClosure` of a small set is small. -/
theorem reflTransClosure_small {S : Set (SupportCondition β)} (h : Small S) :
    Small (reflTransClosure α S) := by
  rw [reflTransClosure_eq_iUnion_nthClosure]
  have : Small (⋃ n : ULift ℕ, nthClosure α S n.down)
  · refine' small_iUnion _ fun _ => small_nthReduction α h
    rw [Cardinal.mk_denumerable]
    exact aleph0_le_mk_Λ.trans_lt Λ_lt_κ
  convert this using 1
  ext x : 1
  simp only [mem_iUnion, ULift.exists]

/-- The `transClosure` of a small set is small. -/
theorem transClosure_small {S : Set (SupportCondition β)} (h : Small S) :
    Small (transClosure α S) := by
  refine' lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset _) (reflTransClosure_small α h)
  rintro c ⟨d, hd₁, hd₂⟩
  exact ⟨d, hd₁, hd₂.to_reflTransGen⟩

/-- The `reduction` of a small set is small. -/
theorem reduction_small {S : Set (SupportCondition β)} (h : Small S) : Small (reduction α S) :=
  lt_of_le_of_lt (Cardinal.mk_subtype_le_of_subset fun _c hc => hc.1) (reflTransClosure_small α h)

/-- The reduction of a set supports every element in its domain under the action of structural
permutations. -/
theorem reduction_supports (S : Set (SupportCondition β)) (c : SupportCondition β) (hc : c ∈ S) :
    Supports (StructPerm β) (reduction α S) c := by
  intro π hc'
  obtain ⟨B, a | N⟩ := c
  · exact hc' (mem_reduction_of_reduced α _ _ (Reduced.mkAtom a) hc)
  by_cases h : N.IsLitter
  · obtain ⟨L, rfl⟩ := h.exists_litter_eq
    exact hc' (mem_reduction_of_reduced α _ _ (Reduced.mkLitter L) hc)
  simp only [StructPerm.smul_supportCondition_eq_iff, smul_inr, inr.injEq] at hc' ⊢
  have h₃ := hc' (mem_reduction_of_reduced_constrains α _ ⟨B, inr N.fst.toNearLitter⟩ _
    (Reduced.mkLitter N.fst) (Constrains.nearLitter B N h) hc)
  have h₄ := fun a ha => hc' (mem_reduction_of_reduced_constrains α _ ⟨B, inl a⟩ _
    (Reduced.mkAtom a) (Constrains.symmDiff B N a ha) hc)
  simp only [smul_inr, inr.injEq, smul_inl, inl.injEq] at h₃ h₄
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

theorem reduction_designatedSupport_supports [TangleData β] (t : Tangle β) :
    Supports (Allowable β) (reduction α (designatedSupport t : Set (SupportCondition β))) t := by
  intro ρ h
  refine (designatedSupport t).supports ρ ?_
  intros c hc'
  exact reduction_supports α (designatedSupport t) c hc' (Allowable.toStructPerm ρ) h

/-- A support for a tangle containing only reduced support conditions. -/
noncomputable def reducedSupport [TangleData β] (t : Tangle β) : Support β (Allowable β) t
    where
  carrier := reduction α (designatedSupport t : Set (SupportCondition β))
  small := reduction_small α (designatedSupport t).small
  supports := reduction_designatedSupport_supports α t

theorem mem_reducedSupport_iff [TangleData β] (t : Tangle β) (c : SupportCondition β) :
    c ∈ reducedSupport α t ↔ c ∈ reduction α (designatedSupport t : Set (SupportCondition β)) :=
  Iff.rfl

theorem transConstrains_of_mem_reducedSupport {β γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ)
    (hε : (ε : Λ) < γ) (hδε : δ ≠ ε) (B : Path (β : TypeIndex) γ) (t : Tangle δ)
    (c : SupportCondition δ) (h : c ∈ reducedSupport α t) :
    ⟨(B.cons (coe_lt hδ)).comp c.path, c.value⟩ <[α]
      ⟨(B.cons (coe_lt hε)).cons (bot_lt_coe _),
        inr (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter⟩ := by
  obtain ⟨⟨d, hd, hcd⟩, _⟩ := h
  refine' Relation.TransGen.tail' _ (Constrains.fuzz hδ hε hδε B t d hd)
  exact reflTransConstrains_comp hcd _

theorem pos_lt_of_mem_reducedSupport {β γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ)
    (hε : (ε : Λ) < γ) (hδε : δ ≠ ε) (B : Path (β : TypeIndex) γ) (t : Tangle δ)
    (c : SupportCondition δ) (h : c ∈ reducedSupport α t) :
    pos c.value < pos (fuzz (coe_ne_coe.mpr <| coe_ne' hδε) t) :=
  transConstrains_subrelation β (transConstrains_of_mem_reducedSupport α hδ hε hδε B t c h)

end ConNF
