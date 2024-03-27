import ConNF.FOA.Basic.Constrains

/-!
# Reductions of supports

We say that an address is *reduced* if it is an atom or a litter.
In this file, we show how we can convert a support into an equivalent support where all of its
addresses are reduced.

## Main declarations
* `ConNF.Reduced`: An address is *reduced* if it is an atom or a litter.
* `ConNF.reflTransClosure` and `ConNF.transClosure`: The (reflexive) transitive closure of a set
    of addresses under the constrains relation.
* `ConNF.reduction`: The downward closure of the set under the constrains relation, but we only keep
    reduced conditions.
* `ConNF.reduction_small` and its variants: The reduction of a support is small.
* `ConNF.reducedSupport`: A reduced support for each tangle.
-/

universe u

open MulAction Quiver Set Sum WithBot

open scoped Cardinal Pointwise

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions]
variable {β : Λ} {G : Type _} {τ : Type _} [SMul G (Address β)] [SMul G τ] {x : τ}

/-- An address is *reduced* if it is an atom or a litter. -/
@[mk_iff]
inductive Reduced : Atom ⊕ NearLitter → Prop
  | mkAtom (a : Atom) : Reduced (inl a)
  | mkLitter (L : Litter) : Reduced (inr L.toNearLitter)

theorem isLitter_of_reduced {N : NearLitter} (h : Reduced (inr N)) : N.IsLitter := by
  cases h
  exact NearLitter.IsLitter.mk _

/-- The reflexive transitive closure of a set of addresses. -/
def reflTransClosure (S : Set (Address β)) : Set (Address β) :=
  {c | ∃ d ∈ S, c ≤ d}

theorem mem_reflTransClosure_of_mem (S : Set (Address β)) (c : Address β)
    (hc : c ∈ S) : c ∈ reflTransClosure S :=
  ⟨c, hc, Relation.ReflTransGen.refl⟩

/-- The transitive closure of a set of addresses. -/
def transClosure (S : Set (Address β)) : Set (Address β) :=
  {c | ∃ d ∈ S, c < d}

/-- The *reduction* of a set of addresses is the downward closure of the set under
the constrains relation, but we only keep reduced conditions. -/
def reduction (S : Set (Address β)) : Set (Address β) :=
  reflTransClosure S ∩ {c | Reduced c.value}

theorem mem_reduction_of_reduced (S : Set (Address β)) (c : Address β)
    (hc₁ : Reduced c.value) (hc₂ : c ∈ S) : c ∈ reduction S :=
  ⟨mem_reflTransClosure_of_mem S c hc₂, hc₁⟩

theorem mem_reduction_of_reduced_constrains (S : Set (Address β))
    (c d : Address β) (hc : Reduced c.value) (hcd : c ≺ d) (hd : d ∈ S) :
    c ∈ reduction S :=
  ⟨⟨d, hd, Relation.ReflTransGen.single hcd⟩, hc⟩

/-- Gadget that helps us prove that the `reflTransClosure` of a small set is small. -/
def nthClosure (S : Set (Address β)) : ℕ → Set (Address β)
  | 0 => S
  | n + 1 => {c | ∃ d, d ∈ nthClosure S n ∧ c ≺ d}

/-- The `nthClosure` of a small set is small. -/
theorem small_nthReduction {S : Set (Address β)} {n : ℕ} (h : Small S) :
    Small (nthClosure S n) := by
  induction' n with n hn
  exact h
  rw [nthClosure]
  simp_rw [← exists_prop, Subtype.exists', setOf_exists]
  refine' small_iUnion hn _
  rintro ⟨c, _⟩
  exact small_constrains c

theorem mem_nthClosure_iff {S : Set (Address β)} {n : ℕ} {c : Address β} :
    c ∈ nthClosure S n ↔
      ∃ l, List.Chain (· ≺ ·) c l ∧
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
theorem reflTransClosure_eq_iUnion_nthClosure {S : Set (Address β)} :
    reflTransClosure S = ⋃ n, nthClosure S n := by
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
theorem reflTransClosure_small {S : Set (Address β)} (h : Small S) :
    Small (reflTransClosure S) := by
  rw [reflTransClosure_eq_iUnion_nthClosure]
  have : Small (⋃ n : ULift ℕ, nthClosure S n.down)
  · refine' small_iUnion _ fun _ => small_nthReduction h
    rw [Cardinal.mk_denumerable]
    exact aleph0_le_mk_Λ.trans_lt Params.Λ_lt_κ
  convert this using 1
  ext x : 1
  simp only [mem_iUnion, ULift.exists]

/-- The `transClosure` of a small set is small. -/
theorem transClosure_small {S : Set (Address β)} (h : Small S) :
    Small (transClosure S) := by
  refine' lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset _) (reflTransClosure_small h)
  rintro c ⟨d, hd₁, hd₂⟩
  exact ⟨d, hd₁, hd₂.to_reflTransGen⟩

/-- The `reduction` of a small set is small. -/
theorem reduction_small {S : Set (Address β)} (h : Small S) : Small (reduction S) :=
  lt_of_le_of_lt (Cardinal.mk_subtype_le_of_subset fun _c hc => hc.1) (reflTransClosure_small h)

/-- The reduction of a set supports every element in its domain under the action of structural
permutations. -/
theorem reduction_supports (S : Set (Address β)) (c : Address β) (hc : c ∈ S) :
    Supports (StructPerm β) (reduction S) c := by
  intro π hc'
  obtain ⟨B, a | N⟩ := c
  · exact hc' (mem_reduction_of_reduced _ _ (Reduced.mkAtom a) hc)
  by_cases h : N.IsLitter
  · obtain ⟨L, rfl⟩ := h.exists_litter_eq
    exact hc' (mem_reduction_of_reduced _ _ (Reduced.mkLitter L) hc)
  simp only [StructPerm.smul_address_eq_iff, smul_inr, inr.injEq] at hc' ⊢
  have h₃ := hc' (mem_reduction_of_reduced_constrains _ ⟨B, inr N.fst.toNearLitter⟩ _
    (Reduced.mkLitter N.fst) (Constrains.nearLitter B N h) hc)
  have h₄ := fun a ha => hc' (mem_reduction_of_reduced_constrains _ ⟨B, inl a⟩ _
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

end ConNF
