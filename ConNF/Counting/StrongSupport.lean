import ConNF.Counting.Spec

/-!
# Strong supports

A support is called *strong* if, whenever `⟨A, inr N⟩ ∈ S`, we have `⟨A, inr N.1.toNearLitter⟩ ∈ S`.
The main theorem is that if `S, T` are a pair of supports with the same specification, they can be
extended to strong supports which also have the same specification.
-/

open Cardinal Quiver Set Sum WithBot symmDiff

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ}

namespace Support

/-- A support is called *strong* if, whenever `⟨A, inr N⟩ ∈ S`,
we have `⟨A, inr N.1.toNearLitter⟩ ∈ S`. -/
def Strong (S : Support β) : Prop :=
  ∀ A : ExtendedIndex β, ∀ N : NearLitter, ⟨A, inr N⟩ ∈ S → ⟨A, inr N.1.toNearLitter⟩ ∈ S

def strongItems (S : Support β) : Set (SupportCondition β) :=
  {c | ∃ A : ExtendedIndex β, ∃ N : NearLitter, ⟨A, inr N⟩ ∈ S ∧ c = ⟨A, inr N.1.toNearLitter⟩} ∪
  {c | ∃ A : ExtendedIndex β, ∃ N : NearLitter, ⟨A, inr N⟩ ∈ S ∧
    ∃ a : Atom, a ∈ litterSet N.1 ∆ N ∧ c = ⟨A, inl a⟩}

def strongItems' (S : Support β) : Set (SupportCondition β) :=
  ⋃ (A : ExtendedIndex β) (N : NearLitter) (_ : ⟨A, inr N⟩ ∈ S),
  {⟨A, inr N.1.toNearLitter⟩} ∪ ⋃ (a : Atom) (_ : a ∈ litterSet N.1 ∆ N), {⟨A, inl a⟩}

theorem strongItems_eq_strongItems' (S : Support β) : strongItems S = strongItems' S := by
  rw [strongItems, strongItems']
  aesop

theorem strongItems_small (S : Support β) : Small (strongItems S) := by
  rw [strongItems_eq_strongItems', strongItems']
  refine small_iUnion ((mk_extendedIndex β).trans_lt Params.Λ_lt_κ) (fun A => ?_)
  refine Small.bUnion ?_ (fun N _ => ?_)
  · refine S.enum.small.preimage (f := fun N => ⟨A, inr N⟩) ?_
    intro N₁ N₂ hN
    cases hN
    rfl
  · exact Small.union (small_singleton _) (Small.bUnion N.2.prop (fun a _ => small_singleton _))

@[simp]
theorem nearLitter_mem_strongItems_iff (S : Support β) (A : ExtendedIndex β) (N : NearLitter) :
    ⟨A, inr N⟩ ∈ strongItems S ↔ N.IsLitter ∧ ∃ N' : NearLitter, N.1 = N'.1 ∧ ⟨A, inr N'⟩ ∈ S := by
  rw [strongItems]
  constructor
  · simp only [mem_union, mem_setOf_eq, SupportCondition.mk.injEq, inr.injEq, and_false,
      exists_const, or_false]
    rintro ⟨_, N', h, rfl, rfl⟩
    exact ⟨NearLitter.IsLitter.mk _, N', rfl, h⟩
  · rintro ⟨h, N', h₁, h₂⟩
    obtain ⟨L, rfl⟩ := h.exists_litter_eq
    refine Or.inl ⟨A, N', h₂, ?_⟩
    rw [← h₁]
    rfl

def atomsToAdd (S : Support β) (A : ExtendedIndex β) : Set Atom :=
  {a | ∃ N : NearLitter, ⟨A, inr N⟩ ∈ S ∧ a ∈ litterSet N.1 ∆ N}

@[simp]
theorem atom_mem_strongItems_iff {S : Support β} {A : ExtendedIndex β} {a : Atom} :
    ⟨A, inl a⟩ ∈ strongItems S ↔ a ∈ atomsToAdd S A := by
  constructor
  · rintro (⟨_, _, _, h⟩ | ⟨A, N, h₁, a, h₂, h₃⟩)
    · cases h
    · cases h₃
      exact ⟨N, h₁, h₂⟩
  · rintro ⟨N, hN, ha⟩
    exact Or.inr ⟨A, N, hN, a, ha, rfl⟩

theorem strengthen_mem_of_mem_symmDiff (S : Support β) (A : ExtendedIndex β)
    (N₁ N₂ : NearLitter) (a : Atom) (hN : N₁.fst = N₂.fst) (ha : a ∈ (N₁ : Set Atom) ∆ N₂)
    (hN₁ : ⟨A, inr N₁⟩ ∈ (S : Set _) ∪ strongItems S)
    (hN₂ : ⟨A, inr N₂⟩ ∈ (S : Set _) ∪ strongItems S) :
    ⟨A, inl a⟩ ∈ (S : Set _) ∪ strongItems S := by
  simp only [mem_union, nearLitter_mem_strongItems_iff] at hN₁ hN₂
  obtain (hN₁ | ⟨hN₁, N₁, hN₁', _⟩) := hN₁ <;> obtain (hN₂ | ⟨hN₂, N₂, hN₂', _⟩) := hN₂
  · exact Or.inl (S.mem_of_mem_symmDiff A N₁ N₂ a hN ha hN₁ hN₂)
  · obtain ⟨L, rfl⟩ := hN₂.exists_litter_eq
    cases hN₂'
    rw [Litter.toNearLitter_fst] at hN
    rw [← hN, symmDiff_comm] at ha
    exact Or.inr (Or.inr ⟨A, N₁, hN₁, a, ha, rfl⟩)
  · obtain ⟨L, rfl⟩ := hN₁.exists_litter_eq
    cases hN₁'
    rw [Litter.toNearLitter_fst] at hN
    rw [hN] at ha
    exact Or.inr (Or.inr ⟨A, N₂, hN₂, a, ha, rfl⟩)
  · obtain ⟨L₁, rfl⟩ := hN₁.exists_litter_eq
    obtain ⟨L₂, rfl⟩ := hN₂.exists_litter_eq
    cases hN
    simp only [Litter.coe_toNearLitter, symmDiff_self, bot_eq_empty, mem_empty_iff_false] at ha

noncomputable def strengthen (S : Support β) : Support β where
  enum := S.enum + Enumeration.ofSet (strongItems S) (strongItems_small S)
  mem_of_mem_symmDiff' := by
    simp only [Enumeration.mem_add_iff, Enumeration.mem_ofSet_iff]
    exact strengthen_mem_of_mem_symmDiff S

theorem convertIndex
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    {i : κ} (hi : i < S.max) : i < T.max :=
  hT.lt_max (hS.of_lt_max hi)

theorem f_eq_atom_of_specSame
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (A : ExtendedIndex β) (a : Atom) (i : κ) (hi : i < S.max) (hia : S.f i hi = ⟨A, inl a⟩) :
    ∃ a' : Atom, T.f i (convertIndex hS hT hi) = ⟨A, inl a'⟩ := by
  have h₁ := hS.specifies i (hS.of_lt_max hi) hi
  have h₂ := hT.specifies i (hS.of_lt_max hi) (convertIndex hS hT hi)
  rw [hia] at h₁
  rw [Spec.specifiesCondition_atom_right_iff] at h₁
  rw [h₁, Spec.specifiesCondition_atom_left_iff] at h₂
  aesop

theorem f_eq_nearLitter_of_specSame
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (A : ExtendedIndex β) (N : NearLitter) (i : κ) (hi : i < S.max) (hiN : S.f i hi = ⟨A, inr N⟩) :
    ∃ N' : NearLitter, T.f i (convertIndex hS hT hi) = ⟨A, inr N'⟩ := by
  have h₁ := hS.specifies i (hS.of_lt_max hi) hi
  have h₂ := hT.specifies i (hS.of_lt_max hi) (convertIndex hS hT hi)
  rw [hiN] at h₁
  obtain (h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩) := flexible_cases' A N.1
  · rw [Spec.specifiesCondition_flexible_right_iff S A N h] at h₁
    rw [h₁, Spec.specifiesCondition_flexible_left_iff] at h₂
    aesop
  · rw [Spec.specifiesCondition_inflexibleBot_right_iff S A N h] at h₁
    rw [h₁, Spec.specifiesCondition_inflexibleBot_left_iff] at h₂
    aesop
  · rw [Spec.specifiesCondition_inflexibleCoe_right_iff S A N h] at h₁
    obtain ⟨_, _, _, _, h₁⟩ := h₁
    rw [h₁, Spec.specifiesCondition_inflexibleCoe_left_iff] at h₂
    aesop

/-- If `i` is the index of an atom in `S`, get the corresponding atom in `T`.
This is only noncomputable for a silly reason: we can't construct elements of `μ`. -/
noncomputable def convertAtom
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (i : κ) (hi : i < S.max) :
    Atom :=
  match T.f i (convertIndex hS hT hi) with
  | ⟨_, inl a'⟩ => a'
  | ⟨_, inr _⟩ => Classical.arbitrary Atom

/-- If `i` is the index of a near-litter in `S`, get the corresponding near-litter in `T`. -/
noncomputable def convertNearLitter
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (i : κ) (hi : i < S.max) :
    NearLitter :=
  match T.f i (convertIndex hS hT hi) with
  | ⟨_, inl _⟩ => Classical.arbitrary NearLitter
  | ⟨_, inr N'⟩ => N'

theorem convertAtom_eq
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (A : ExtendedIndex β) (a : Atom) (i : κ) (hi : i < S.max) (ha : S.f i hi = ⟨A, inl a⟩) :
    T.f i (convertIndex hS hT hi) = ⟨A, inl (convertAtom hS hT i hi)⟩ := by
  rw [convertAtom]
  obtain ⟨a', ha'⟩ := f_eq_atom_of_specSame hS hT A a i hi ha
  rw [ha']

theorem convertNearLitter_eq
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (A : ExtendedIndex β) (N : NearLitter) (i : κ) (hi : i < S.max) (hN : S.f i hi = ⟨A, inr N⟩) :
    T.f i (convertIndex hS hT hi) = ⟨A, inr (convertNearLitter hS hT i hi)⟩ := by
  rw [convertNearLitter]
  obtain ⟨N', hN'⟩ := f_eq_nearLitter_of_specSame hS hT A N i hi hN
  rw [hN']

/-- A litter that is not allowed to be used as a sandbox because it appears somewhere that
we need to preserve. -/
@[mk_iff]
inductive BannedLitter (T : Support β) (A : ExtendedIndex β) : Litter → Prop
  | atom (a : Atom) : ⟨A, inl a⟩ ∈ T → BannedLitter T A a.1
  | nearLitter (a : Atom) (N : NearLitter) : a ∈ N → ⟨A, inr N⟩ ∈ T → BannedLitter T A a.1

def bannedLitters (T : Support β) (A : ExtendedIndex β) : Set Litter :=
  (⋃ (a : Atom) (_ : ⟨A, inl a⟩ ∈ T), {a.1}) ∪
  (⋃ (N : NearLitter) (_ : ⟨A, inr N⟩ ∈ T), {N.1}) ∪
  (⋃ (N : NearLitter) (_ : ⟨A, inr N⟩ ∈ T)
    (a : Atom) (_ : a ∈ (N : Set Atom) \ litterSet N.1), {a.1})

theorem bannedLitter_iff_mem_bannedLitters (T : Support β) (A : ExtendedIndex β) (L : Litter) :
    BannedLitter T A L ↔ L ∈ bannedLitters T A := by
  simp only [bannedLitter_iff, bannedLitters,
    mem_union, mem_iUnion, Set.mem_singleton_iff, exists_prop]
  constructor
  · rintro (h | ⟨a, N, ha, hN, rfl⟩)
    · exact Or.inl (Or.inl h)
    · by_cases ha' : a ∈ litterSet N.1
      · exact Or.inl (Or.inr ⟨N, hN, ha'⟩)
      · exact Or.inr ⟨N, hN, a, ⟨ha, ha'⟩, rfl⟩
  · rintro ((h | ⟨N, hN, rfl⟩) | ⟨N, hN, a, ha, rfl⟩)
    · exact Or.inl h
    · obtain ⟨a, ha⟩ := NearLitter.inter_nonempty_of_fst_eq_fst
        (N₁ := N.1.toNearLitter) (N₂ := N) rfl
      exact Or.inr ⟨a, N, ha.2, hN, ha.1.symm⟩
    · exact Or.inr ⟨a, N, ha.1, hN, rfl⟩

theorem bannedLitter_small (T : Support β) (A : ExtendedIndex β) :
    Small {L | BannedLitter T A L} := by
  simp only [bannedLitter_iff_mem_bannedLitters]
  refine Small.union (Small.union ?_ ?_) ?_
  · refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine Small.preimage (f := fun a => ⟨A, inl a⟩) ?_ T.small
    intro a₁ a₂ h
    simp only [SupportCondition.mk.injEq, inl.injEq, true_and] at h
    exact h
  · refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine Small.preimage (f := fun N => ⟨A, inr N⟩) ?_ T.small
    intro a₁ a₂ h
    simp only [SupportCondition.mk.injEq, inr.injEq, true_and] at h
    exact h
  · refine Small.bUnion ?_ (fun N _ => Small.bUnion ?_ (fun _ _ => small_singleton _))
    · refine Small.preimage (f := fun N => ⟨A, inr N⟩) ?_ T.small
      intro a₁ a₂ h
      simp only [SupportCondition.mk.injEq, inr.injEq, true_and] at h
      exact h
    · exact Small.mono (Set.subset_union_right _ _) N.2.prop

theorem mk_not_bannedLitter (T : Support β) (A : ExtendedIndex β) :
    #{L | ¬BannedLitter T A L} = #μ := by
  have := mk_sum_compl {L | BannedLitter T A L}
  rw [compl_setOf, mk_litter] at this
  rw [← this, add_eq_right]
  · by_contra h
    have h' := add_le_add (le_of_lt (bannedLitter_small T A)) (le_of_not_le h)
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le Params.κ_lt_μ _
    exact lt_of_le_of_lt Params.κ_isRegular.aleph0_le Params.κ_lt_μ
  · by_contra h
    have h' := add_le_add (le_of_lt (bannedLitter_small T A)) (le_of_not_le h)
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le Params.κ_lt_μ _
    exact lt_trans (bannedLitter_small T A) Params.κ_lt_μ

theorem not_bannedLitter_nonempty (T : Support β) (A : ExtendedIndex β) :
    Nonempty {L | ¬BannedLitter T A L} := by
  simp only [← mk_ne_zero_iff, mk_not_bannedLitter, Ne.def, mk_ne_zero, not_false_iff]

noncomputable def sandboxLitter (T : Support β) (A : ExtendedIndex β) : Litter :=
  (not_bannedLitter_nonempty T A).some

theorem sandboxLitter_not_banned (T : Support β) (A : ExtendedIndex β) :
    ¬BannedLitter T A (sandboxLitter T A) :=
  (not_bannedLitter_nonempty T A).some.2

theorem atomsToAdd_small (S : Support β) (A : ExtendedIndex β) : Small (atomsToAdd S A) := by
  refine Small.image_subset (fun a => ⟨A, inl a⟩) ?_ (strongItems_small S) ?_
  · intro a₁ a₂ h
    simp only [SupportCondition.mk.injEq, inl.injEq, true_and] at h
    exact h
  · rintro _ ⟨a, ha, rfl⟩
    rw [atom_mem_strongItems_iff]
    exact ha

theorem exists_atomsToAddEmbedding (S T : Support β) (A : ExtendedIndex β) :
    Nonempty (atomsToAdd S A ↪ litterSet (sandboxLitter T A)) := by
  rw [← Cardinal.le_def, mk_litterSet]
  exact (atomsToAdd_small S A).le

noncomputable def atomsToAddEmbedding (S T : Support β) (A : ExtendedIndex β) :
    atomsToAdd S A ↪ litterSet (sandboxLitter T A) :=
  (exists_atomsToAddEmbedding S T A).some

open scoped Classical in
noncomputable def strengthenImageAtom
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (A : ExtendedIndex β) (a : Atom) : Atom :=
  if h : ∃ (i : κ) (hi : i < S.max), S.f i hi = ⟨A, inl a⟩ then
    convertAtom hS hT h.choose h.choose_spec.choose
  else if h : a ∈ atomsToAdd S A then
    atomsToAddEmbedding S T A ⟨a, h⟩
  else
    Classical.arbitrary Atom

/-- Assuming that `S.f i hi = ⟨A, inr N⟩`, calculate the corresponding value of
`⟨A, inr N.1.toNearLitter⟩` in `T`. -/
noncomputable def strengthenImageLitter
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (A : ExtendedIndex β) (N : NearLitter) (i : κ) (hi : i < S.max) :
    NearLitter :=
  ⟨(convertNearLitter hS hT i hi).1,
    convertNearLitter hS hT i hi ∆ (strengthenImageAtom hS hT A '' litterSet N.1 ∆ N),
    by
      rw [IsNearLitter, IsNear, ← symmDiff_assoc]
      exact Small.symmDiff (convertNearLitter hS hT i hi).2.prop (Small.image N.2.prop)⟩

noncomputable def nearLitter_mem_strongItems_index
    {S : Support β} {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ strongItems S) : κ :=
  ((nearLitter_mem_strongItems_iff _ _ _).mp h).2.choose_spec.2.choose

theorem nearLitter_mem_strongItems_index_lt
    {S : Support β} {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ strongItems S) :
    nearLitter_mem_strongItems_index h < S.max :=
  ((nearLitter_mem_strongItems_iff _ _ _).mp h).2.choose_spec.2.choose_spec.choose

theorem nearLitter_mem_strongItems_index_spec
    {S : Support β} {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ strongItems S) :
    ∃ N' : NearLitter,
    S.f (nearLitter_mem_strongItems_index h) (nearLitter_mem_strongItems_index_lt h) =
      ⟨A, inr N'⟩ :=
  ⟨_, ((nearLitter_mem_strongItems_iff _ _ _).mp h).2.choose_spec.2.choose_spec.choose_spec.symm⟩

noncomputable def strengthenImageCondition
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T) :
    (c : SupportCondition β) → c ∈ strongItems S → SupportCondition β
  | ⟨A, inl a⟩, _ => ⟨A, inl (strengthenImageAtom hS hT A a)⟩
  | ⟨A, inr N⟩, h => ⟨A, inr (strengthenImageLitter hS hT A N
      (nearLitter_mem_strongItems_index h) (nearLitter_mem_strongItems_index_lt h))⟩

noncomputable def strengthenImage
    {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)
    (i : κ) (hi : i < S.strengthen.max) : SupportCondition β :=
  if hi' : i < S.max then
    T.f i (convertIndex hS hT hi')
  else
    strengthenImageCondition hS hT
      ((Enumeration.ofSet (strongItems S) (strongItems_small S)).f
        (i - S.max) (κ_sub_lt hi (le_of_not_lt hi')))
      (by rw [← Enumeration.mem_ofSet_iff]; exact ⟨_, _, rfl⟩)

end Support

end ConNF
