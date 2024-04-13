import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Mathlib.Order.RelClasses
import ConNF.Fuzz.Construction

open Cardinal Sum

open scoped Cardinal symmDiff

universe u

namespace ConNF.MainInduction

variable [Params.{u}]

noncomputable def litterEquiv : Litter ≃ μ :=
  (Cardinal.eq.mp mk_litter).some

noncomputable def nearLitterEquiv : NearLitter ≃ μ :=
  (Cardinal.eq.mp mk_nearLitter).some

noncomputable def alMap : Atom ⊕ Litter → μ ×ₗ (Unit ⊕ₗ κ)
  | inl a => (litterEquiv a.1, inr a.2)
  | inr L => (litterEquiv L, inl ())

def posBound (N : NearLitter) : Set (μ ×ₗ (Unit ⊕ₗ κ)) :=
  {ν | ¬N.IsLitter ∧ ν = alMap (inr N.1)} ∪
  {ν | ∃ a ∈ litterSet N.1 ∆ N, ν = alMap (inl a)}

def posBound' (N : NearLitter) : Set (μ ×ₗ (Unit ⊕ₗ κ)) :=
  {ν | ¬N.IsLitter ∧ ν = alMap (inr N.1)} ∪
  ⋃ (a ∈ litterSet N.1 ∆ N), {alMap (inl a)}

theorem posBound_eq_posBound' (N : NearLitter) : posBound N = posBound' N := by
  unfold posBound posBound'
  aesop

def posDeny (N : NearLitter) : Set (μ ×ₗ (Unit ⊕ₗ κ)) :=
  {ν | ∃ ν' ∈ posBound N, ν ≤ ν'}

theorem small_posBound (N : NearLitter) : Small (posBound N) := by
  rw [posBound_eq_posBound']
  refine Small.union ?_ (Small.bUnion N.2.prop (fun _ _ => small_singleton _))
  refine Set.Subsingleton.small ?_
  intro x₁ h₁ x₂ h₂
  cases h₁.2
  cases h₂.2
  rfl

section Instances

variable {α β : Type _} [LinearOrder α] [LinearOrder β]
  [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)]

instance : IsWellFounded (α ⊕ₗ β) (· < ·) :=
  ⟨Sum.lex_wf (inferInstanceAs (IsWellFounded _ _)).wf (inferInstanceAs (IsWellFounded _ _)).wf⟩

instance : IsWellOrder (α ×ₗ β) (· < ·) := instIsWellOrderProdLex
instance : IsWellOrder (α ⊕ₗ β) (· < ·) := ⟨⟩

end Instances

section μProd

variable {α : Type u} [LinearOrder α] [IsWellOrder α (· < ·)] (hα : #α < #μ) (hα' : #α ≠ 0)

instance μProdWO : IsWellOrder (μ ×ₗ α) (· < ·) := inferInstance

@[simp]
theorem mk_μProd : #(μ ×ₗ α) = #μ := by
  change #(μ × α) = #μ
  simp only [mk_prod, lift_id]
  refine le_antisymm ?_ ?_
  · exact mul_le_of_le le_rfl hα.le Params.μ_isStrongLimit.isLimit.aleph0_le
  · exact Cardinal.le_mul_right hα'

theorem μProd_fst_le {y x : μ ×ₗ α} (h : y < x) : y.1 ≤ x.1 := by
  cases h
  exact le_of_lt ‹_›
  rfl

theorem μProd_card_iio (x : μ ×ₗ α) : #{y | y < x} < #μ := by
  have : {y | y < x} ⊆ ⋃ (ν ≤ x.1), {y | y.1 = ν}
  · intro y hy
    exact ⟨_, ⟨y.1, rfl⟩, _, ⟨μProd_fst_le hy, rfl⟩, rfl⟩
  refine (mk_subtype_le_of_subset this).trans_lt ?_
  refine (mk_biUnion_le _ _).trans_lt ?_
  refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le (card_Iic_lt _) ?_
  refine (ciSup_le' (a := #α) (fun _ => ?_)).trans_lt hα
  refine mk_le_of_injective (f := fun y => y.val.2) ?_
  rintro ⟨⟨a₁, b₁⟩, h₁⟩ ⟨⟨a₂, b₂⟩, h₂⟩ h
  cases h₁
  cases h₂
  cases h
  rfl

theorem μProd_typein_lt (x : μ ×ₗ α) :
    Ordinal.typein (α := μ ×ₗ α) (· < ·) x < Ordinal.type (α := μ) (· < ·) := by
  rw [Params.μ_ord, Cardinal.lt_ord]
  exact μProd_card_iio hα x

theorem μProd_typein_lt' (x : μ) :
    Ordinal.typein (α := μ) (· < ·) x < Ordinal.type (α := μ ×ₗ α) (· < ·) := by
  refine (Ordinal.typein_lt_type (α := μ) (· < ·) x).trans_le ?_
  rw [Params.μ_ord]
  by_contra! h
  rw [Cardinal.lt_ord] at h
  change #(μ ×ₗ α) < #μ at h
  simp only [mk_μProd hα hα', lt_self_iff_false] at h

noncomputable def μProd_toFun (x : μ ×ₗ α) : μ :=
  Ordinal.enum (· < ·) (Ordinal.typein (α := μ ×ₗ α) (· < ·) x) (μProd_typein_lt hα x)

noncomputable def μProd_invFun (x : μ) : μ ×ₗ α :=
  Ordinal.enum (· < ·) (Ordinal.typein (α := μ) (· < ·) x) (μProd_typein_lt' hα hα' x)

noncomputable def μProd_equiv : μ ×ₗ α ≃o μ where
  toFun := μProd_toFun hα
  invFun := μProd_invFun hα hα'
  left_inv := by
    unfold μProd_invFun μProd_toFun
    intro x
    simp only [Ordinal.typein_enum, Ordinal.enum_typein]
  right_inv := by
    unfold μProd_invFun μProd_toFun
    intro x
    simp only [Ordinal.typein_enum, Ordinal.enum_typein]
  map_rel_iff' := by
    unfold μProd_invFun μProd_toFun
    intro x y
    simp only [Equiv.coe_fn_mk]
    have := Ordinal.enum_le_enum (α := μ) (· < ·) (μProd_typein_lt hα x) (μProd_typein_lt hα y)
    simp only [not_lt, Ordinal.typein_le_typein] at this
    exact this

theorem μProd_type : Ordinal.type (α := μ ×ₗ α) (· < ·) = (#μ).ord := by
  rw [← Params.μ_ord, Ordinal.type_eq]
  exact ⟨(μProd_equiv hα hα').toRelIsoLT⟩

theorem card_Iio_lt' (x : μ ×ₗ α) : #(Set.Iio x) < #μ := by
  have := card_typein_lt (α := μ ×ₗ α) (· < ·) x ?_
  · rw [mk_μProd hα hα'] at this
    exact this
  · rw [mk_μProd hα hα', μProd_type hα hα']

theorem card_Iic_lt' (x : μ ×ₗ α) : #(Set.Iic x) < #μ := by
  rw [← Set.Iio_union_right, mk_union_of_disjoint, mk_singleton]
  · exact (add_one_le_succ _).trans_lt (Params.μ_isStrongLimit.isLimit.succ_lt
      (card_Iio_lt' hα hα' x))
  · simp

end μProd

theorem unitSum_lt : #(Unit ⊕ₗ κ) < #μ := by
  change #(Unit ⊕ κ) < #μ
  simp only [mk_sum, mk_fintype, Fintype.card_ofSubsingleton, Nat.cast_one, lift_one, lift_id']
  refine add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ Params.κ_lt_μ
  exact one_lt_aleph0.trans_le Params.μ_isStrongLimit.isLimit.aleph0_le

theorem unitSum_ne_zero : #(Unit ⊕ₗ κ) ≠ 0 := by
  simp only [ne_eq, mk_ne_zero, not_false_eq_true]

theorem mk_posDeny (N : NearLitter) : #(posDeny N) < #μ := by
  have := (small_posBound N).trans_le Params.κ_le_μ_ord_cof
  rw [← μProd_type unitSum_lt unitSum_ne_zero] at this
  obtain ⟨ν, hν⟩ := Ordinal.lt_cof_type this
  refine (Cardinal.mk_subtype_le_of_subset ?_).trans_lt (card_Iic_lt' unitSum_lt unitSum_ne_zero ν)
  rintro ν₁ ⟨ν₂, hν₂, hν₁⟩
  exact hν₁.trans (hν ν₂ hν₂).le

instance isWellOrder : IsWellOrder NearLitter (InvImage (· < ·) nearLitterEquiv) :=
  isWellOrder_invImage inferInstance _ nearLitterEquiv.injective

theorem isWellOrder_type_eq :
    letI := isWellOrder
    Ordinal.type (InvImage (· < ·) nearLitterEquiv) = (#μ).ord := by
  rw [← Params.μ_ord, Ordinal.type_eq]
  refine ⟨⟨nearLitterEquiv, ?_⟩⟩
  intros
  rfl

theorem mk_posDeny' (N : NearLitter) :
    #{ N' // nearLitterEquiv N' < nearLitterEquiv N } + #(posDeny N) < #(μ ×ₗ (Unit ⊕ₗ κ)) := by
  rw [mk_μProd unitSum_lt unitSum_ne_zero]
  refine add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ (mk_posDeny N)
  letI := isWellOrder
  have := Ordinal.typein_lt_type (InvImage (· < ·) nearLitterEquiv) N
  rw [isWellOrder_type_eq, Cardinal.lt_ord] at this
  exact this

noncomputable def nlMap : NearLitter → μ ×ₗ (Unit ⊕ₗ κ) :=
  chooseWf (hwf := isWellOrder) posDeny mk_posDeny'

theorem nlMap_injective : Function.Injective nlMap :=
  chooseWf_injective

theorem nlMap_not_mem_posDeny (N : NearLitter) : nlMap N ∉ posDeny N :=
  chooseWf_not_mem_deny N

open scoped Classical in
noncomputable def pos : Atom ⊕ NearLitter → (μ ×ₗ (Unit ⊕ₗ κ)) ×ₗ ULift.{u} Bool
  | inl a => (alMap (inl a), .up false)
  | inr N => if N.IsLitter then (alMap (inr N.1), .up false) else (nlMap N, .up true)

theorem pos_injective : Function.Injective pos := by
  rintro (a₁ | N₁) (a₂ | N₂) h <;> dsimp only [pos, alMap] at h
  · have h₁ := congr_arg Prod.fst (congr_arg Prod.fst h)
    have h₂ := congr_arg Prod.snd (congr_arg Prod.fst h)
    simp only [EmbeddingLike.apply_eq_iff_eq] at h₁ h₂
    exact congr_arg _ (Prod.ext h₁ (inr_injective h₂))
  · split_ifs at h
    · cases congr_arg Prod.snd (congr_arg Prod.fst h)
    · cases congr_arg Prod.snd h
  · split_ifs at h
    · cases congr_arg Prod.snd (congr_arg Prod.fst h)
    · cases congr_arg Prod.snd h
  · split_ifs at h with hN₁ hN₂
    · obtain ⟨L₁, rfl⟩ := hN₁.exists_litter_eq
      obtain ⟨L₂, rfl⟩ := hN₂.exists_litter_eq
      have := congr_arg Prod.fst (congr_arg Prod.fst h)
      simp only [Litter.toNearLitter_fst, EmbeddingLike.apply_eq_iff_eq] at this
      rw [this]
    · cases congr_arg Prod.snd h
    · cases congr_arg Prod.snd h
    · rw [nlMap_injective (congr_arg Prod.fst h)]

theorem lt_pos_atom' (a : Atom) :
    pos (inr a.1.toNearLitter) < pos (inl a) := by
  dsimp only [pos]
  rw [if_pos (NearLitter.IsLitter.mk _)]
  refine Prod.Lex.left _ _ ?_
  refine Prod.Lex.right _ ?_
  exact Sum.Lex.sep _ _

theorem lt_pos_litter' (N : NearLitter) (hN : ¬N.IsLitter) :
    pos (inr N.1.toNearLitter) < pos (inr N) := by
  dsimp only [pos]
  rw [if_pos (NearLitter.IsLitter.mk _), if_neg hN]
  refine Prod.Lex.left _ _ ?_
  by_contra! h
  refine nlMap_not_mem_posDeny N ?_
  refine ⟨_, ?_, h⟩
  exact Or.inl ⟨hN, rfl⟩

theorem lt_pos_symmDiff' (a : Atom) (N : NearLitter) (h : a ∈ litterSet N.1 ∆ N) :
    pos (inl a) < pos (inr N) := by
  dsimp only [pos]
  rw [if_neg]
  · refine Prod.Lex.left _ _ ?_
    by_contra! h'
    refine nlMap_not_mem_posDeny N ?_
    refine ⟨_, ?_, h'⟩
    exact Or.inr ⟨a, h, rfl⟩
  · rintro ⟨L, hL⟩
    simp only [Litter.toNearLitter_fst, Litter.coe_toNearLitter, symmDiff_self, Set.bot_eq_empty,
      Set.mem_empty_iff_false] at h

theorem bool_lt : lift.{u} #Bool < #μ := by
  simp only [mk_fintype, Fintype.card_bool, Nat.cast_ofNat, lift_ofNat]
  exact (nat_lt_aleph0 2).trans_le Params.μ_isStrongLimit.isLimit.aleph0_le

theorem bool_ne_zero : lift.{u} #Bool ≠ 0 := by
  simp only [mk_fintype, Fintype.card_bool, Nat.cast_ofNat, lift_ofNat, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true]

theorem unitSum_le_iff (x y : (μ ×ₗ (Unit ⊕ₗ κ)) ×ₗ ULift.{u} Bool) :
    x ≤ y ↔ Prod.Lex (· < ·) (· ≤ ·) (μProd_equiv unitSum_lt unitSum_ne_zero x.1, x.2)
      (μProd_equiv unitSum_lt unitSum_ne_zero y.1, y.2) := by
  change Prod.Lex _ _ _ _ ↔ _
  simp only [Prod.lex_iff]
  simp only [OrderIso.lt_iff_lt, EmbeddingLike.apply_eq_iff_eq]

noncomputable def posEquiv : ((μ ×ₗ (Unit ⊕ₗ κ)) ×ₗ ULift.{u} Bool) ≃o μ where
  toFun x := μProd_equiv bool_lt bool_ne_zero (μProd_equiv unitSum_lt unitSum_ne_zero x.1, x.2)
  invFun x := ((μProd_equiv unitSum_lt unitSum_ne_zero).symm
    ((μProd_equiv bool_lt bool_ne_zero).symm x).1, ((μProd_equiv bool_lt bool_ne_zero).symm x).2)
  left_inv := by
    intro x
    simp only [OrderIso.symm_apply_apply, Prod.mk.eta]
  right_inv := by
    intro x
    simp only [OrderIso.apply_symm_apply, Prod.mk.eta]
  map_rel_iff' := by
    intro x y
    simp only [Equiv.coe_fn_mk, map_le_map_iff]
    have := (unitSum_le_iff x y).symm
    exact this

/-- We register this as an instance because we have no need to allow this to be customised. -/
noncomputable instance : BasePositions where
  posAtom := ⟨posEquiv ∘ pos ∘ inl,
    posEquiv.injective.comp (pos_injective.comp inl_injective)⟩
  posNearLitter := ⟨posEquiv ∘ pos ∘ inr,
    posEquiv.injective.comp (pos_injective.comp inr_injective)⟩
  lt_pos_atom := by
    simp only [Function.Embedding.coeFn_mk, Function.comp_apply, OrderIso.lt_iff_lt]
    exact lt_pos_atom'
  lt_pos_litter := by
    simp only [Function.Embedding.coeFn_mk, Function.comp_apply, OrderIso.lt_iff_lt]
    exact lt_pos_litter'
  lt_pos_symmDiff := by
    simp only [Function.Embedding.coeFn_mk, Function.comp_apply, OrderIso.lt_iff_lt]
    exact lt_pos_symmDiff'

end ConNF.MainInduction
