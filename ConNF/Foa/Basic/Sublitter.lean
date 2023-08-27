import ConNF.Atom.NearLitter

open Cardinal

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}]

/-- The type of sublitters. -/
structure Sublitter : Type u where
  litter : Litter
  carrier : Set Atom
  subset : carrier ⊆ litterSet litter
  diff_small : Small (litterSet litter \ carrier)

namespace Sublitter

variable {S S₁ S₂ : Sublitter}

/-- Use sublitter.mk_eq_κ instead if possible. -/
theorem mk_S_eq_κ (S : Sublitter) : #S.carrier = #κ := by
  have := mk_le_mk_of_subset S.subset
  rw [mk_litterSet] at this
  obtain (h | h) := lt_or_eq_of_le this
  · have := mk_diff_add_mk S.subset
    rw [mk_litterSet] at this
    cases (add_lt_of_lt κ_isRegular.aleph0_le S.diff_small h).ne this
  · exact h

instance : SetLike Sublitter Atom where
  coe S := S.carrier
  coe_injective' := by
    rintro ⟨i, N₁, h₁, h₂⟩ ⟨j, N₂, h₃, h₄⟩ (rfl : N₁ = N₂)
    obtain ⟨e⟩ := Cardinal.eq.mp (Sublitter.mk_S_eq_κ ⟨i, N₁, h₁, h₂⟩)
    have h₅ := h₁ (e.symm default).prop
    have h₆ := h₃ (e.symm default).prop
    rw [mem_litterSet] at h₅ h₆
    rw [h₅] at h₆
    cases h₆
    rfl

@[simp]
theorem mk_eq_κ (S : Sublitter) : #S = #κ :=
  S.mk_S_eq_κ

@[simp]
theorem mk_eq_κ' (S : Sublitter) : #(S : Set Atom) = #κ :=
  S.mk_S_eq_κ

@[simp]
theorem carrier_eq_coe {S : Sublitter} : S.carrier = S :=
  rfl

@[simp]
theorem coe_mk (L S subset diff_small) :
    (⟨L, S, subset, diff_small⟩ : Sublitter) = S :=
  rfl

@[ext]
theorem ext (h : (S₁ : Set Atom) = S₂) : S₁ = S₂ :=
  SetLike.coe_injective h

theorem fst_eq_of_mem {a : Atom} (h : a ∈ S) : a.1 = S.litter :=
  S.subset h

theorem mem_litterSet_of_mem {a : Atom} (h : a ∈ S) : a ∈ litterSet S.litter :=
  S.subset h

@[simp]
theorem mem_mk {a : Atom} {L S subset diff_small} :
    a ∈ (⟨L, S, subset, diff_small⟩ : Sublitter) ↔ a ∈ S :=
  Iff.rfl

@[simp]
theorem litter_diff_eq (S : Sublitter) : (S : Set Atom) \ litterSet S.litter = ∅ :=
  Set.eq_empty_of_forall_not_mem fun _ ha => ha.2 (S.subset ha.1)

theorem isNearLitter (S : Sublitter) : IsNearLitter S.litter S := by
  refine Small.union S.diff_small ?_
  rw [litter_diff_eq]
  exact small_empty

def toNearLitter (S : Sublitter) : NearLitter :=
  ⟨S.litter, S, S.isNearLitter⟩

@[simp]
theorem toNearLitter_litter (S : Sublitter) : S.toNearLitter.1 = S.litter :=
  rfl

@[simp]
theorem coe_toNearLitter (S : Sublitter) : (S.toNearLitter : Set Atom) = S :=
  rfl

@[simp]
theorem mem_toNearLitter (a : Atom) : a ∈ S.toNearLitter ↔ a ∈ S :=
  Iff.rfl

theorem isNear_iff : IsNear (S₁ : Set Atom) S₂ ↔ S₁.litter = S₂.litter := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨f⟩ := IsNear.mk_inter h S₁.mk_eq_κ.symm.le
    rw [← fst_eq_of_mem (f default).prop.1, ← fst_eq_of_mem (f default).prop.2]
  · refine S₁.isNearLitter.symm.trans ?_
    rw [h]
    exact S₂.isNearLitter

theorem inter_nonempty_iff : (S₁ ∩ S₂ : Set Atom).Nonempty ↔ S₁.litter = S₂.litter := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, ha⟩ := h
    rw [← fst_eq_of_mem ha.1, fst_eq_of_mem ha.2]
  · exact NearLitter.inter_nonempty_of_fst_eq_fst (N₁ := S₁.toNearLitter) (N₂ := S₂.toNearLitter) h

end Sublitter

def Litter.toSublitter (L : Litter) : Sublitter :=
  ⟨L, litterSet L, subset_rfl, by
    rw [sdiff_self]
    exact small_empty⟩

@[simp]
theorem Litter.litter_toSublitter (L : Litter) : L.toSublitter.litter = L :=
  rfl

@[simp]
theorem Litter.coe_toSublitter (L : Litter) : (L.toSublitter : Set Atom) = litterSet L :=
  rfl

namespace Sublitter

noncomputable def equivκ (S : Sublitter) : S ≃ κ :=
  (Cardinal.eq.mp S.mk_eq_κ).some

/-- There is a (unique) order isomorphism between any two sublitters. -/
noncomputable def equiv (S T : Sublitter) : S ≃ T :=
  S.equivκ.trans T.equivκ.symm

@[simp]
theorem equiv_apply_mem {S T : Sublitter} (a : S) : (S.equiv T a : Atom) ∈ T :=
  (S.equiv T a).prop

@[simp]
theorem equiv_symm_apply_mem {S T : Sublitter} (a : T) : ((S.equiv T).symm a : Atom) ∈ S :=
  ((S.equiv T).symm a).prop

@[simp]
theorem equiv_apply_fst_eq {S T : Sublitter} (a : S) : (S.equiv T a : Atom).1 = T.litter :=
  T.subset (S.equiv T a).prop

@[simp]
theorem equiv_symm_apply_fst_eq {S T : Sublitter} (a : T) :
    ((S.equiv T).symm a : Atom).1 = S.litter :=
  S.subset ((S.equiv T).symm a).prop

theorem equiv_congr_left {S T U : Sublitter} (h : S = T) (a : S) :
    (S.equiv U a : Atom) = T.equiv U ⟨a, by rw [← h]; exact a.2⟩ := by
  cases h
  rw [Subtype.coe_eta]

theorem equiv_congr_right {S T U : Sublitter} (h : T = U) (a : S) :
    (S.equiv T a : Atom) = S.equiv U a := by cases h; rfl

end Sublitter

end ConNF
