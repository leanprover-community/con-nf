import ConNF.Counting.OrdSupport
import ConNF.Counting.Reorder

/-!
# Equivalence of ordered supports
-/

open Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

def reorderSymm (r : Tree Reorder β) : Tree Reorder β :=
  fun A => (r A).symm

namespace OrdSupport

/-- Ordered supports are *equivalent* if they are defined on the same set and put support conditions
in the same order. -/
structure Equiv (S T : OrdSupport β) : Prop where
  mem_left ⦃c : SupportCondition β⦄ : c ∈ T → c ∈ S
  mem_right ⦃c : SupportCondition β⦄ : c ∈ S → c ∈ T
  lt_iff_lt ⦃c d : SupportCondition β⦄ (hcS : c ∈ S) (hcT : c ∈ T) (hdS : d ∈ S) (hdT : d ∈ T) :
    (S.cpos c).get hcS < (S.cpos d).get hdS ↔ (T.cpos c).get hcT < (T.cpos d).get hdT

namespace Equiv

def refl (S : OrdSupport β) : Equiv S S where
  mem_left _ hc := hc
  mem_right _ hc := hc
  lt_iff_lt _ _ _ _ _ _ := Iff.rfl

def symm {S T : OrdSupport β} (h : Equiv S T) : Equiv T S where
  mem_left _ hc := h.mem_right hc
  mem_right _ hc := h.mem_left hc
  lt_iff_lt _ _ hcT hcS hdT hdS := (h.lt_iff_lt hcS hcT hdS hdT).symm

def trans {S T U : OrdSupport β} (h₁ : Equiv S T) (h₂ : Equiv T U) : Equiv S U where
  mem_left _ hc := h₁.mem_left (h₂.mem_left hc)
  mem_right _ hc := h₂.mem_right (h₁.mem_right hc)
  lt_iff_lt _ _ hcS hcU hdS hdU :=
    (h₁.lt_iff_lt hcS (h₁.mem_right hcS) hdS (h₁.mem_right hdS)).trans
    (h₂.lt_iff_lt (h₂.mem_left hcU) hcU (h₂.mem_left hdU) hdU)

end Equiv

instance setoid (β : Iic α) : Setoid (OrdSupport β) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem mem_iff_mem {S T : OrdSupport β} (h : S ≈ T) (c : SupportCondition β) :
    c ∈ S ↔ c ∈ T :=
  ⟨fun h' => h.mem_right h', fun h' => h.mem_left h'⟩

theorem smul_equiv_smul {S T : OrdSupport β} (h : S ≈ T) (ρ : Allowable β) :
    ρ • S ≈ ρ • T := by
  constructor
  case mem_left =>
    intro c hc
    exact h.mem_left hc
  case mem_right =>
    intro c hc
    exact h.mem_right hc
  case lt_iff_lt =>
    intro c d hcS hcT hdS hdT
    exact h.lt_iff_lt _ _ _ _

/-- This is the key lemma that uses the fact that equivalences are order isomorphisms. -/
theorem cpos_smul_eq_cpos {S : OrdSupport β} (ρ : Allowable β) (h : ρ • S ≈ S)
    (c : SupportCondition β) (hc : c ∈ S) :
    ((ρ • S).cpos c).get (h.mem_left hc) = (S.cpos c).get hc := by
  letI hwo : IsWellOrder (Atom ⊕ NearLitter) (· < ·) := inferInstance
  letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
  -- Override the normal preorder on `⊕`.
  letI hpo : Preorder (Atom ⊕ NearLitter) := hlo.toPreorder
  refine hwo.wf.induction
    (C := fun x => ∀ c, ∀ hc : c ∈ S, (S.cpos c).get hc = x →
      ((ρ • S).cpos c).get (h.mem_left hc) = (S.cpos c).get hc)
    _ ?_ c hc rfl
  clear hc c
  rintro _ ih c hc rfl
  obtain (h' | h' | h') := lt_trichotomy (((ρ • S).cpos c).get (h.mem_left hc)) ((S.cpos c).get hc)
  · exfalso
    have := ih _ h' _ (h.mem_left hc) rfl
    have h'' := h.lt_iff_lt
      (h.mem_left <| h.mem_left hc) (h.mem_left hc) (h.mem_left hc) hc
    simp_rw [smul_cpos, ← h'', this, smul_cpos] at h'
    exact ne_of_lt h' rfl
  · exact h'
  · exfalso
    have := h.lt_iff_lt
      (smul_mem_smul.mpr hc) (h.mem_right (smul_mem_smul.mpr hc)) (h.mem_left hc) hc
    simp_rw [smul_cpos_smul] at this
    rw [this] at h'
    have := ih _ h' _ _ rfl
    simp_rw [smul_cpos_smul] at this
    exact ne_of_lt h' this.symm

theorem smul_eq_of_smul_equiv {S : OrdSupport β} (ρ : Allowable β) (h : ρ • S ≈ S) :
    ρ • S = S := by
  ext c _ hc
  · exact ⟨fun hc => h.mem_right hc, fun hc => h.mem_left hc⟩
  · exact cpos_smul_eq_cpos ρ h c hc

theorem Strong.reduced_of_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    (c : SupportCondition β) (h : c ∈ T) : Reduced c.value :=
  hS.reduced_of_mem c (hST.mem_left h)

theorem Strong.transConstrains_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    (c d : SupportCondition β) (hc : Reduced c.value) (hcd : c <[α] d) (hd : d ∈ T) : c ∈ T :=
  hST.mem_right (hS.transConstrains_mem c d hc hcd (hST.mem_left hd))

theorem Strong.fst_toNearLitter_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    {A : ExtendedIndex β} {a : Atom} (h : ⟨A, inl a⟩ ∈ T) :
    ⟨A, inr a.1.toNearLitter⟩ ∈ T :=
  hST.mem_right (hS.fst_toNearLitter_mem (hST.mem_left h))

theorem Strong.isLitter_of_mem_equiv {S T : OrdSupport β} (hS : S.Strong) (hST : S ≈ T)
    {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ T) :
    N.IsLitter :=
  hS.isLitter_of_mem (hST.mem_left h)

/--
`r` is an equivalence of ordered supports `S` and `T`.
Paths in the following diagram starting with `S` or `T` commute, where
* the morphisms `S ↔ T` are the identity,
* the maps `μ ↔ μ` are `toFun` and `invFun`,
* the maps `S → μ` and `T → μ` are `cpos`.
```
μ ↔ μ
↑   ↑
S ↔ T
```
-/
structure IsEquiv (r : Tree Reorder β) (S T : OrdSupport β) : Prop where
  equiv : S ≈ T
  toFun_apply (c : SupportCondition β) (hS : c ∈ S) (hT : c ∈ T) :
    r c.path ((S.cpos c).get hS) = (T.cpos c).get hT
  invFun_apply (c : SupportCondition β) (hT : c ∈ T) (hS : c ∈ S) :
    (r c.path).symm ((T.cpos c).get hT) = (S.cpos c).get hS

theorem IsEquiv.symm {r : Tree Reorder β} {S T : OrdSupport β} (h : IsEquiv r S T) :
    IsEquiv (reorderSymm r) T S :=
  ⟨h.equiv.symm, h.invFun_apply, h.toFun_apply⟩

open scoped Classical in
/-- Maps `S.cpos c` to `T.cpos c` if the input is of the form `S.cpos c`. -/
noncomputable def posOf (S T : OrdSupport β) (A : ExtendedIndex β) (x : Atom ⊕ NearLitter) :
    Atom ⊕ NearLitter :=
  if h : ∃ y : Atom ⊕ NearLitter, ∃ c : SupportCondition β, ∃ hS : c ∈ S, ∃ hT : c ∈ T,
      c.path = A ∧ (S.cpos c).get hS = x ∧ (T.cpos c).get hT = y then
    h.choose
  else
    default

theorem posOf_spec (S T : OrdSupport β) (A : ExtendedIndex β) (x : Atom ⊕ NearLitter)
    (h : ∃ y : Atom ⊕ NearLitter, ∃ c : SupportCondition β, ∃ hS : c ∈ S, ∃ hT : c ∈ T,
      c.path = A ∧ (S.cpos c).get hS = x ∧ (T.cpos c).get hT = y) :
    ∃ c : SupportCondition β, ∃ hS : c ∈ S, ∃ hT : c ∈ T,
      c.path = A ∧ (S.cpos c).get hS = x ∧ (T.cpos c).get hT = posOf S T A x := by
  rw [posOf, dif_pos h]
  exact h.choose_spec

/-- `posOf` behaves as required. -/
theorem posOf_cpos (S T : OrdSupport β) (c : SupportCondition β) (hS : c ∈ S) (hT : c ∈ T) :
    posOf S T c.path ((S.cpos c).get hS) = (T.cpos c).get hT := by
  obtain ⟨_, _, _, h₁, h₂, h₃⟩ :=
    posOf_spec S T c.path ((S.cpos c).get hS) ⟨_, c, hS, hT, rfl, rfl, rfl⟩
  cases S.injective _ _ _ _ h₁ h₂
  exact h₃.symm

noncomputable def reorderTree (S T : OrdSupport β) : Tree Reorder β :=
  fun A => {
    toFun := posOf S T A
    invFun := posOf T S A
  }

theorem reorderTree_isEquiv {S T : OrdSupport β} (h : S ≈ T) : IsEquiv (reorderTree S T) S T := by
  constructor
  · exact h
  · intro c hS hT
    rw [reorderTree]
    dsimp only
    rw [posOf_cpos]
  · intro c hT hS
    rw [reorderTree, Reorder.symm]
    dsimp only
    rw [posOf_cpos]

theorem exists_isEquiv_of_equiv {S T : OrdSupport β} (h : S ≈ T) :
    ∃ r : Tree Reorder β, IsEquiv r S T :=
  ⟨reorderTree S T, reorderTree_isEquiv h⟩

theorem isEquiv_isEquiv_right {r : Tree Reorder β} {S T U : OrdSupport β}
    (h₁ : IsEquiv r S T) (h₂ : IsEquiv r S U) : T = U := by
  ext c hcT hcU
  · rw [← mem_iff_mem h₁.equiv c, ← mem_iff_mem h₂.equiv c]
  · rw [← h₁.toFun_apply c (h₁.equiv.mem_left hcT) hcT,
      ← h₂.toFun_apply c (h₂.equiv.mem_left hcU) hcU]

theorem isEquiv_smul {r : Tree Reorder β} {S T : OrdSupport β}
    (h : IsEquiv r S T) (ρ : Allowable β) :
    IsEquiv r (ρ • S) (ρ • T) := by
  constructor
  case equiv => exact smul_equiv_smul h.equiv ρ
  case toFun_apply =>
    intros c hS hT
    exact h.toFun_apply (ρ⁻¹ • c) hS hT
  case invFun_apply =>
    intros c hT hS
    exact h.invFun_apply (ρ⁻¹ • c) hT hS

-- TODO: Rename this.
structure ReorderSupports (S : OrdSupport β) (r : Tree Reorder β) : Prop where
  invFun_toFun (c : SupportCondition β) (hc : c ∈ S) :
    (r c.path).symm (r c.path ((S.cpos c).get hc)) = (S.cpos c).get hc
  lt_iff_lt (c d : SupportCondition β) (hc : c ∈ S) (hd : d ∈ S) :
    (S.cpos c).get hc < (S.cpos d).get hd ↔
    r c.path ((S.cpos c).get hc) < r d.path ((S.cpos d).get hd)

theorem reorderSupports_of_isEquiv {S T : OrdSupport β} {r : Tree Reorder β}
    (h : IsEquiv r S T) : ReorderSupports S r := by
  constructor
  · intro c hc
    rw [h.toFun_apply, h.invFun_apply]
    exact h.equiv.mem_right hc
  · intro c d hc hd
    rw [h.toFun_apply _ hc (h.equiv.mem_right hc), h.toFun_apply _ hd (h.equiv.mem_right hd)]
    exact h.equiv.lt_iff_lt hc (h.equiv.mem_right hc) hd (h.equiv.mem_right hd)

theorem ReorderSupports.smul {S : OrdSupport β} {r : Tree Reorder β}
    (h : S.ReorderSupports r) (ρ : Allowable β) : (ρ • S).ReorderSupports r :=
  ⟨fun _ => h.invFun_toFun _, fun c d => h.lt_iff_lt (ρ⁻¹ • c) (ρ⁻¹ • d)⟩

theorem ReorderSupports.cpos_injective {S : OrdSupport β} {r : Tree Reorder β}
    (h : S.ReorderSupports r) {A : ExtendedIndex β} {x y : Atom ⊕ NearLitter}
    (hx : ⟨A, x⟩ ∈ S) (hy : ⟨A, y⟩ ∈ S)
    (hxy : r A ((S.cpos ⟨A, x⟩).get hx) = r A ((S.cpos ⟨A, y⟩).get hy)) :
    x = y := by
  have := h.invFun_toFun _ hx
  rw [hxy, h.invFun_toFun _ hy] at this
  have := S.injective _ _ hx hy rfl this.symm
  simp only [SupportCondition.mk.injEq, true_and] at this
  exact this

def reorder (S : OrdSupport β) (r : Tree Reorder β) (h : S.ReorderSupports r) : OrdSupport β where
  cpos c := ⟨c ∈ S, fun h => r c.path ((S.cpos c).get h)⟩
  injective := by
    rintro ⟨A, x⟩ ⟨_, y⟩ hx hy rfl h'
    rw [h.cpos_injective hx hy h']
  dom_small' := S.dom_small'

@[simp]
theorem cpos_reorder {S : OrdSupport β} {r : Tree Reorder β} {h : S.ReorderSupports r}
    (c : SupportCondition β) (hc : c ∈ S) :
    ((reorder S r h).cpos c).get hc = r c.path ((S.cpos c).get hc) :=
  rfl

theorem reorder_equiv (S : OrdSupport β) (r : Tree Reorder β) (h : S.ReorderSupports r) :
    reorder S r h ≈ S := by
  constructor
  · intro c hc
    exact hc
  · intro c hc
    exact hc
  · intro c d hcS hcT hcD hdT
    rw [cpos_reorder, cpos_reorder]
    exact (h.lt_iff_lt _ _ _ _).symm

theorem reorder_isEquiv (S : OrdSupport β) (r : Tree Reorder β) (h : S.ReorderSupports r) :
    IsEquiv r S (reorder S r h) := by
  refine ⟨(reorder_equiv S r h).symm, ?_, ?_⟩
  · intros
    rfl
  · intros
    rw [cpos_reorder, h.invFun_toFun]

theorem subset_or_subset_of_le_equiv {S₁ S₂ T₁ T₂ : OrdSupport β}
    (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂) (hT : T₁ ≈ T₂) :
    (∀ c, c ∈ S₁ → c ∈ S₂) ∨ (∀ c, c ∈ S₂ → c ∈ S₁) := by
  rw [or_iff_not_imp_left]
  intro h c hc₂
  by_contra hc₁
  simp only [not_forall, exists_prop] at h
  obtain ⟨d, hd₁, hd₂⟩ := h
  have h₁' := h₁.get_lt_get d c hd₁ (h₁.mem_of_mem d hd₁) hc₁ (hT.mem_left (h₂.mem_of_mem c hc₂))
  have h₂' := h₂.get_lt_get c d hc₂ (h₂.mem_of_mem c hc₂) hd₂ (hT.mem_right (h₁.mem_of_mem d hd₁))
  rw [← hT.lt_iff_lt (hT.mem_left (h₂.mem_of_mem c hc₂)) _ (h₁.mem_of_mem d hd₁)] at h₂'
  exact not_lt_of_lt h₁' h₂'

/-- If `ρ` maps `S` to an initial segment of itself, it is an order isomorphism. -/
theorem lt_iff_lt_of_le_equiv {S T₁ T₂ : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T₁) (h₂ : S ≤ T₂) (hT : T₁ ≈ T₂)
    (h : ∀ c, c ∈ S → ρ • c ∈ S)
    (c d : SupportCondition β) (hc : c ∈ S) (hd : d ∈ S) :
    (S.cpos c).get hc < (S.cpos d).get hd ↔
    (S.cpos (ρ • c)).get (h c hc) < (S.cpos (ρ • d)).get (h d hd) := by
  simp_rw [← smul_cpos_smul (ρ := ρ) (c := c), ← smul_cpos_smul (ρ := ρ) (c := d)]
  rw [h₁.get_eq_get _ _ (h₁.mem_of_mem _ (smul_mem_smul.mpr hc)),
    h₁.get_eq_get _ _ (h₁.mem_of_mem _ (smul_mem_smul.mpr hd)),
    h₂.get_eq_get _ _ (hT.mem_right (h₁.mem_of_mem _ (smul_mem_smul.mpr hc))),
    h₂.get_eq_get _ _ (hT.mem_right (h₁.mem_of_mem _ (smul_mem_smul.mpr hd))),
    hT.lt_iff_lt]

/-- If `ρ` maps `S` to an initial segment of itself, it is the identity function. -/
theorem smul_eq_of_le_equiv' {S T₁ T₂ : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T₁) (h₂ : S ≤ T₂) (hT : T₁ ≈ T₂)
    (h : ∀ c, c ∈ S → ρ • c ∈ S)
    (c : SupportCondition β) (hc : c ∈ S) :
    ρ • c = c := by
  letI hwo : IsWellOrder (Atom ⊕ NearLitter) (· < ·) := inferInstance
  letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
  letI hpo : Preorder (Atom ⊕ NearLitter) := hlo.toPreorder
  refine hwo.wf.induction _
    (C := fun x => ∀ c, ∀ hc : c ∈ S, (S.cpos c).get hc = x → ρ • c = c)
    ?_ c hc rfl
  clear hc c
  rintro _ ih c hc rfl
  have hc'' : c ∈ ρ • S
  · by_contra hc''
    have := h₁.get_lt_get (ρ • c) c
      (smul_mem_smul.mpr hc) (h₁.mem_of_mem _ (smul_mem_smul.mpr hc))
      hc'' (hT.mem_left (h₂.mem_of_mem _ hc))
    rw [hT.lt_iff_lt _ (h₂.mem_of_mem _ (h c hc)) (hT.mem_left (h₂.mem_of_mem _ hc))
      (h₂.mem_of_mem _ hc)] at this
    rw [← h₂.get_eq_get _ (h c hc), ← h₂.get_eq_get _ hc] at this
    have h := ih _ this (ρ • c) (h c hc) rfl
    rw [smul_left_cancel_iff] at h
    simp_rw [h] at this
    exact this.false
  refine S.injective (ρ • c) c (h c hc) hc rfl ?_
  by_contra' hc'
  obtain (hc' | hc') := lt_or_gt_of_ne hc'
  · have := ih _ hc' (ρ • c) (h c hc) rfl
    rw [smul_left_cancel_iff] at this
    simp_rw [this] at hc'
    exact hc'.false
  · rw [gt_iff_lt] at hc'
    have := lt_iff_lt_of_le_equiv h₁ h₂ hT h (ρ⁻¹ • c) c hc'' hc
    simp only [smul_inv_smul, hc', iff_true] at this
    have h := ih _ this (ρ⁻¹ • c) hc'' rfl
    rw [smul_inv_smul] at h
    simp_rw [← h] at this
    exact this.false

/-- `ρ` is an order isomorphism. -/
theorem smul_eq_of_le_equiv {S T₁ T₂ : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T₁) (h₂ : S ≤ T₂) (hT : T₁ ≈ T₂)
    (c : SupportCondition β) (hc : c ∈ S) :
    ρ • c = c := by
  obtain (h | h) := subset_or_subset_of_le_equiv h₁ h₂ hT
  · refine smul_eq_of_le_equiv' h₁ h₂ hT ?_ c hc
    intro c hc
    exact h (ρ • c) (smul_mem_smul.mpr hc)
  · have := smul_eq_of_le_equiv' (ρ := ρ⁻¹) (by rwa [inv_smul_smul]) h₁ hT.symm ?_
    · rw [← this (ρ • c) (smul_mem_smul.mpr hc), inv_smul_smul]
    · intro c hc
      exact h (ρ⁻¹ • c) hc

theorem equiv_of_le_equiv {S T₁ T₂ : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T₁) (h₂ : S ≤ T₂) (hT : T₁ ≈ T₂) : ρ • S ≈ S := by
  constructor
  · intro c hc
    rw [smul_mem, ← smul_eq_of_le_equiv h₁ h₂ hT c hc, inv_smul_smul]
    exact hc
  · intro c hc
    have := smul_eq_of_le_equiv h₁ h₂ hT (ρ⁻¹ • c) hc
    rw [smul_inv_smul] at this
    rw [this]
    exact hc
  · intro c d hc₁ hc₂ hd₁ hd₂
    rw [h₁.get_eq_get c hc₁ (h₁.mem_of_mem c hc₁),
      h₁.get_eq_get d hd₁ (h₁.mem_of_mem d hd₁),
      h₂.get_eq_get c hc₂ (h₂.mem_of_mem c hc₂),
      h₂.get_eq_get d hd₂ (h₂.mem_of_mem d hd₂)]
    exact hT.lt_iff_lt
      (h₁.mem_of_mem c hc₁) (h₂.mem_of_mem c hc₂) (h₁.mem_of_mem d hd₁) (h₂.mem_of_mem d hd₂)

end OrdSupport

def OrdSupportClass (β : Iic α) : Type u :=
  Quotient (OrdSupport.setoid β)

namespace OrdSupportClass

def mk (S : OrdSupport β) : OrdSupportClass β := ⟦S⟧

protected theorem eq {S T : OrdSupport β} : mk S = mk T ↔ S ≈ T :=
  Quotient.eq

def Strong (S : OrdSupportClass β) : Prop :=
  ∃ S' : OrdSupport β, S'.Strong ∧ S = mk S'

-- TODO: Make this into a `noncomputable def`?
theorem exists_strong_of_strong {S : OrdSupportClass β} (h : S.Strong) :
    ∃ S' : OrdSupport β, S'.Strong ∧ S = mk S' :=
  h

instance : MulAction (Allowable β) (OrdSupportClass β) where
  smul ρ := Quotient.lift (fun S => mk (ρ • S))
    (fun S T h => Quotient.sound (OrdSupport.smul_equiv_smul h ρ))
  one_smul S := by
    refine Quotient.inductionOn S ?_
    change ∀ S, mk ((1 : Allowable β) • S) = mk S
    simp only [one_smul, implies_true]
  mul_smul ρ₁ ρ₂ S := by
    refine Quotient.inductionOn S ?_
    change ∀ S, mk ((ρ₁ * ρ₂) • S) = mk (ρ₁ • ρ₂ • S)
    simp only [mul_smul, implies_true]

@[simp]
theorem smul_mk (ρ : Allowable β) (S : OrdSupport β) :
    mk (ρ • S) = ρ • (mk S) :=
  rfl

end OrdSupportClass

end ConNF
