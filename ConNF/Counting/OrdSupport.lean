import ConNF.Foa.Basic.Reduction

/-!
# Ordered supports
-/

open Set Sum
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

structure OrdSupport (β : Iic α) where
  /-- The position of a support condition in this ordered support.
  Named `cpos` instead of `pos` so it doesn't clash with `pos`.

  The support conditions in the domain of an ordered support are well-ordered lexicographically
  first by `cpos` then their paths. -/
  cpos : SupportCondition β →. Atom ⊕ NearLitter
  injective (c d : SupportCondition β) (hc : (cpos c).Dom) (hd : (cpos d).Dom) :
    c.path = d.path → (cpos c).get hc = (cpos d).get hd → c = d
  dom_small' : Small cpos.Dom

namespace OrdSupport

instance : Membership (SupportCondition β) (OrdSupport β) where
  mem c S := (S.cpos c).Dom

theorem mem_iff {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ S ↔ (S.cpos c).Dom :=
  Iff.rfl

theorem dom_small (S : OrdSupport β) : Small {c | c ∈ S} :=
  S.dom_small'

@[ext]
theorem ext {S T : OrdSupport β}
    (hdom : ∀ c, c ∈ S ↔ c ∈ T)
    (h : ∀ c hcS hcT, (S.cpos c).get hcS = (T.cpos c).get hcT) :
    S = T := by
  rw [mk.injEq]
  funext c
  exact Part.ext' (hdom c) (h c)

instance : MulAction (Allowable β) (OrdSupport β) where
  smul ρ S := {
    cpos := fun c => S.cpos (ρ⁻¹ • c)
    injective := fun c d hc hd h₁ h₂ =>
      smul_left_cancel _ (S.injective (ρ⁻¹ • c) (ρ⁻¹ • d) hc hd h₁ h₂)
    dom_small' := by
      refine lt_of_le_of_lt ?_ S.dom_small
      refine ⟨⟨fun c => ⟨ρ⁻¹ • c.1, c.2⟩, ?_⟩⟩
      rintro ⟨c, hc⟩ ⟨d, hd⟩
      simp only [Subtype.mk.injEq, smul_left_cancel_iff, PFun.dom_mk, coe_setOf, mem_setOf_eq,
        imp_self]
  }
  one_smul S := by
    ext c hc₁ hc₂
    · change (S.cpos _).Dom ↔ (S.cpos _).Dom
      simp only [inv_one, one_smul]
    · change (S.cpos _).get _ = (S.cpos _).get _
      simp only [inv_one, one_smul]
  mul_smul π₁ π₂ S:= by
    ext c hc₁ hc₂
    · change (S.cpos _).Dom ↔ (S.cpos _).Dom
      simp only [mul_inv_rev, mul_smul]
    · change (S.cpos _).get _ = (S.cpos _).get _
      simp only [mul_inv_rev, mul_smul]


@[simp]
theorem smul_mem {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ • S ↔ ρ⁻¹ • c ∈ S :=
  Iff.rfl

theorem smul_mem_smul {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    ρ • c ∈ ρ • S ↔ c ∈ S := by
  simp only [smul_mem, inv_smul_smul]

@[simp]
theorem smul_cpos {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    (ρ • S).cpos c = S.cpos (ρ⁻¹ • c) :=
  rfl

theorem smul_cpos_rev {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    S.cpos (ρ • c) = (ρ⁻¹ • S).cpos c := by
  simp only [smul_cpos, inv_inv]

theorem smul_cpos_smul {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    (ρ • S).cpos (ρ • c) = S.cpos c := by
  simp only [smul_cpos, inv_smul_smul]

theorem smul_mem_inv {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ⁻¹ • S ↔ ρ • c ∈ S := by
  simp only [smul_mem, inv_inv]

theorem inv_smul_mem {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    ρ⁻¹ • c ∈ S ↔ c ∈ ρ • S := by
  simp only [smul_mem]

theorem smul_eq_of_smul_eq (ρ : Allowable β) {S : OrdSupport β} {c : SupportCondition β}
    (h : c ∈ S) : ρ • S = S → ρ • c = c := by
  intro hS
  have := congr_arg₂ OrdSupport.cpos hS (refl c)
  refine eq_inv_smul_iff.mp (S.injective c (ρ⁻¹ • c) h ?_ rfl ?_)
  · rw [← smul_cpos, this]
    exact h
  · rw [smul_cpos] at this
    simp_rw [this]

/-- The restriction of this ordered support to conditions that come before position `i`. -/
def before (S : OrdSupport β) (i : Atom ⊕ NearLitter) : OrdSupport β where
  cpos c := ⟨∃ h : c ∈ S, (S.cpos c).get h < i, fun h => (S.cpos c).get h.1⟩
  injective c d hc hd h := S.injective c d _ _ h
  dom_small' := by
    refine Small.mono ?_ S.dom_small
    intro c hc
    exact hc.1

@[simp]
theorem mem_before {S : OrdSupport β} {i : Atom ⊕ NearLitter} (c : SupportCondition β) :
    c ∈ S.before i ↔ ∃ h : c ∈ S, (S.cpos c).get h < i :=
  Iff.rfl

@[simp]
theorem before_get {S : OrdSupport β} {i : Atom ⊕ NearLitter} {c : SupportCondition β}
    (hc : c ∈ S.before i) :
    ((S.before i).cpos c).get hc = (S.cpos c).get hc.1 :=
  rfl

/-- Retains only those support conditions beginning with the path `A`. -/
def comp (S : OrdSupport β) (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ) : OrdSupport γ where
  cpos c := S.cpos ⟨A.comp c.path, c.value⟩
  injective c d hc hd h₁ h₂ := by
    have := S.injective _ _ _ _ ?_ h₂
    · rw [SupportCondition.mk.injEq] at this ⊢
      rw [Quiver.Path.comp_inj_right] at this
      exact this
    · rw [h₁]
  dom_small' := by
    change Small ((fun c : SupportCondition γ => ⟨A.comp c.path, c.value⟩) ⁻¹' S.cpos.Dom)
    refine Small.preimage ?_ S.dom_small
    intro c d h
    rw [SupportCondition.mk.injEq] at h ⊢
    rw [Quiver.Path.comp_inj_right] at h
    exact h

@[simp]
theorem mem_comp {S : OrdSupport β} (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ)
    (c : SupportCondition γ) :
    c ∈ S.comp γ A ↔ ⟨A.comp c.path, c.value⟩ ∈ S :=
  Iff.rfl

@[simp]
theorem comp_get {S : OrdSupport β} {γ : Iic α} {A : Quiver.Path (β : TypeIndex) γ}
    {c : SupportCondition γ} (hc : c ∈ S.comp γ A) :
    ((S.comp γ A).cpos c).get hc = (S.cpos ⟨A.comp c.path, c.value⟩).get hc :=
  rfl

/-- An ordered support is strong if every element of its domain is reduced, every reduced condition
it constrains lies in its domain, and the position of each support condition is given by the global
position function. -/
structure Strong (S : OrdSupport β) : Prop where
  reduced_of_mem (c : SupportCondition β) : c ∈ S → Reduced c.value
  transConstrains_mem (c d : SupportCondition β) : Reduced c.value → c <[α] d → d ∈ S → c ∈ S
  cpos_get_eq (c : SupportCondition β) (hc : c ∈ S) : (S.cpos c).get hc = c.value

theorem Strong.cpos_eq {S : OrdSupport β} (h : S.Strong) {c : SupportCondition β} :
    S.cpos c = ⟨c ∈ S, fun _ => c.value⟩ := by
  refine Part.ext' Iff.rfl ?_
  intros hc _
  exact h.cpos_get_eq c hc

theorem Strong.fst_toNearLitter_mem {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {a : Atom} (h : ⟨A, inl a⟩ ∈ S) :
    ⟨A, inr a.1.toNearLitter⟩ ∈ S :=
  hS.transConstrains_mem _ _
    (Reduced.mkLitter a.1) (Relation.TransGen.single (Constrains.atom A a)) h

theorem Strong.isLitter_of_mem {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ S) :
    N.IsLitter := by
  cases hS.reduced_of_mem _ h
  exact NearLitter.IsLitter.mk _

def strongSupport (S : Set (SupportCondition β)) (hS : Small S) : OrdSupport β where
  cpos c := ⟨c ∈ S, fun _ => c.value⟩
  injective := by intros; ext <;> assumption
  dom_small' := hS

@[simp]
theorem strongSupport_cpos (S : Set (SupportCondition β)) (hS : Small S)
    (c : SupportCondition β) (h : c ∈ S) : ((strongSupport S hS).cpos c).get h = c.value :=
  rfl

theorem strongSupport_strong (S : Set (SupportCondition β)) (hS : Small S)
    (hS₁ : ∀ c ∈ S, Reduced c.value) (hS₂ : ∀ c d, Reduced c.value → c <[α] d → d ∈ S → c ∈ S) :
    (strongSupport S hS).Strong :=
  ⟨hS₁, hS₂, fun _ _ => rfl⟩

theorem smul_strongSupport_eq (S : Set (SupportCondition β)) (hS : Small S) (ρ : Allowable β)
    (h : ∀ c ∈ S, ρ • c = c) : ρ • strongSupport S hS = strongSupport S hS := by
  ext c hcS hcT
  · simp only [smul_mem]
    constructor
    · intro hc
      have := h _ hc
      rw [smul_inv_smul] at this
      rw [this]
      exact hc
    · intro hc
      have := h _ hc
      rw [← this, inv_smul_smul]
      exact hc
  · simp only [smul_cpos, strongSupport_cpos]
    conv_lhs => rw [← h _ hcT, inv_smul_smul]

/-- `T` *extends* `S` if it is defined wherever `S` is, and agrees with it there, and any
extra support conditions come after all those in `S`. -/
structure Extends (T S : OrdSupport β) : Prop where
  mem_of_mem (c : SupportCondition β) : c ∈ S → c ∈ T
  get_eq_get (c : SupportCondition β) (hS : c ∈ S) (hT : c ∈ T) :
    (S.cpos c).get hS = (T.cpos c).get hT
  /-- If `c` is in `S ∩ T` and `d` is in `T \ S`, then `c` comes before `d`. -/
  get_lt_get (c d : SupportCondition β) (hcS : c ∈ S) (hcT : c ∈ T) (hdS : d ∉ S) (hdT : d ∈ T) :
    (T.cpos c).get hcT < (T.cpos d).get hdT

instance : LE (OrdSupport β) where
  le S T := Extends T S

instance : PartialOrder (OrdSupport β) where
  le_refl S := by
    constructor
    · intro c hc
      exact hc
    · intros
      rfl
    · intro c d _ _ hdS hdT
      cases hdS hdT
  le_trans S T U hST hTU := by
    constructor
    · intro c hc
      exact hTU.mem_of_mem c (hST.mem_of_mem c hc)
    · intro c hS hU
      rw [hST.get_eq_get c hS (hST.mem_of_mem c hS), hTU.get_eq_get c (hST.mem_of_mem c hS) hU]
    · intro c d hcS hcU hdS hdU
      by_cases hdT : d ∈ T
      · rw [← hTU.get_eq_get c (hST.mem_of_mem c hcS) hcU, ← hTU.get_eq_get d hdT hdU]
        exact hST.get_lt_get c d hcS (hST.mem_of_mem c hcS) hdS hdT
      · exact hTU.get_lt_get c d (hST.mem_of_mem c hcS) hcU hdT hdU
  le_antisymm S T hST hTS := by
    ext c hS hT
    · constructor
      · exact hST.mem_of_mem c
      · exact hTS.mem_of_mem c
    · exact hST.get_eq_get c hS hT

theorem smul_le_smul {S T : OrdSupport β} (h : S ≤ T) (ρ : Allowable β) : ρ • S ≤ ρ • T := by
  constructor
  · intro c
    exact h.mem_of_mem (ρ⁻¹ • c)
  · intro c
    exact h.get_eq_get (ρ⁻¹ • c)
  · intro c d
    exact h.get_lt_get (ρ⁻¹ • c) (ρ⁻¹ • d)

theorem smul_le_iff_le_inv {S T : OrdSupport β} (ρ : Allowable β) : S ≤ ρ⁻¹ • T ↔ ρ • S ≤ T := by
  constructor
  · intro h
    have := smul_le_smul h ρ
    rw [smul_inv_smul] at this
    exact this
  · intro h
    have := smul_le_smul h ρ⁻¹
    rw [inv_smul_smul] at this
    exact this

theorem _root_.PFun.image_dom {α β : Type _} (f : α →. β) :
    f.image f.Dom = f.ran := by
  ext x
  simp only [PFun.mem_image, PFun.ran, PFun.mem_dom, mem_setOf_eq]
  constructor
  · rintro ⟨y, _, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, ⟨x, hy⟩, hy⟩

theorem le_invImage_cof {α β : Type _} {c : Cardinal} (r : α → α → Prop) (f : β → α)
    [inst : IsWellOrder α r] [IsWellOrder β (InvImage r f)]
    (hf : Unbounded r (Set.range f)) (hc : c ≤ (Ordinal.type r).cof) :
    c ≤ (Ordinal.type (InvImage r f)).cof := by
  rw [Ordinal.le_cof_type] at hc ⊢
  intro S hS
  refine (hc (f '' S) ?_).trans Cardinal.mk_image_le
  intro a
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf a
  obtain ⟨c, hc₁, hc₂⟩ := hS b
  refine ⟨f c, ⟨c, hc₁, rfl⟩, ?_⟩
  intro h
  rw [InvImage] at hc₂
  refine hc₂ ?_
  have := inst.trichotomous (f b) a
  simp only [hb, false_or] at this
  obtain (this | this) := this
  · subst this
    exact h
  · exact inst.trans _ _ _ h this

theorem unbounded_of_injective {α β : Type _} (r : α → α → Prop) (f : β → α)
    [IsWellOrder α r] (hα : Ordinal.type r = (#α).ord) (hαβ : #α = #β) (hf : Function.Injective f) :
    Unbounded r (Set.range f) := by
  rw [← not_bounded_iff]
  rintro ⟨x, hx⟩
  have : #{y | r y x} < #α := Cardinal.card_typein_lt r x hα.symm
  rw [lt_iff_not_le] at this
  refine this ?_
  rw [hαβ]
  refine ⟨⟨fun y => ⟨f y, hx _ ⟨_, rfl⟩⟩, ?_⟩⟩
  intro y z h
  simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq] at h
  exact hf h

theorem unbounded_sumAtomNearLitter_pos :
    Unbounded (· < ·) (Set.range (pos : Atom ⊕ NearLitter → μ)) := by
  refine unbounded_of_injective _ _ μ_ord ?_ ?_
  · simp only [Cardinal.mk_sum, mk_atom, Cardinal.lift_id, mk_nearLitter,
      Cardinal.add_mk_eq_max, max_self]
  · intro a b
    simp only [EmbeddingLike.apply_eq_iff_eq, imp_self]

theorem mk_setOf_eq (S : OrdSupport β) :
    #{x | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < x} = #μ := by
  letI hwo : IsWellOrder (Atom ⊕ NearLitter) (· < ·) := inferInstance
  letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
  letI hpo : Preorder (Atom ⊕ NearLitter) := hlo.toPreorder
  refine le_antisymm ?_ ?_
  · refine (Cardinal.mk_subtype_le _).trans ?_
    simp only [Cardinal.mk_sum, mk_atom, Cardinal.lift_id, mk_nearLitter, Cardinal.add_mk_eq_max,
      max_self, le_refl]
  have : Small S.cpos.ran
  · have := Small.pFun_image S.dom_small' (f := S.cpos)
    rw [PFun.image_dom] at this
    exact this
  have := Ordinal.lt_cof_type (r := (· < ·)) (this.trans_le ?_)
  swap
  · have hμ := κ_le_μ_ord_cof
    rw [← μ_ord] at hμ
    exact le_invImage_cof _ _ unbounded_sumAtomNearLitter_pos hμ
  obtain ⟨x, hx⟩ := this
  have huniv : Iic x ∪ {y | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < y} = univ
  · simp only [eq_univ_iff_forall, mem_union, or_iff_not_imp_left, mem_Iic, not_le]
    rintro y hy d hd
    exact (hx _ ⟨d, hd, rfl⟩).trans hy
  by_contra' h
  have := Cardinal.mk_union_le (Iic x) {y | ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < y}
  have := this.trans_lt (Cardinal.add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le ?_ h)
  swap
  · refine lt_of_le_of_lt ?_ (card_Iic_lt (pos x))
    refine ⟨⟨fun y => ⟨pos y.val, ?_⟩, ?_⟩⟩
    · rw [mem_Iic]
      show pos y.val ≤ pos x
      have : _ = _ ∨ _ < _ := y.prop
      rw [le_iff_eq_or_lt, EmbeddingLike.apply_eq_iff_eq]
      exact this
    · intro x y h
      simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Subtype.coe_inj.mp h
  simp only [huniv, Cardinal.mk_univ, Cardinal.mk_sum, mk_atom, Cardinal.lift_id, mk_nearLitter,
    Cardinal.add_mk_eq_max, max_self, lt_self_iff_false] at this

theorem embedAfter_nonempty (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s) :
    Nonempty (s ↪ {x // ∀ d, ∀ hd : d ∈ S, (S.cpos d).get hd < x}) :=
  (le_of_lt hs).trans (κ_le_μ.trans (mk_setOf_eq S).symm.le)

noncomputable def embedAfter (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (c : SupportCondition β) (hc : c ∈ s) :
    Atom ⊕ NearLitter :=
  (embedAfter_nonempty S s hs).some ⟨c, hc⟩

theorem embedAfter_injective (S : OrdSupport β) (s : Set (SupportCondition β))
    (hs : Small s) (c d : SupportCondition β) (hc : c ∈ s) (hd : d ∈ s)
    (hcd : S.embedAfter s hs c hc = S.embedAfter s hs d hd) :
    c = d := by
  have := (embedAfter_nonempty S s hs).some.injective (Subtype.coe_injective hcd)
  rw [Subtype.mk.injEq] at this
  exact this

theorem lt_embedAfter (S : OrdSupport β) (s : Set (SupportCondition β))
    (hs : Small s) (c d : SupportCondition β) (hc : c ∈ S) (hd : d ∈ s) :
    (S.cpos c).get hc < S.embedAfter s hs d hd :=
  ((embedAfter_nonempty S s hs).some ⟨d, hd⟩).prop c hc

open scoped Classical in
/-- Add some extra support conditions to the end of an ordered support. -/
noncomputable def extend (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s) :
    OrdSupport β where
  cpos c := ⟨c ∈ S ∨ c ∈ s, fun h =>
    if hc : c ∈ S then
      (S.cpos c).get hc
    else
      S.embedAfter s hs c (or_iff_not_imp_left.mp h hc)⟩
  injective := by
    letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
    letI hpo : Preorder (Atom ⊕ NearLitter) := hlo.toPreorder
    rintro ⟨A, x⟩ ⟨_, y⟩ hc hd rfl h
    simp only at hc hd h
    split_ifs at h with h₁ h₂ h₂
    · exact S.injective _ _ _ _ rfl h
    · have := lt_embedAfter S s hs _ _ h₁ (or_iff_not_imp_left.mp hd h₂)
      rw [h] at this
      cases this.false
    · have := lt_embedAfter S s hs _ _ h₂ (or_iff_not_imp_left.mp hc h₁)
      rw [h] at this
      cases this.false
    · exact S.embedAfter_injective s hs _ _
        (or_iff_not_imp_left.mp hc h₁) (or_iff_not_imp_left.mp hd h₂) h
  dom_small' := Small.union S.dom_small hs

/-- An extended support specialises the original. -/
theorem le_extend (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s) :
    S ≤ S.extend s hs where
  mem_of_mem c := Or.inl
  get_eq_get _ _ _ := by
    dsimp only [extend]
    rw [dif_pos]
  get_lt_get c d hc _ hdS hds := by
    dsimp only [extend]
    rw [dif_pos hc, dif_neg hdS]
    exact S.lt_embedAfter s hs c d hc (or_iff_not_imp_left.mp hds hdS)

theorem mem_extend_iff (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (c : SupportCondition β) :
    c ∈ S.extend s hs ↔ c ∈ S ∨ c ∈ s :=
  Iff.rfl

end OrdSupport

end ConNF
