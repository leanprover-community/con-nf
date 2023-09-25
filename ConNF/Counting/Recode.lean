import ConNF.Structural.Pretangle
import ConNF.Counting.OrdSupportOrbit
import ConNF.Counting.CodingFunctionEquiv

/-!
# Raising supports to higher levels
-/

open MulAction Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions]

class CountingAssumptions (α : Λ) [BasePositions] extends FoaAssumptions α where
  toPretangle (β : IicBot α) : Tangle β → Pretangle β
  toPretangle_smul (β : IicBot α) (ρ : Allowable β) (t : Tangle β) :
    toPretangle β (ρ • t) = ρ • toPretangle β t
  /-- Tangles contain only tangles. -/
  eq_toPretangle_of_mem (β : Iic α) (γ : IicBot α) (h : γ < β) (t₁ : Tangle β) (t₂ : Pretangle γ) :
    t₂ ∈ Pretangle.ofCoe (toPretangle β t₁) γ h → ∃ t₂' : Tangle γ, t₂ = toPretangle γ t₂'
  /-- Tangles are extensional at every proper level `γ < β`. -/
  toPretangle_ext (β γ : Iic α) (h : γ < β) (t₁ t₂ : Tangle β) :
    (∀ t : Pretangle γ,
      t ∈ Pretangle.ofCoe (toPretangle β t₁) γ (coe_lt_coe.mpr h) ↔
      t ∈ Pretangle.ofCoe (toPretangle β t₂) γ (coe_lt_coe.mpr h)) →
    t₁ = t₂
  /-- Any `γ`-tangle can be treated as a singleton at level `β` if `γ < β`. -/
  singleton (β : Iic α) (γ : IicBot α) (h : γ < β) (t : Tangle γ) : Tangle β
  singleton_toPretangle (β : Iic α) (γ : IicBot α) (h : γ < β) (t : Tangle γ) :
    Pretangle.ofCoe (toPretangle β (singleton β γ h t)) γ h = {toPretangle γ t}

export CountingAssumptions (toPretangle toPretangle_smul eq_toPretangle_of_mem toPretangle_ext
  singleton singleton_toPretangle)

variable [CountingAssumptions α] {β : Iio α}

theorem singleton_smul (β : Iic α) (γ : Iic α) (h : (γ : IicBot α) < β) (t : Tangle γ)
    (ρ : Allowable β) :
    ρ • singleton β γ h t = singleton β γ h (Allowable.comp (Hom.toPath h) ρ • t) := by
  refine toPretangle_ext β γ ?_ _ _ ?_
  · simp only [Subtype.mk_lt_mk, coe_lt_coe, Subtype.coe_lt_coe] at h
    exact h
  intro u
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    singleton_toPretangle, singleton_toPretangle, smul_set_singleton,
    mem_singleton_iff, mem_singleton_iff, toPretangle_smul, Allowable.toStructPerm_smul,
    Allowable.toStructPerm_comp]

def top (α : Λ) : Iic α := ⟨α, by simp only [mem_Iic, le_refl]⟩

def raiseIndex (A : ExtendedIndex (β : TypeIndex)) : ExtendedIndex (top α) :=
  (Hom.toPath (show β < top α from Iio.lt β)).comp A

def raise (c : SupportCondition β) : SupportCondition (top α) :=
  ⟨raiseIndex c.path, c.value⟩

@[simp]
theorem raise_path (c : SupportCondition β) : (raise c).path = raiseIndex c.path := rfl

@[simp]
theorem raise_value (c : SupportCondition β) : (raise c).value = c.value := rfl

theorem smul_raise_eq_iff (c : SupportCondition β) (ρ : Allowable (top α)) :
    ρ • raise c = raise c ↔
    Allowable.comp (Hom.toPath
      (show (β : IicBot α) < top α from coe_lt_coe.mpr β.prop)) ρ • c = c := by
  obtain ⟨A, x⟩ := c
  rw [raise, Allowable.smul_supportCondition, Allowable.smul_supportCondition]
  simp only [raise_path, raise_value, SupportCondition.mk.injEq, true_and]
  rw [Allowable.toStructPerm_comp (Hom.toPath
      (show (β : IicBot α) < top α from coe_lt_coe.mpr β.prop)),
    Tree.comp_apply,
    raiseIndex]

/-- A support for a `β`-tangle, expressed as a set of `α`-support conditions. -/
noncomputable def raisedSupport (t : Tangle (top α)) (u : Tangle β) :
    OrdSupport (top α) :=
  (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small).extend
    (reduction α (raise '' (reducedSupport α u).carrier))
    (reduction_small _ (Small.image (reduction_small α (designatedSupport u).small)))

/-- A set `s` of `β`-pretangles *appears* at level `α` if it occurs as the `β`-extension of some
`α`-tangle. -/
def Appears (s : Set (Pretangle β)) : Prop :=
  ∃ t : Tangle (top α),
    s = Pretangle.ofCoe (toPretangle (top α : IicBot α) t) β (coe_lt_coe.mpr β.prop)

/-- Convert a set of `β`-tangles to the (unique) `α`-tangle with that `β`-extension,
if it exists. -/
noncomputable def toTangle (s : Set (Pretangle β)) (h : Appears s) : Tangle (top α) :=
  h.choose

theorem toPretangle_toTangle (s : Set (Pretangle β)) (h : Appears s) :
    s = Pretangle.ofCoe (toPretangle (top α : IicBot α) (toTangle s h)) β (coe_lt_coe.mpr β.prop) :=
  h.choose_spec

def AppearsRaised (β : Iio α)
    (cs : Set (CodingClass (top α))) (U : OrdSupportClass (top α)) : Prop :=
  Appears {u | ∃ c ∈ cs, ∃ V ≥ U, ∃ hV : V ∈ c,
    u ∈ Pretangle.ofCoe
      (toPretangle (top α : IicBot α) (c.decode V hV))
      β (coe_lt_coe.mpr β.prop)}

noncomputable def decodeRaised (cs : Set (CodingClass (top α)))
    (U : OrdSupportClass (top α)) (hU : AppearsRaised β cs U) : Tangle (top α) :=
  hU.choose

/-!
We now aim to show that `decodeRaised` is a coding function.
-/

theorem decodeRaised_spec (cs : Set (CodingClass (top α)))
    (U : OrdSupportClass (top α)) (hU : AppearsRaised β cs U) :
    Pretangle.ofCoe (toPretangle (top α : IicBot α) (decodeRaised cs U hU))
      β (coe_lt_coe.mpr β.prop) =
    {u | ∃ c ∈ cs, ∃ V ≥ U, ∃ hV : V ∈ c,
      u ∈ Pretangle.ofCoe
        (toPretangle (top α : IicBot α) (c.decode V hV))
        β (coe_lt_coe.mpr β.prop)} :=
  hU.choose_spec.symm

theorem appearsRaised_smul {β : Iio α} {cs : Set (CodingClass (top α))}
    (U : OrdSupportClass (top α)) (hU : AppearsRaised β cs U) (ρ : Allowable (top α)) :
    AppearsRaised β cs (ρ • U) := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨ρ • t, ?_⟩
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul, ← ht]
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro c hc V hUV hVc hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr β.prop)) (Allowable.toStructPerm ρ))⁻¹ • u,
      ?_, by simp only [smul_inv_smul]⟩
    refine ⟨c, hc, ρ⁻¹ • V, by rwa [OrdSupportClass.smul_le_iff_le_inv],
      CodingClass.smul_mem _ hVc, ?_⟩
    rw [CodingClass.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, map_inv, Tree.comp_inv, smul_mem_smul_set_iff]
    exact hu
  · simp only [ge_iff_le, mem_setOf_eq]
    rintro ⟨u, ⟨c, hc, V, hUV, hVc, hu⟩, rfl⟩
    refine ⟨c, hc, ρ • V, OrdSupportClass.smul_le_smul hUV ρ, CodingClass.smul_mem _ hVc, ?_⟩
    rw [CodingClass.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, smul_mem_smul_set_iff]
    exact hu

theorem decodeRaised_smul {β : Iio α} {cs : Set (CodingClass (top α))}
    (U : OrdSupportClass (top α)) (hU : AppearsRaised β cs U) (ρ : Allowable (top α)) :
    decodeRaised cs (ρ • U) (appearsRaised_smul U hU ρ) = ρ • decodeRaised cs U hU := by
  refine CountingAssumptions.toPretangle_ext (top α) β β.prop _ _ ?_
  intro u
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    decodeRaised_spec, decodeRaised_spec]
  -- TODO: Unify this proof with the previous by extracting a lemma.
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro c hc V hUV hVc hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr β.prop)) (Allowable.toStructPerm ρ))⁻¹ • u,
      ?_, by simp only [smul_inv_smul]⟩
    refine ⟨c, hc, ρ⁻¹ • V, by rwa [OrdSupportClass.smul_le_iff_le_inv],
      CodingClass.smul_mem _ hVc, ?_⟩
    rw [CodingClass.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, map_inv, Tree.comp_inv, smul_mem_smul_set_iff]
    exact hu
  · simp only [ge_iff_le, mem_setOf_eq]
    rintro ⟨u, ⟨c, hc, V, hUV, hVc, hu⟩, rfl⟩
    refine ⟨c, hc, ρ • V, OrdSupportClass.smul_le_smul hUV ρ, CodingClass.smul_mem _ hVc, ?_⟩
    rw [CodingClass.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, smul_mem_smul_set_iff]
    exact hu

/-- The tangles in the `β`-extension of a given `α`-tangle. -/
def tangleExtension (β : Iio α) (t : Tangle (top α)) : Set (Tangle β) :=
  {u | toPretangle (β : IicBot α) u ∈
    Pretangle.ofCoe (toPretangle (top α : IicBot α) t) β (coe_lt_coe.mpr β.prop)}

theorem raisedSupport_supports (t : Tangle (top α)) (u : Tangle β) :
    Supports (Allowable (top α)) {c | c ∈ raisedSupport t u}
      (singleton (top α) β (coe_lt_coe.mpr β.prop) u) := by
  intro ρ h
  rw [singleton_smul (top α) β]
  refine congr_arg _ ?_
  refine (reducedSupport α u).supports _ ?_
  intro c hc
  rw [← smul_raise_eq_iff]
  refine h ?_
  rw [mem_setOf, raisedSupport, OrdSupport.mem_extend_iff]
  refine Or.inr ⟨?_, hc.2⟩
  exact mem_reflTransClosure_of_mem α _ _ ⟨_, hc, rfl⟩

theorem strongSupport_le_raisedSupport (β : Iio α) (t : Tangle (top α)) (u : Tangle β) :
    OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small ≤
    raisedSupport t u :=
  OrdSupport.le_extend _ _ _

/-- Take the `β`-extension of `t`, treated as a set of `α`-level singletons, and turn them into
coding functions. -/
def raiseSingletons (β : Iio α) (t : Tangle (top α)) : Set (CodingClass (top α)) :=
  (fun u => CodingClass.mk <| CodingFunction.code
    (raisedSupport t u)
    (singleton (top α) β (coe_lt_coe.mpr β.prop) u)
    (raisedSupport_supports t u)) ''
      tangleExtension β t

theorem smul_reducedSupport_eq (β : Iio α) (t : Tangle (top α)) (V : OrdSupportClass (top α))
    (hUV : OrdSupportClass.mk
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small) ≤ V)
    (v : Tangle β) (ρ : Allowable (top α))
    (hV : OrdSupportClass.mk (ρ • raisedSupport t v) = V)
    (c : SupportCondition (top α)) (hc : c ∈ (reducedSupport α t).carrier) : ρ • c = c := by
  subst hV
  obtain ⟨W, hW₁, hW₂⟩ := hUV _ rfl
  have' := OrdSupport.equiv_of_le_equiv
    (OrdSupport.smul_le_smul (strongSupport_le_raisedSupport β t v) ρ)
    hW₂ (OrdSupportClass.eq.mp hW₁.symm)
  have hc' := OrdSupport.cpos_smul_eq_cpos ρ this c hc
  have hS₁ := OrdSupport.smul_eq_of_smul_equiv ρ this
  have hS₂ := OrdSupport.strongSupport_strong (reducedSupport α t) (reducedSupport α t).small ?_ ?_
  · simp_rw [OrdSupport.smul_cpos] at hc'
    rw [hS₂.cpos_get_eq, hS₂.cpos_get_eq] at hc'
    simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply] at hc' ⊢
    rw [← hc', smul_inv_smul]
  · intro c hc
    exact hc.2
  · rintro c d hc hcd ⟨⟨e, he₁, he₂⟩, _⟩
    exact ⟨⟨e, he₁, hcd.to_reflTransGen.trans he₂⟩, hc⟩

theorem raiseSingletons_reducedSupport (β : Iio α) (t : Tangle (top α)) :
    {u | ∃ c ∈ raiseSingletons β t,
      ∃ V ≥ OrdSupportClass.mk
        (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small),
      ∃ hV : V ∈ c,
      u ∈ Pretangle.ofCoe
        (toPretangle (top α : IicBot α) (c.decode V hV)) β (coe_lt_coe.mpr β.prop)} =
    Pretangle.ofCoe (toPretangle (top α : IicBot α) t) β (coe_lt_coe.mpr β.prop) := by
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro c hc V hUV hVc hu
    obtain ⟨v, hv, rfl⟩ := hc
    dsimp only at hVc hu
    obtain ⟨W, hVW, hW⟩ := CodingClass.exists_rep_of_mem_mk hVc
    simp_rw [← hVW, CodingClass.decode_mk_eq_decode hW] at hu
    obtain ⟨ρ, rfl⟩ := hW
    simp_rw [CodingFunction.decode_smul, CodingFunction.code_decode] at hu
    rw [Part.get_some, toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
      singleton_toPretangle, smul_set_singleton, mem_singleton_iff] at hu
    subst hu
    rw [← mem_inv_smul_set_iff, Tree.comp_inv, ← StructPerm.ofCoe_smul, ← map_inv,
      ← Allowable.toStructPerm_smul, ← toPretangle_smul (top α : IicBot α),
      ← (reducedSupport α t).supports _ (smul_reducedSupport_eq β t V hUV v ρ hVW), inv_smul_smul]
    exact hv
  · simp only [ge_iff_le, mem_setOf_eq]
    intro hu
    obtain ⟨u, rfl⟩ := eq_toPretangle_of_mem (top α) β (coe_lt_coe.mpr β.prop) t u hu
    refine ⟨_, ⟨u, hu, rfl⟩, OrdSupportClass.mk (raisedSupport t u), ?_⟩
    refine ⟨?_, CodingClass.mk_mem_mk_of_mem (CodingFunction.mem_code_self), ?_⟩
    · have := strongSupport_le_raisedSupport β t u
      intro S hS
      sorry
    · simp only [CodingFunction.mem_code_self, CodingClass.decode_mk_eq_decode,
        CodingFunction.code_decode, Part.get_some]
      rw [singleton_toPretangle, mem_singleton_iff]

theorem appearsRaised_raiseSingletons (β : Iio α) (t : Tangle (top α)) :
    AppearsRaised β (raiseSingletons β t)
      (OrdSupportClass.mk
        (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small)) :=
  ⟨t, raiseSingletons_reducedSupport β t⟩

theorem decodeRaised_raiseSingletons (β : Iio α) (t : Tangle (top α)) :
    decodeRaised (raiseSingletons β t)
      (OrdSupportClass.mk
        (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small))
      (appearsRaised_raiseSingletons β t) = t := by
  refine toPretangle_ext (top α) β β.prop _ _ ?_
  intro u
  rw [decodeRaised_spec, raiseSingletons_reducedSupport]

noncomputable def raisedCodingFunction (β : Iio α) (cs : Set (CodingClass (top α)))
    (o : OrdSupportOrbit (top α)) (ho : ∀ U ∈ o, AppearsRaised β cs (OrdSupportClass.mk U))
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable (top α)) {c | c ∈ U} (decodeRaised cs (OrdSupportClass.mk U) (ho U hU))) :
    CodingFunction (top α) where
  decode U := ⟨U ∈ o, fun hU => decodeRaised cs (OrdSupportClass.mk U) (ho U hU)⟩
  dom_nonempty := o.nonempty
  supports_decode' := ho'
  dom_iff := by
    intro S T hS
    cases OrdSupportOrbit.eq_mk_of_mem hS
    simp only [OrdSupportOrbit.mem_mk_iff, mem_orbit_iff, eq_comm]
  decode_smul' := by
    intro S ρ h₁ h₂
    simp only [OrdSupportClass.smul_mk]
    rw [decodeRaised_smul]

theorem decode_raisedCodingFunction (β : Iio α) (cs : Set (CodingClass (top α)))
    (o : OrdSupportOrbit (top α)) (ho : ∀ U ∈ o, AppearsRaised β cs (OrdSupportClass.mk U))
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable (top α)) {c | c ∈ U} (decodeRaised cs (OrdSupportClass.mk U) (ho U hU)))
    (U : OrdSupport (top α)) (hU : U ∈ raisedCodingFunction β cs o ho ho') :
    ((raisedCodingFunction β cs o ho ho').decode U).get hU =
    decodeRaised cs (OrdSupportClass.mk U) (ho U hU) :=
  rfl

theorem mem_raisedCodingFunction_iff (β : Iio α) (cs : Set (CodingClass (top α)))
    (o : OrdSupportOrbit (top α)) (ho : ∀ U ∈ o, AppearsRaised β cs (OrdSupportClass.mk U))
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable (top α)) {c | c ∈ U} (decodeRaised cs (OrdSupportClass.mk U) (ho U hU)))
    (U : OrdSupport (top α)) :
    U ∈ raisedCodingFunction β cs o ho ho' ↔ U ∈ o :=
  Iff.rfl

theorem mk_raisedCodingFunction_congr {β : Iio α} {cs : Set (CodingClass (top α))}
    {o₁ o₂ : OrdSupportOrbit (top α)} {ho₁ ho₁' ho₂ ho₂'}
    (ho : OrdSupportClassOrbit.ofOrbit o₁ = OrdSupportClassOrbit.ofOrbit o₂) :
    CodingClass.mk (raisedCodingFunction β cs o₁ ho₁ ho₁') =
    CodingClass.mk (raisedCodingFunction β cs o₂ ho₂ ho₂') := by
  rw [CodingClass.eq]
  obtain ⟨S, T, hS, hT, hST⟩ := OrdSupportClassOrbit.ofOrbit_eq_ofOrbit ho
  refine ⟨S, hS, T, hT, hST, ?_⟩
  rw [decode_raisedCodingFunction, decode_raisedCodingFunction]
  simp_rw [OrdSupportClass.eq.mpr hST]

noncomputable def raisedCodingClass (β : Iio α) (cs : Set (CodingClass (top α)))
    (o : OrdSupportClassOrbit (top α))
    (ho : ∀ U, U ∈ o → AppearsRaised β cs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable (top α)) {c | c ∈ U} (decodeRaised cs U (ho U hU))) :
    CodingClass (top α) :=
  CodingClass.mk (raisedCodingFunction β cs o.chooseOrbit
    (fun U hU => ho (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU o.ofOrbit_chooseOrbit))
    (fun U hU => ho' (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU o.ofOrbit_chooseOrbit)))

theorem appearsRaised_of_mem_orbit (β : Iio α) (t : Tangle (top α)) (U : OrdSupportClass (top α))
    (hU : U ∈ OrdSupportClassOrbit.mk (OrdSupportClass.mk
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small))) :
    AppearsRaised β (raiseSingletons β t) U := by
  simp only [OrdSupportClassOrbit.mem_mk_iff] at hU
  obtain ⟨ρ, rfl⟩ := hU
  exact appearsRaised_smul _ (appearsRaised_raiseSingletons β t) _

theorem supports_decodeRaised_of_mem_orbit (β : Iio α) (t : Tangle (top α))
    (U : OrdSupportClass (top α))
    (hU : U ∈ OrdSupportClassOrbit.mk (OrdSupportClass.mk
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small))) :
    Supports (Allowable (top α)) {c | c ∈ U}
      (decodeRaised (raiseSingletons β t) U (appearsRaised_of_mem_orbit β t U hU)) := by
  simp only [OrdSupportClassOrbit.mem_mk_iff] at hU
  obtain ⟨ρ₁, rfl⟩ := hU
  intro ρ₂ hρ₂
  rw [decodeRaised_smul _ (appearsRaised_of_mem_orbit β t _ rfl), decodeRaised_raiseSingletons]
  rw [← inv_smul_eq_iff, smul_smul, smul_smul]
  refine (reducedSupport α t).supports _ ?_
  intros c hc
  rw [mul_smul, mul_smul, inv_smul_eq_iff]
  refine hρ₂ ?_
  dsimp only
  rw [mem_setOf_eq, ← OrdSupportClass.smul_mk, OrdSupportClass.mem_mk_iff,
    OrdSupport.smul_mem, inv_smul_smul]
  exact hc

/-- Converts a tangle to a coding class by going via `raisedCodingClass β`. -/
noncomputable def recode (β : Iio α) (t : Tangle (top α)) :
    CodingClass (top α) :=
  raisedCodingClass β (raiseSingletons β t)
    (OrdSupportClassOrbit.mk (OrdSupportClass.mk
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small)))
    (appearsRaised_of_mem_orbit β t)
    (supports_decodeRaised_of_mem_orbit β t)

noncomputable def recodeFunction (β : Iio α) (t : Tangle (top α)) :
    CodingFunction (top α) :=
  raisedCodingFunction β (raiseSingletons β t)
    (OrdSupportOrbit.mk (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small))
    (fun U hU => appearsRaised_of_mem_orbit β t (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU rfl))
    (fun U hU => supports_decodeRaised_of_mem_orbit β t (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU rfl))

theorem decode_recodeFunction (β : Iio α) (t : Tangle (top α)) :
    ((recodeFunction β t).decode _).get rfl = t := by
  unfold recodeFunction
  rw [decode_raisedCodingFunction, decodeRaised_raiseSingletons]

theorem mk_recodeFunction_eq (β : Iio α) (t : Tangle (top α)) :
    CodingClass.mk (recodeFunction β t) = recode β t := by
  rw [recodeFunction, recode, raisedCodingClass, mk_raisedCodingFunction_congr]
  rw [OrdSupportClassOrbit.ofOrbit_mk, OrdSupportClassOrbit.ofOrbit_chooseOrbit]

/-- The `recode` function yields the original coding function on `t`. -/
theorem recode_eq (β : Iio α) (t : Tangle (top α)) :
    recode β t =
    CodingClass.mk (CodingFunction.code
      (OrdSupport.strongSupport (reducedSupport α t).carrier (reducedSupport α t).small) t
      (reducedSupport α t).supports) := by
  rw [← mk_recodeFunction_eq]
  refine congrArg _ ?_
  refine CodingFunction.ext
    (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small) ?_ ?_ ?_
  · rfl
  · exact CodingFunction.mem_code_self
  · simp only [Support.carrier_eq_coe, CodingFunction.code_decode, Part.get_some,
      decode_recodeFunction]

end ConNF
