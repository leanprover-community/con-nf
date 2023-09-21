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

/-- A support for a `β`-tangle, expressed as a set of `α`-support conditions.
We also throw in another set of support conditions for convenience later. -/
def raisedSupportSet (S : Set (SupportCondition (top α))) (t : Tangle β) :
    Set (SupportCondition (top α)) :=
  S ∪ reduction α (raise '' (reducedSupport α t).carrier)

theorem raise_reducedSupport_subset (S : Set (SupportCondition (top α))) (t : Tangle β) :
    raise '' (reducedSupport α t).carrier ⊆ raisedSupportSet S t := by
  rintro _ ⟨c, hc, rfl⟩
  exact Or.inr ⟨mem_reflTransClosure_of_mem _ _ _ ⟨_, hc, rfl⟩, hc.2⟩

theorem raisedSupportSet_small (S : Set (SupportCondition (top α))) (t : Tangle β)
    (hS : Small S) : Small (raisedSupportSet S t) :=
  Small.union hS (reduction_small _ (Small.image (reduction_small α (designatedSupport t).small)))

/-- A support for a `β`-tangle, expressed as a set of `α`-support conditions. -/
def raisedSupport (S : Set (SupportCondition (top α))) (t : Tangle β) (hS : Small S) :
    OrdSupport (top α) :=
  OrdSupport.strongSupport (raisedSupportSet S t) (raisedSupportSet_small S t hS)

theorem raisedSupport_strong (S : Set (SupportCondition (top α))) (t : Tangle β)
    (hS : Small S) (hS₁ : ∀ c ∈ S, Reduced c.value)
    (hS₂ : ∀ c d, Reduced c.value → c <[α] d → d ∈ S → c ∈ S) :
    (raisedSupport S t hS).Strong := by
  refine OrdSupport.strongSupport_strong _ _ ?_ ?_
  · rintro c (hc | hc)
    · exact hS₁ c hc
    · exact hc.2
  · rintro c d hc hcd (hd | ⟨⟨e, he₁, he₂⟩, _⟩)
    · exact Or.inl (hS₂ c d hc hcd hd)
    · refine Or.inr ⟨?_, hc⟩
      exact ⟨e, he₁, Relation.ReflTransGen.trans hcd.to_reflTransGen he₂⟩

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

def AppearsRaised (β : Iio α) (χs : Set (CodingFunction (top α))) (U : OrdSupport (top α)) : Prop :=
  Appears {u | ∃ χ ∈ χs, ∃ V ≥ U, ∃ hV : V ∈ χ,
    u ∈ Pretangle.ofCoe
      (toPretangle (top α : IicBot α) ((χ.decode V).get hV))
      β (coe_lt_coe.mpr β.prop)}

noncomputable def decodeRaised (χs : Set (CodingFunction (top α)))
    (U : OrdSupport (top α)) (hU : AppearsRaised β χs U) : Tangle (top α) :=
  hU.choose

/-!
We now aim to show that `decodeRaised` is a coding function.
-/

theorem decodeRaised_spec (χs : Set (CodingFunction (top α)))
    (U : OrdSupport (top α)) (hU : AppearsRaised β χs U) :
    Pretangle.ofCoe (toPretangle (top α : IicBot α) (decodeRaised χs U hU))
      β (coe_lt_coe.mpr β.prop) =
    {u | ∃ χ ∈ χs, ∃ V ≥ U, ∃ hV : V ∈ χ,
      u ∈ Pretangle.ofCoe
        (toPretangle (top α : IicBot α) ((χ.decode V).get hV))
        β (coe_lt_coe.mpr β.prop)} :=
  hU.choose_spec.symm

theorem appearsRaised_smul {β : Iio α} {χs : Set (CodingFunction (top α))} (U : OrdSupport (top α))
    (hU : AppearsRaised β χs U) (ρ : Allowable (top α)) :
    AppearsRaised β χs (ρ • U) := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨ρ • t, ?_⟩
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul, ← ht]
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr β.prop)) (Allowable.toStructPerm ρ))⁻¹ • u,
      ?_, by simp only [smul_inv_smul]⟩
    refine ⟨χ, hχ, ρ⁻¹ • V, by rwa [OrdSupport.smul_le_iff_le_inv],
      CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, map_inv, Tree.comp_inv, smul_mem_smul_set_iff]
    exact hu
  · simp only [ge_iff_le, mem_setOf_eq]
    rintro ⟨u, ⟨χ, hχ, V, hUV, hVχ, hu⟩, rfl⟩
    refine ⟨χ, hχ, ρ • V, OrdSupport.smul_le_smul hUV ρ, CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, smul_mem_smul_set_iff]
    exact hu

theorem decodeRaised_smul {β : Iio α} {χs : Set (CodingFunction (top α))} (U : OrdSupport (top α))
    (hU : AppearsRaised β χs U) (ρ : Allowable (top α)) :
    decodeRaised χs (ρ • U) (appearsRaised_smul U hU ρ) = ρ • decodeRaised χs U hU := by
  refine CountingAssumptions.toPretangle_ext (top α) β β.prop _ _ ?_
  intro t
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    decodeRaised_spec, decodeRaised_spec]
  -- TODO: Unify this proof with the previous by extracting a lemma.
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr β.prop)) (Allowable.toStructPerm ρ))⁻¹ • t,
      ?_, by simp only [smul_inv_smul]⟩
    refine ⟨χ, hχ, ρ⁻¹ • V, by rwa [OrdSupport.smul_le_iff_le_inv],
      CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, map_inv, Tree.comp_inv, smul_mem_smul_set_iff]
    exact hu
  · simp only [ge_iff_le, mem_setOf_eq]
    rintro ⟨u, ⟨χ, hχ, V, hUV, hVχ, hu⟩, rfl⟩
    refine ⟨χ, hχ, ρ • V, OrdSupport.smul_le_smul hUV ρ, CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, smul_mem_smul_set_iff]
    exact hu

/-- The tangles in the `β`-extension of a given `α`-tangle. -/
def tangleExtension (β : Iio α) (t : Tangle (top α)) : Set (Tangle β) :=
  {u | toPretangle (β : IicBot α) u ∈
    Pretangle.ofCoe (toPretangle (top α : IicBot α) t) β (coe_lt_coe.mpr β.prop)}

theorem raisedSupport_supports (S : Set (SupportCondition (top α))) (t : Tangle β) (hS : Small S) :
    Supports (Allowable (top α)) {c | c ∈ raisedSupport S t hS}
      (singleton (top α) β (coe_lt_coe.mpr β.prop) t) := by
  intro ρ h
  rw [singleton_smul (top α) β]
  refine congr_arg _ ?_
  refine (reducedSupport α t).supports _ ?_
  intro c hc
  have := h (raise_reducedSupport_subset S t ⟨c, hc, rfl⟩)
  rw [smul_raise_eq_iff] at this
  exact this

theorem strongSupport_le_raisedSupport (β : Iio α) (t : Tangle (top α)) (u : Tangle β) :
    OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small ≤
    raisedSupport (reducedSupport α t) u (reducedSupport α t).small := by
  constructor
  · intro c hc
    exact Or.inl hc
  · intros
    rfl

/-- Take the `β`-extension of `t`, treated as a set of `α`-level singletons, and turn them into
coding functions. -/
def raiseSingletons (β : Iio α) (t : Tangle (top α)) : Set (CodingFunction (top α)) :=
  (fun u => CodingFunction.code
    (raisedSupport (reducedSupport α t) u (reducedSupport α t).small)
    (singleton (top α) β (coe_lt_coe.mpr β.prop) u)
    (raisedSupport_supports (reducedSupport α t) u _)) '' tangleExtension β t

-- TODO: Move next two lemmas.

theorem reduced_of_mem_reducedSupport {β : Iic α} {t : Tangle β}
    (c : SupportCondition β) (hc : c ∈ reducedSupport α t) :
    Reduced c.value :=
  hc.2

theorem mem_reducedSupport_of_transConstrains_mem_reducedSupport {β : Iic α} {t : Tangle β}
    (c d : SupportCondition β)
    (hc : Reduced c.value) (hcd : c <[α] d) (hd : d ∈ reducedSupport α t) :
    c ∈ reducedSupport α t := by
  obtain ⟨e, he₁, he₂⟩ := hd.1
  exact ⟨⟨e, he₁, Relation.ReflTransGen.trans hcd.to_reflTransGen he₂⟩, hc⟩

theorem raiseSingletons_reducedSupport (β : Iio α) (t : Tangle (top α)) :
    {u | ∃ χ ∈ raiseSingletons β t,
      ∃ V ≥ OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small,
      ∃ hV : V ∈ χ,
      u ∈ Pretangle.ofCoe
        (toPretangle (top α : IicBot α) ((χ.decode V).get hV))
        β (coe_lt_coe.mpr β.prop)} =
    Pretangle.ofCoe (toPretangle (top α : IicBot α) t) β (coe_lt_coe.mpr β.prop) := by
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    obtain ⟨v, hv, rfl⟩ := hχ
    rw [CodingFunction.mem_code] at hVχ
    obtain ⟨ρ, rfl⟩ := hVχ
    simp_rw [CodingFunction.decode_smul, CodingFunction.code_decode] at hu
    rw [Part.get_some, toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
      singleton_toPretangle, smul_set_singleton, mem_singleton_iff] at hu
    subst hu
    suffices : ρ • t = t
    · rw [← mem_inv_smul_set_iff, Tree.comp_inv, ← StructPerm.ofCoe_smul, ← map_inv,
        ← Allowable.toStructPerm_smul, ← toPretangle_smul (top α : IicBot α), ← this, inv_smul_smul]
      exact hv
    refine (reducedSupport α t).supports _ ?_
    intro c hc
    have := hUV.get_eq_get _ hc (hUV.mem_of_mem _ hc)
    simp only [OrdSupport.smul_cpos] at this
    rw [OrdSupport.Strong.cpos_get_eq, OrdSupport.Strong.cpos_get_eq] at this
    · rw [Allowable.smul_supportCondition, this, Allowable.smul_supportCondition]
      simp only [map_inv, Tree.inv_apply, smul_inv_smul]
    · exact raisedSupport_strong _ _ _
        reduced_of_mem_reducedSupport mem_reducedSupport_of_transConstrains_mem_reducedSupport
    · exact OrdSupport.strongSupport_strong _ _
        reduced_of_mem_reducedSupport mem_reducedSupport_of_transConstrains_mem_reducedSupport
  · simp only [ge_iff_le, mem_setOf_eq]
    intro hu
    obtain ⟨u, rfl⟩ := eq_toPretangle_of_mem (top α) β (coe_lt_coe.mpr β.prop) t u hu
    refine ⟨_, ⟨u, hu, rfl⟩, (raisedSupport (reducedSupport α t) u (reducedSupport α t).small), ?_⟩
    refine ⟨strongSupport_le_raisedSupport β t u, CodingFunction.mem_code_self, ?_⟩
    simp only [CodingFunction.code_decode]
    rw [Part.get_some, singleton_toPretangle, mem_singleton_iff]

theorem appearsRaised_raiseSingletons (β : Iio α) (t : Tangle (top α)) :
    AppearsRaised β (raiseSingletons β t)
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small) :=
  ⟨t, raiseSingletons_reducedSupport β t⟩

theorem decodeRaised_raiseSingletons (β : Iio α) (t : Tangle (top α)) :
    decodeRaised (raiseSingletons β t)
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small)
      (appearsRaised_raiseSingletons β t) = t := by
  refine toPretangle_ext (top α) β β.prop _ _ ?_
  intro u
  rw [decodeRaised_spec, raiseSingletons_reducedSupport]

noncomputable def raisedCodingFunction (β : Iio α) (χs : Set (CodingFunction (top α)))
    (o : OrdSupportOrbit (top α)) (ho : ∀ U ∈ o, AppearsRaised β χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable (top α)) {c | c ∈ U} (decodeRaised χs U (ho U hU))) :
    CodingFunction (top α) where
  decode U := ⟨U ∈ o, fun hU => decodeRaised χs U (ho U hU)⟩
  dom_nonempty := o.nonempty
  supports_decode' := ho'
  dom_iff := by
    intro S T hS
    cases OrdSupportOrbit.eq_mk_of_mem hS
    simp only [OrdSupportOrbit.mem_mk_iff, mem_orbit_iff, eq_comm]
  decode_smul' := by
    intro S ρ h₁ h₂
    dsimp only
    rw [decodeRaised_smul]

theorem decode_raisedCodingFunction (β : Iio α) (χs : Set (CodingFunction (top α)))
    (o : OrdSupportOrbit (top α)) (ho : ∀ U ∈ o, AppearsRaised β χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable (top α)) {c | c ∈ U} (decodeRaised χs U (ho U hU)))
    (U : OrdSupport (top α)) (hU : U ∈ raisedCodingFunction β χs o ho ho') :
    ((raisedCodingFunction β χs o ho ho').decode U).get hU = decodeRaised χs U (ho U hU) :=
  rfl

theorem mem_raisedCodingFunction_iff (β : Iio α) (χs : Set (CodingFunction (top α)))
    (o : OrdSupportOrbit (top α)) (ho : ∀ U ∈ o, AppearsRaised β χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable (top α)) {c | c ∈ U} (decodeRaised χs U (ho U hU)))
    (U : OrdSupport (top α)) :
    U ∈ raisedCodingFunction β χs o ho ho' ↔ U ∈ o :=
  Iff.rfl

theorem appearsRaised_of_mem_orbit (β : Iio α) (t : Tangle (top α)) (U : OrdSupport (top α))
    (hU : U ∈ OrdSupportOrbit.mk
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small)) :
    AppearsRaised β (raiseSingletons β t) U := by
  simp only [OrdSupportOrbit.mem_mk_iff] at hU
  obtain ⟨ρ, rfl⟩ := hU
  exact appearsRaised_smul _ (appearsRaised_raiseSingletons β t) _

theorem supports_decodeRaised_raiseSingletons (β : Iio α) (t : Tangle (top α)) :
    Supports (Allowable (top α)) {c | c ∈ reducedSupport α t}
      (decodeRaised (raiseSingletons β t)
        (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small)
        (appearsRaised_raiseSingletons β t)) := by
  intro ρ h
  rw [← decodeRaised_smul]
  simp_rw [OrdSupport.smul_strongSupport_eq (reducedSupport α t) (reducedSupport α t).small ρ h]

theorem supports_decodeRaised_of_mem_orbit (β : Iio α) (t : Tangle (top α)) (U : OrdSupport (top α))
    (hU : U ∈ OrdSupportOrbit.mk
      (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small)) :
    Supports (Allowable (top α)) {c | c ∈ U}
      (decodeRaised (raiseSingletons β t) U (appearsRaised_of_mem_orbit β t U hU)) := by
  simp only [OrdSupportOrbit.mem_mk_iff] at hU
  obtain ⟨ρ, rfl⟩ := hU
  rw [decodeRaised_smul _ (appearsRaised_raiseSingletons β t) ρ]
  intro ρ' h
  have := supports_decodeRaised_raiseSingletons β t (ρ⁻¹ * ρ' * ρ) ?_
  · rw [mul_smul, mul_smul, inv_smul_eq_iff] at this
    exact this
  · intro c hc
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
    refine h ⟨?_, ?_⟩
    · rw [inv_smul_smul]
      exact hc.1
    · rw [inv_smul_smul]
      exact hc.2

/-- Converts a tangle to a coding function by going via `raisedCodingFunction β`. -/
noncomputable def recode (β : Iio α) (t : Tangle (top α)) :
    CodingFunction (top α) :=
  raisedCodingFunction β (raiseSingletons β t)
    (OrdSupportOrbit.mk (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small))
    (appearsRaised_of_mem_orbit β t)
    (supports_decodeRaised_of_mem_orbit β t)

theorem mem_recode (β : Iio α) (t : Tangle (top α)) :
    (OrdSupport.strongSupport (reducedSupport α t) (reducedSupport α t).small) ∈ recode β t := by
  rw [recode, mem_raisedCodingFunction_iff]
  rfl

theorem decode_recode (β : Iio α) (t : Tangle (top α)) :
    ((recode β t).decode _).get (mem_recode β t) = t :=
  by simp only [recode, decode_raisedCodingFunction, decodeRaised_raiseSingletons]

/-- The `recode` function yields the original coding function on `t`. -/
theorem recode_eq (β : Iio α) (t : Tangle (top α)) :
    recode β t =
    CodingFunction.code
      (OrdSupport.strongSupport (reducedSupport α t).carrier (reducedSupport α t).small) t
      (reducedSupport α t).supports := by
  refine CodingFunction.ext _ (mem_recode β t) CodingFunction.mem_code_self ?_
  simp only [decode_recode, Support.carrier_eq_coe, CodingFunction.code_decode, Part.get_some]

end ConNF
