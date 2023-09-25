import ConNF.Structural.Pretangle
import ConNF.Counting.OrdSupportExtend
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

variable [CountingAssumptions α] {β γ : Iic α} (hγ : γ < β)

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

def raiseIndex (A : ExtendedIndex (γ : TypeIndex)) : ExtendedIndex β :=
  (Hom.toPath hγ).comp A

def raise (c : SupportCondition γ) : SupportCondition β :=
  ⟨raiseIndex hγ c.path, c.value⟩

@[simp]
theorem raise_path (c : SupportCondition γ) : (raise hγ c).path = raiseIndex hγ c.path := rfl

@[simp]
theorem raise_value (c : SupportCondition γ) : (raise hγ c).value = c.value := rfl

theorem smul_raise_eq_iff (c : SupportCondition γ) (ρ : Allowable β) :
    ρ • raise hγ c = raise hγ c ↔
    Allowable.comp (Hom.toPath
      (show (γ : IicBot α) < β from coe_lt_coe.mpr hγ)) ρ • c = c := by
  obtain ⟨A, x⟩ := c
  rw [raise, Allowable.smul_supportCondition, Allowable.smul_supportCondition]
  simp only [raise_path, raise_value, SupportCondition.mk.injEq, true_and]
  rw [Allowable.toStructPerm_comp (Hom.toPath
      (show (γ : IicBot α) < β from coe_lt_coe.mpr hγ)),
    Tree.comp_apply,
    raiseIndex]

/-- A set `s` of `γ`-pretangles *appears* at level `α` if it occurs as the `γ`-extension of some
`α`-tangle. -/
def Appears (s : Set (Pretangle γ)) : Prop :=
  ∃ t : Tangle β,
    s = Pretangle.ofCoe (toPretangle (β : IicBot α) t) γ (coe_lt_coe.mpr hγ)

/-- Convert a set of `γ`-tangles to the (unique) `α`-tangle with that `γ`-extension,
if it exists. -/
noncomputable def toTangle (s : Set (Pretangle γ)) (h : Appears hγ s) : Tangle β :=
  h.choose

theorem toPretangle_toTangle (s : Set (Pretangle γ)) (h : Appears hγ s) :
    s = Pretangle.ofCoe (toPretangle (β : IicBot α) (toTangle hγ s h)) γ (coe_lt_coe.mpr hγ) :=
  h.choose_spec

def AppearsRaised
    (cs : Set (CodingClass β)) (U : OrdSupportClass β) : Prop :=
  Appears hγ {u | ∃ c ∈ cs, ∃ V ≥ U, ∃ hV : V ∈ c,
    u ∈ Pretangle.ofCoe
      (toPretangle (β : IicBot α) (c.decode V hV))
      γ (coe_lt_coe.mpr hγ)}

noncomputable def decodeRaised (cs : Set (CodingClass β))
    (U : OrdSupportClass β) (hU : AppearsRaised hγ cs U) : Tangle β :=
  hU.choose

/-!
We now aim to show that `decodeRaised` is a coding function.
-/

theorem decodeRaised_spec (cs : Set (CodingClass β))
    (U : OrdSupportClass β) (hU : AppearsRaised hγ cs U) :
    Pretangle.ofCoe (toPretangle (β : IicBot α) (decodeRaised hγ cs U hU))
      γ (coe_lt_coe.mpr hγ) =
    {u | ∃ c ∈ cs, ∃ V ≥ U, ∃ hV : V ∈ c,
      u ∈ Pretangle.ofCoe
        (toPretangle (β : IicBot α) (c.decode V hV))
        γ (coe_lt_coe.mpr hγ)} :=
  hU.choose_spec.symm

theorem appearsRaised_smul {cs : Set (CodingClass β)}
    (U : OrdSupportClass β) (hU : AppearsRaised hγ cs U) (ρ : Allowable β) :
    AppearsRaised hγ cs (ρ • U) := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨ρ • t, ?_⟩
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul, ← ht]
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro c hc V hUV hVc hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr hγ)) (Allowable.toStructPerm ρ))⁻¹ • u,
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

theorem decodeRaised_smul {cs : Set (CodingClass β)}
    (U : OrdSupportClass β) (hU : AppearsRaised hγ cs U) (ρ : Allowable β) :
    decodeRaised hγ cs (ρ • U) (appearsRaised_smul hγ U hU ρ) = ρ • decodeRaised hγ cs U hU := by
  refine CountingAssumptions.toPretangle_ext β γ hγ _ _ ?_
  intro u
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    decodeRaised_spec, decodeRaised_spec]
  -- TODO: Unify this proof with the previous by extracting a lemma.
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro c hc V hUV hVc hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr hγ)) (Allowable.toStructPerm ρ))⁻¹ • u,
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

/-- The tangles in the `γ`-extension of a given `α`-tangle. -/
def tangleExtension (t : Tangle β) : Set (Tangle γ) :=
  {u | toPretangle (γ : IicBot α) u ∈
    Pretangle.ofCoe (toPretangle (β : IicBot α) t) γ (coe_lt_coe.mpr hγ)}

/-- A support for a `γ`-tangle, expressed as a set of `α`-support conditions. -/
noncomputable def raisedSupport (S : OrdSupport β) (u : Tangle γ) :
    OrdSupport β :=
  S.extend
    (reduction α (raise hγ '' (reducedSupport α u).carrier))
    (reduction_small _ (Small.image (reduction_small α (designatedSupport u).small)))

theorem raisedSupport_supports (S : OrdSupport β) (u : Tangle γ) :
    Supports (Allowable β) {c | c ∈ raisedSupport hγ S u}
      (singleton β γ (coe_lt_coe.mpr hγ) u) := by
  intro ρ h
  rw [singleton_smul β γ]
  refine congr_arg _ ?_
  refine (reducedSupport α u).supports _ ?_
  intro c hc
  rw [← smul_raise_eq_iff]
  refine h ?_
  rw [mem_setOf, raisedSupport, OrdSupport.mem_extend_iff]
  refine Or.inr ⟨?_, hc.2⟩
  exact mem_reflTransClosure_of_mem α _ _ ⟨_, hc, rfl⟩

theorem le_raisedSupport (S : OrdSupport β) (u : Tangle γ) :
    S ≤ raisedSupport hγ S u :=
  OrdSupport.le_extend _ _ _

/-- Take the `γ`-extension of `t`, treated as a set of `α`-level singletons, and turn them into
coding functions. -/
def raiseSingletons (S : OrdSupport β) (t : Tangle β) : Set (CodingClass β) :=
  (fun u => CodingClass.mk <| CodingFunction.code
    (raisedSupport hγ S u)
    (singleton β γ (coe_lt_coe.mpr hγ) u)
    (raisedSupport_supports hγ S u)) ''
      tangleExtension hγ t

theorem smul_reducedSupport_eq (S : OrdSupport β) (V : OrdSupportClass β)
    (hUV : OrdSupportClass.mk S ≤ V)
    (v : Tangle γ) (ρ : Allowable β)
    (hV : OrdSupportClass.mk (ρ • raisedSupport hγ S v) = V)
    (c : SupportCondition β) (hc : c ∈ S) : ρ • c = c := by
  subst hV
  obtain ⟨W, hW₁, hW₂⟩ := hUV _ rfl
  have' := OrdSupport.equiv_of_le_equiv
    (OrdSupport.smul_le_smul (le_raisedSupport hγ S v) ρ)
    hW₂ (OrdSupportClass.eq.mp hW₁.symm)
  have hc' := OrdSupport.cpos_smul_eq_cpos ρ this c hc
  simp_rw [OrdSupport.smul_cpos] at hc'
  simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply] at hc' ⊢
  have := S.injective _ _ _ _ ?_ hc'
  · conv_lhs => rw [← this]
    rw [smul_inv_smul]
  · rfl

theorem raiseSingletons_reducedSupport (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    {u | ∃ c ∈ raiseSingletons hγ S t,
      ∃ V ≥ OrdSupportClass.mk S,
      ∃ hV : V ∈ c,
      u ∈ Pretangle.ofCoe
        (toPretangle (β : IicBot α) (c.decode V hV)) γ (coe_lt_coe.mpr hγ)} =
    Pretangle.ofCoe (toPretangle (β : IicBot α) t) γ (coe_lt_coe.mpr hγ) := by
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
      ← Allowable.toStructPerm_smul, ← toPretangle_smul (β : IicBot α),
      ← hSt _ (smul_reducedSupport_eq hγ S V hUV v ρ hVW), inv_smul_smul]
    exact hv
  · simp only [ge_iff_le, mem_setOf_eq]
    intro hu
    obtain ⟨u, rfl⟩ := eq_toPretangle_of_mem β γ (coe_lt_coe.mpr hγ) t u hu
    refine ⟨_, ⟨u, hu, rfl⟩, OrdSupportClass.mk (raisedSupport hγ S u), ?_⟩
    refine ⟨?_, CodingClass.mk_mem_mk_of_mem (CodingFunction.mem_code_self), ?_⟩
    · intro S hS
      refine ⟨S.extend (reduction α (raise hγ '' (reducedSupport α u).carrier))
        (reduction_small _ (Small.image (reduction_small α (designatedSupport u).small))), ?_, ?_⟩
      · rw [OrdSupportClass.eq] at hS ⊢
        exact OrdSupport.extend_equiv _ _ _ _ hS
      · exact OrdSupport.le_extend _ _ _
    · simp only [CodingFunction.mem_code_self, CodingClass.decode_mk_eq_decode,
        CodingFunction.code_decode, Part.get_some]
      rw [singleton_toPretangle, mem_singleton_iff]

theorem appearsRaised_raiseSingletons (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    AppearsRaised hγ (raiseSingletons hγ S t) (OrdSupportClass.mk S) :=
  ⟨t, raiseSingletons_reducedSupport hγ S t hSt⟩

theorem decodeRaised_raiseSingletons (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    decodeRaised hγ (raiseSingletons hγ S t) (OrdSupportClass.mk S)
      (appearsRaised_raiseSingletons hγ S t hSt) = t := by
  refine toPretangle_ext β γ hγ _ _ ?_
  intro u
  rw [decodeRaised_spec, raiseSingletons_reducedSupport hγ S t hSt]

noncomputable def raisedCodingFunction (cs : Set (CodingClass β))
    (o : OrdSupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ cs (OrdSupportClass.mk U))
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ cs (OrdSupportClass.mk U) (ho U hU))) :
    CodingFunction β where
  decode U := ⟨U ∈ o, fun hU => decodeRaised hγ cs (OrdSupportClass.mk U) (ho U hU)⟩
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

theorem decode_raisedCodingFunction (cs : Set (CodingClass β))
    (o : OrdSupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ cs (OrdSupportClass.mk U))
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ cs (OrdSupportClass.mk U) (ho U hU)))
    (U : OrdSupport β) (hU : U ∈ raisedCodingFunction hγ cs o ho ho') :
    ((raisedCodingFunction hγ cs o ho ho').decode U).get hU =
    decodeRaised hγ cs (OrdSupportClass.mk U) (ho U hU) :=
  rfl

theorem mem_raisedCodingFunction_iff (cs : Set (CodingClass β))
    (o : OrdSupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ cs (OrdSupportClass.mk U))
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ cs (OrdSupportClass.mk U) (ho U hU)))
    (U : OrdSupport β) :
    U ∈ raisedCodingFunction hγ cs o ho ho' ↔ U ∈ o :=
  Iff.rfl

theorem mk_raisedCodingFunction_congr {cs : Set (CodingClass β)}
    {o₁ o₂ : OrdSupportOrbit β} {ho₁ ho₁' ho₂ ho₂'}
    (ho : OrdSupportClassOrbit.ofOrbit o₁ = OrdSupportClassOrbit.ofOrbit o₂) :
    CodingClass.mk (raisedCodingFunction hγ cs o₁ ho₁ ho₁') =
    CodingClass.mk (raisedCodingFunction hγ cs o₂ ho₂ ho₂') := by
  rw [CodingClass.eq]
  obtain ⟨S, T, hS, hT, hST⟩ := OrdSupportClassOrbit.ofOrbit_eq_ofOrbit ho
  refine ⟨S, hS, T, hT, hST, ?_⟩
  rw [decode_raisedCodingFunction, decode_raisedCodingFunction]
  simp_rw [OrdSupportClass.eq.mpr hST]

noncomputable def raisedCodingClass (cs : Set (CodingClass β))
    (o : OrdSupportClassOrbit β)
    (ho : ∀ U, U ∈ o → AppearsRaised hγ cs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ cs U (ho U hU))) :
    CodingClass β :=
  CodingClass.mk (raisedCodingFunction hγ cs o.chooseOrbit
    (fun U hU => ho (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU o.ofOrbit_chooseOrbit))
    (fun U hU => ho' (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU o.ofOrbit_chooseOrbit)))

theorem appearsRaised_of_mem_orbit (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) (U : OrdSupportClass β)
    (hU : U ∈ OrdSupportClassOrbit.mk (OrdSupportClass.mk S)) :
    AppearsRaised hγ (raiseSingletons hγ S t) U := by
  simp only [OrdSupportClassOrbit.mem_mk_iff] at hU
  obtain ⟨ρ, rfl⟩ := hU
  exact appearsRaised_smul hγ _ (appearsRaised_raiseSingletons hγ S t hSt) _

theorem supports_decodeRaised_of_mem_orbit (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) (U : OrdSupportClass β)
    (hU : U ∈ OrdSupportClassOrbit.mk (OrdSupportClass.mk S)) :
    Supports (Allowable β) {c | c ∈ U}
      (decodeRaised hγ (raiseSingletons hγ S t) U
        (appearsRaised_of_mem_orbit hγ S t hSt U hU)) := by
  simp only [OrdSupportClassOrbit.mem_mk_iff] at hU
  obtain ⟨ρ₁, rfl⟩ := hU
  intro ρ₂ hρ₂
  rw [decodeRaised_smul hγ _ (appearsRaised_of_mem_orbit hγ S t hSt _ rfl),
    decodeRaised_raiseSingletons hγ S t hSt]
  rw [← inv_smul_eq_iff, smul_smul, smul_smul]
  refine hSt _ ?_
  intros c hc
  rw [mul_smul, mul_smul, inv_smul_eq_iff]
  refine hρ₂ ?_
  dsimp only
  rw [mem_setOf_eq, ← OrdSupportClass.smul_mk, OrdSupportClass.mem_mk_iff,
    OrdSupport.smul_mem, inv_smul_smul]
  exact hc

/-- Converts a tangle to a coding class by going via `raisedCodingClass γ`. -/
noncomputable def recode (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    CodingClass β :=
  raisedCodingClass hγ (raiseSingletons hγ S t)
    (OrdSupportClassOrbit.mk (OrdSupportClass.mk S))
    (appearsRaised_of_mem_orbit hγ S t hSt)
    (supports_decodeRaised_of_mem_orbit hγ S t hSt)

noncomputable def recodeFunction (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    CodingFunction β :=
  raisedCodingFunction hγ (raiseSingletons hγ S t)
    (OrdSupportOrbit.mk S)
    (fun U hU => appearsRaised_of_mem_orbit hγ S t hSt (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU rfl))
    (fun U hU => supports_decodeRaised_of_mem_orbit hγ S t hSt (OrdSupportClass.mk U)
      (OrdSupportClassOrbit.mk_mem_of_mem_orbit hU rfl))

theorem decode_recodeFunction (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    ((recodeFunction hγ S t hSt).decode _).get rfl = t := by
  unfold recodeFunction
  rw [decode_raisedCodingFunction, decodeRaised_raiseSingletons hγ S t hSt]

theorem mk_recodeFunction_eq (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    CodingClass.mk (recodeFunction hγ S t hSt) = recode hγ S t hSt := by
  rw [recodeFunction, recode, raisedCodingClass, mk_raisedCodingFunction_congr]
  rw [OrdSupportClassOrbit.ofOrbit_mk, OrdSupportClassOrbit.ofOrbit_chooseOrbit]

/-- The `recode` function yields the original coding function on `t`. -/
theorem recode_eq (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    recode hγ S t hSt =
    CodingClass.mk (CodingFunction.code S t hSt) := by
  rw [← mk_recodeFunction_eq]
  refine congrArg _ ?_
  refine CodingFunction.ext S ?_ ?_ ?_
  · rfl
  · exact CodingFunction.mem_code_self
  · simp only [Support.carrier_eq_coe, CodingFunction.code_decode, Part.get_some,
      decode_recodeFunction]

end ConNF
