import ConNF.Structural.Pretangle
import ConNF.Counting.OrdSupportExtend
import ConNF.Counting.OrdSupportOrbit
import ConNF.Counting.CodingFunction

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
    (χs : Set (CodingFunction β)) (U : OrdSupport β) : Prop :=
  Appears hγ {u | ∃ χ ∈ χs, ∃ V ≥ U, ∃ hV : V ∈ χ,
    u ∈ Pretangle.ofCoe (toPretangle (β : IicBot α) ((χ.decode V).get hV)) γ (coe_lt_coe.mpr hγ)}

noncomputable def decodeRaised (χs : Set (CodingFunction β))
    (U : OrdSupport β) (hU : AppearsRaised hγ χs U) : Tangle β :=
  hU.choose

/-!
We now aim to show that `decodeRaised` is a coding function.
-/

theorem decodeRaised_spec (χs : Set (CodingFunction β))
    (U : OrdSupport β) (hU : AppearsRaised hγ χs U) :
    Pretangle.ofCoe (toPretangle (β : IicBot α) (decodeRaised hγ χs U hU))
      γ (coe_lt_coe.mpr hγ) =
    {u | ∃ χ ∈ χs, ∃ V ≥ U, ∃ hV : V ∈ χ,
      u ∈ Pretangle.ofCoe (toPretangle (β : IicBot α) ((χ.decode V).get hV))
        γ (coe_lt_coe.mpr hγ)} :=
  hU.choose_spec.symm

theorem appearsRaised_smul {χs : Set (CodingFunction β)}
    (U : OrdSupport β) (hU : AppearsRaised hγ χs U) (ρ : Allowable β) :
    AppearsRaised hγ χs (ρ • U) := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨ρ • t, ?_⟩
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul, ← ht]
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr hγ)) (Allowable.toStructPerm ρ))⁻¹ • u,
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

theorem decodeRaised_smul {χs : Set (CodingFunction β)}
    (U : OrdSupport β) (hU : AppearsRaised hγ χs U) (ρ : Allowable β) :
    decodeRaised hγ χs (ρ • U) (appearsRaised_smul hγ U hU ρ) = ρ • decodeRaised hγ χs U hU := by
  refine CountingAssumptions.toPretangle_ext β γ hγ _ _ ?_
  intro u
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    decodeRaised_spec, decodeRaised_spec]
  -- TODO: Unify this proof with the previous by extracting a lemma.
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    refine ⟨(Tree.comp (Hom.toPath (coe_lt_coe.mpr hγ)) (Allowable.toStructPerm ρ))⁻¹ • u,
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
def raiseSingletons (S : OrdSupport β) (t : Tangle β) : Set (CodingFunction β) :=
  (fun u => CodingFunction.code
    (raisedSupport hγ S u)
    (singleton β γ (coe_lt_coe.mpr hγ) u)
    (raisedSupport_supports hγ S u)) ''
      tangleExtension hγ t

theorem smul_reducedSupport_eq (S : OrdSupport β) (v : Tangle γ) (ρ : Allowable β)
    (hUV : S ≤ ρ • raisedSupport hγ S v)
    (c : SupportCondition β) (hc : c ∈ S) : ρ • c = c := by
  have := OrdSupport.eq_of_le (OrdSupport.smul_le_smul (le_raisedSupport hγ S v) ρ) hUV
  exact OrdSupport.smul_eq_of_smul_eq ρ ⟨c, hc⟩ this

theorem raiseSingletons_reducedSupport (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    {u | ∃ χ ∈ raiseSingletons hγ S t,
      ∃ V ≥ S, ∃ hV : V ∈ χ,
      u ∈ Pretangle.ofCoe
        (toPretangle (β : IicBot α) ((χ.decode V).get hV)) γ (coe_lt_coe.mpr hγ)} =
    Pretangle.ofCoe (toPretangle (β : IicBot α) t) γ (coe_lt_coe.mpr hγ) := by
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
    rw [← mem_inv_smul_set_iff, Tree.comp_inv, ← StructPerm.ofCoe_smul, ← map_inv,
      ← Allowable.toStructPerm_smul, ← toPretangle_smul (β : IicBot α),
      ← hSt _ (smul_reducedSupport_eq hγ S v ρ hUV), inv_smul_smul]
    exact hv
  · simp only [ge_iff_le, mem_setOf_eq]
    intro hu
    obtain ⟨u, rfl⟩ := eq_toPretangle_of_mem β γ (coe_lt_coe.mpr hγ) t u hu
    refine ⟨_, ⟨u, hu, rfl⟩, raisedSupport hγ S u, ?_⟩
    refine ⟨le_raisedSupport hγ S u, CodingFunction.mem_code_self, ?_⟩
    simp only [CodingFunction.mem_code_self, CodingFunction.code_decode, Part.get_some]
    rw [singleton_toPretangle, mem_singleton_iff]

theorem appearsRaised_raiseSingletons (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    AppearsRaised hγ (raiseSingletons hγ S t) S :=
  ⟨t, raiseSingletons_reducedSupport hγ S t hSt⟩

theorem decodeRaised_raiseSingletons (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    decodeRaised hγ (raiseSingletons hγ S t) S (appearsRaised_raiseSingletons hγ S t hSt) = t := by
  refine toPretangle_ext β γ hγ _ _ ?_
  intro u
  rw [decodeRaised_spec, raiseSingletons_reducedSupport hγ S t hSt]

noncomputable def raisedCodingFunction (χs : Set (CodingFunction β))
    (o : OrdSupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ χs U (ho U hU))) :
    CodingFunction β where
  decode U := ⟨U ∈ o, fun hU => decodeRaised hγ χs U (ho U hU)⟩
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

theorem decode_raisedCodingFunction (χs : Set (CodingFunction β))
    (o : OrdSupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ χs U (ho U hU)))
    (U : OrdSupport β) (hU : U ∈ raisedCodingFunction hγ χs o ho ho') :
    ((raisedCodingFunction hγ χs o ho ho').decode U).get hU =
    decodeRaised hγ χs U (ho U hU) :=
  rfl

theorem mem_raisedCodingFunction_iff (χs : Set (CodingFunction β))
    (o : OrdSupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ χs U (ho U hU)))
    (U : OrdSupport β) :
    U ∈ raisedCodingFunction hγ χs o ho ho' ↔ U ∈ o :=
  Iff.rfl

theorem appearsRaised_of_mem_orbit (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) (U : OrdSupport β)
    (hU : U ∈ OrdSupportOrbit.mk S) :
    AppearsRaised hγ (raiseSingletons hγ S t) U := by
  simp only [OrdSupportOrbit.mem_mk_iff] at hU
  obtain ⟨ρ, rfl⟩ := hU
  exact appearsRaised_smul hγ _ (appearsRaised_raiseSingletons hγ S t hSt) _

theorem supports_decodeRaised_of_mem_orbit (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) (U : OrdSupport β)
    (hU : U ∈ OrdSupportOrbit.mk S) :
    Supports (Allowable β) {c | c ∈ U}
      (decodeRaised hγ (raiseSingletons hγ S t) U
        (appearsRaised_of_mem_orbit hγ S t hSt U hU)) := by
  simp only [OrdSupportOrbit.mem_mk_iff] at hU
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
  simp only [OrdSupport.smul_mem, mem_setOf_eq, inv_smul_smul]
  exact hc

/-- Converts a tangle to a coding class by going via `raisedCodingFunction γ`. -/
noncomputable def recode (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    CodingFunction β :=
  raisedCodingFunction hγ (raiseSingletons hγ S t)
    (OrdSupportOrbit.mk S)
    (appearsRaised_of_mem_orbit hγ S t hSt)
    (supports_decodeRaised_of_mem_orbit hγ S t hSt)

theorem decode_recode (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    ((recode hγ S t hSt).decode _).get rfl = t := by
  unfold recode
  rw [decode_raisedCodingFunction, decodeRaised_raiseSingletons hγ S t hSt]

/-- The `recode` function yields the original coding function on `t`. -/
theorem recode_eq (S : OrdSupport β) (t : Tangle β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    recode hγ S t hSt = CodingFunction.code S t hSt := by
  refine CodingFunction.ext S ?_ ?_ ?_
  · rfl
  · exact CodingFunction.mem_code_self
  · simp only [Support.carrier_eq_coe, CodingFunction.code_decode, Part.get_some, decode_recode]

end ConNF
