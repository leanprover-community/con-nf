import ConNF.Counting.Hypotheses
import ConNF.Counting.CodingFunction
import ConNF.Counting.SupportOrbit
import ConNF.Counting.Twist

/-!
# Raising supports to higher levels
-/

open MulAction Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions]
  {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : (γ : TypeIndex) < β)

def raiseIndex (A : ExtendedIndex (γ : TypeIndex)) : ExtendedIndex β :=
  (Hom.toPath hγ).comp A

def raise (c : Address γ) : Address β :=
  ⟨raiseIndex hγ c.path, c.value⟩

@[simp]
theorem raise_path (c : Address γ) : (raise hγ c).path = raiseIndex hγ c.path := rfl

@[simp]
theorem raise_value (c : Address γ) : (raise hγ c).value = c.value := rfl

theorem raiseIndex_injective {A B : ExtendedIndex γ}
    (h : raiseIndex hγ A = raiseIndex hγ B) : A = B :=
  Path.comp_inj_right.mp h

theorem raise_injective {c d : Address γ} (h : raise hγ c = raise hγ d) : c = d := by
  refine Address.ext _ _ ?_ ?_
  · exact raiseIndex_injective hγ (congr_arg Address.path h)
  · have := congr_arg Address.value h
    exact this

theorem smul_raise_eq_iff (c : Address γ) (ρ : Allowable β) :
    ρ • raise hγ c = raise hγ c ↔
    Allowable.comp (Hom.toPath hγ) ρ • c = c := by
  obtain ⟨A, x⟩ := c
  rw [raise, Allowable.smul_address, Allowable.smul_address]
  simp only [raise_path, raise_value, Address.mk.injEq, true_and]
  rw [Allowable.toStructPerm_comp (Hom.toPath hγ), Tree.comp_apply, raiseIndex]

/-- A set `s` of `γ`-pretangles *appears* at level `α` if it occurs as the `γ`-extension of some
`α`-tangle. -/
def Appears (s : Set (Pretangle γ)) : Prop :=
  ∃ t : TSet β, s = Pretangle.ofCoe (toPretangle t) γ hγ

/-- Convert a set of `γ`-tangles to the (unique) `α`-tangle with that `γ`-extension,
if it exists. -/
noncomputable def toTSet (s : Set (Pretangle γ)) (h : Appears hγ s) : TSet β :=
  h.choose

theorem toPretangle_toTSet (s : Set (Pretangle γ)) (h : Appears hγ s) :
    s = Pretangle.ofCoe (toPretangle (toTSet hγ s h)) γ hγ :=
  h.choose_spec

def AppearsRaised (χs : Set (CodingFunction β)) (U : Support β) : Prop :=
  Appears hγ {u | ∃ χ ∈ χs, ∃ V ≥ U, ∃ hV : V ∈ χ,
    u ∈ Pretangle.ofCoe (toPretangle ((χ.decode V).get hV)) γ hγ}

noncomputable def decodeRaised (χs : Set (CodingFunction β))
    (U : Support β) (hU : AppearsRaised hγ χs U) : TSet β :=
  hU.choose

/-!
We now aim to show that `decodeRaised` is a coding function.
-/

theorem decodeRaised_spec (χs : Set (CodingFunction β))
    (U : Support β) (hU : AppearsRaised hγ χs U) :
    Pretangle.ofCoe (toPretangle (decodeRaised hγ χs U hU)) γ hγ =
    {u | ∃ χ ∈ χs, ∃ V ≥ U, ∃ hV : V ∈ χ,
      u ∈ Pretangle.ofCoe (toPretangle ((χ.decode V).get hV)) γ hγ} :=
  hU.choose_spec.symm

theorem appearsRaised_smul {χs : Set (CodingFunction β)}
    (U : Support β) (hU : AppearsRaised hγ χs U) (ρ : Allowable β) :
    AppearsRaised hγ χs (ρ • U) := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨ρ • t, ?_⟩
  rw [toPretangle_smul, Allowable.toStructPerm_smul, Allowable.toStructPerm_smul,
    StructPerm.ofCoe_smul, ← ht]
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    refine ⟨(Tree.comp (Hom.toPath hγ) (Allowable.toStructPerm ρ))⁻¹ • u,
      ?_, by simp only [smul_inv_smul]⟩
    refine ⟨χ, hχ, ρ⁻¹ • V, by rwa [Enumeration.le_inv_iff_smul_le],
      CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, map_inv, Tree.comp_inv, smul_mem_smul_set_iff]
    exact hu
  · simp only [ge_iff_le, mem_setOf_eq]
    rintro ⟨u, ⟨χ, hχ, V, hUV, hVχ, hu⟩, rfl⟩
    refine ⟨χ, hχ, ρ • V, Enumeration.smul_le_smul hUV ρ, CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, smul_mem_smul_set_iff]
    exact hu

theorem decodeRaised_smul {χs : Set (CodingFunction β)}
    (U : Support β) (hU : AppearsRaised hγ χs U) (ρ : Allowable β) :
    decodeRaised hγ χs (ρ • U) (appearsRaised_smul hγ U hU ρ) = ρ • decodeRaised hγ χs U hU := by
  refine toPretangle.inj' ?_
  refine toPretangle_ext β γ hγ _ _ ?_
  intro u
  simp_rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    decodeRaised_spec]
  -- TODO: Unify this proof with the previous by extracting a lemma.
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    refine ⟨(Tree.comp (Hom.toPath hγ) (Allowable.toStructPerm ρ))⁻¹ • u,
      ?_, by simp only [smul_inv_smul]⟩
    refine ⟨χ, hχ, ρ⁻¹ • V, by rwa [Enumeration.le_inv_iff_smul_le],
      CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, map_inv, Tree.comp_inv, smul_mem_smul_set_iff]
    exact hu
  · simp only [ge_iff_le, mem_setOf_eq]
    rintro ⟨u, ⟨χ, hχ, V, hUV, hVχ, hu⟩, rfl⟩
    refine ⟨χ, hχ, ρ • V, Enumeration.smul_le_smul hUV ρ, CodingFunction.smul_mem _ hVχ, ?_⟩
    rw [CodingFunction.decode_smul, toPretangle_smul, Allowable.toStructPerm_smul,
      StructPerm.ofCoe_smul, smul_mem_smul_set_iff]
    exact hu

/-- The tangles in the `γ`-extension of a given `β`-tangle. -/
def tangleExtension (t : TSet β) : Set (TSet γ) :=
  {u | toPretangle u ∈ Pretangle.ofCoe (toPretangle t) γ hγ}

/-- A support for a `γ`-tangle, expressed as a set of `β`-support conditions. -/
noncomputable def raisedSupport (S : Support β) (u : TSet γ) : Support β :=
  S + u.support.image (raise hγ)

theorem le_raisedSupport (S : Support β) (u : TSet γ) :
    S ≤ raisedSupport hγ S u :=
  Enumeration.le_add _ _

theorem raisedSupport_supports (S : Support β) (u : TSet γ) :
    Supports (Allowable β) (raisedSupport hγ S u : Set (Address β)) (singleton β γ hγ u) := by
  intro ρ h
  rw [singleton_smul β γ]
  refine congr_arg _ ?_
  refine TangleData.TSet.support_supports u _ ?_
  intro c hc
  rw [← smul_raise_eq_iff]
  refine h ?_
  erw [raisedSupport, Enumeration.mem_add_iff]
  exact Or.inr (Enumeration.apply_mem_image hc _)

noncomputable def raiseSingleton (S : Support β) (u : TSet γ) : CodingFunction β :=
  CodingFunction.code
    (raisedSupport hγ S u)
    (singleton β γ hγ u)
    (raisedSupport_supports hγ S u)

def RaisedSingleton : Type u :=
  {χ : CodingFunction β // ∃ S : Support β, ∃ u : TSet γ, χ = raiseSingleton hγ S u}

theorem smul_raise_eq (ρ : Allowable β) (c : Address γ) :
    ρ • raise hγ c = raise hγ (Allowable.comp (Hom.toPath hγ) ρ • c) := by
  simp only [raise, raiseIndex, Allowable.smul_address, Allowable.toStructPerm_comp,
    Tree.comp_apply]

theorem smul_image_raise_eq (ρ : Allowable β) (T : Support γ) :
    ρ • T.image (raise hγ) = (Allowable.comp (Hom.toPath hγ) ρ • T).image (raise hγ) := by
  refine Enumeration.ext' rfl ?_
  intro i hE hF
  dsimp only [Enumeration.smul_f, Enumeration.image_f]
  rw [smul_raise_eq]

/-- Take the `γ`-extension of `t`, treated as a set of `α`-level singletons, and turn them into
coding functions. -/
def raiseSingletons (S : Support β) (t : TSet β) : Set (CodingFunction β) :=
  raiseSingleton hγ S '' tangleExtension hγ t

theorem raiseSingletons_subset_range {S : Support β} {t : TSet β} :
    raiseSingletons hγ S t ⊆
    range (Subtype.val : RaisedSingleton hγ → CodingFunction β) := by
  rintro _ ⟨u, _, rfl⟩
  exact ⟨⟨raiseSingleton hγ S u, ⟨S, u, rfl⟩⟩, rfl⟩

theorem smul_reducedSupport_eq (S : Support β) (v : TSet γ) (ρ : Allowable β)
    (hUV : S ≤ ρ • raisedSupport hγ S v)
    (c : Address β) (hc : c ∈ S) : ρ • c = c := by
  have := Enumeration.eq_of_le (Enumeration.smul_le_smul (le_raisedSupport hγ S v) ρ) hUV
  exact Enumeration.smul_eq_of_smul_eq this hc

theorem raiseSingletons_reducedSupport (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    {u | ∃ χ ∈ raiseSingletons hγ S t,
      ∃ V ≥ S, ∃ hV : V ∈ χ,
      u ∈ Pretangle.ofCoe (toPretangle ((χ.decode V).get hV)) γ hγ} =
    Pretangle.ofCoe (toPretangle t) γ hγ := by
  ext u
  constructor
  · simp only [ge_iff_le, mem_setOf_eq, forall_exists_index, and_imp]
    intro χ hχ V hUV hVχ hu
    obtain ⟨v, hv, rfl⟩ := hχ
    rw [raiseSingleton, CodingFunction.mem_code] at hVχ
    obtain ⟨ρ, rfl⟩ := hVχ
    simp_rw [CodingFunction.decode_smul, raiseSingleton, CodingFunction.code_decode] at hu
    rw [Part.get_some, toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
      singleton_toPretangle, smul_set_singleton, mem_singleton_iff] at hu
    subst hu
    rw [← mem_inv_smul_set_iff, Tree.comp_inv, ← StructPerm.ofCoe_smul, ← map_inv,
      ← Allowable.toStructPerm_smul, ← toPretangle_smul,
      ← hSt _ (smul_reducedSupport_eq hγ S v ρ hUV), inv_smul_smul]
    exact hv
  · simp only [ge_iff_le, mem_setOf_eq]
    intro hu
    obtain ⟨u, rfl⟩ := eq_toPretangle_of_mem β γ hγ t u hu
    refine ⟨_, ⟨u, hu, rfl⟩, raisedSupport hγ S u, ?_⟩
    refine ⟨le_raisedSupport hγ S u, CodingFunction.mem_code_self, ?_⟩
    simp only [raiseSingleton, CodingFunction.mem_code_self, CodingFunction.code_decode,
      Part.get_some]
    rw [singleton_toPretangle, mem_singleton_iff]

theorem appearsRaised_raiseSingletons (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    AppearsRaised hγ (raiseSingletons hγ S t) S :=
  ⟨t, raiseSingletons_reducedSupport hγ S t hSt⟩

theorem decodeRaised_raiseSingletons (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    decodeRaised hγ (raiseSingletons hγ S t) S (appearsRaised_raiseSingletons hγ S t hSt) = t := by
  refine toPretangle.inj' ?_
  refine toPretangle_ext β γ hγ _ _ ?_
  intro u
  rw [decodeRaised_spec, raiseSingletons_reducedSupport hγ S t hSt]

noncomputable def raisedCodingFunction (χs : Set (CodingFunction β))
    (o : SupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ χs U (ho U hU))) :
    CodingFunction β where
  decode U := ⟨U ∈ o, fun hU => decodeRaised hγ χs U (ho U hU)⟩
  dom_nonempty := o.nonempty
  supports_decode' := ho'
  dom_iff := by
    intro S T hS
    cases SupportOrbit.eq_mk_of_mem hS
    simp only [SupportOrbit.mem_mk_iff, mem_orbit_iff, eq_comm]
  decode_smul' := by
    intro S ρ h₁ h₂
    dsimp only
    rw [decodeRaised_smul]

theorem decode_raisedCodingFunction (χs : Set (CodingFunction β))
    (o : SupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ χs U (ho U hU)))
    (U : Support β) (hU : U ∈ raisedCodingFunction hγ χs o ho ho') :
    ((raisedCodingFunction hγ χs o ho ho').decode U).get hU =
    decodeRaised hγ χs U (ho U hU) :=
  rfl

theorem mem_raisedCodingFunction_iff (χs : Set (CodingFunction β))
    (o : SupportOrbit β) (ho : ∀ U ∈ o, AppearsRaised hγ χs U)
    (ho' : ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ χs U (ho U hU)))
    (U : Support β) :
    U ∈ raisedCodingFunction hγ χs o ho ho' ↔ U ∈ o :=
  Iff.rfl

theorem appearsRaised_of_mem_orbit (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) (U : Support β)
    (hU : U ∈ SupportOrbit.mk S) :
    AppearsRaised hγ (raiseSingletons hγ S t) U := by
  simp only [SupportOrbit.mem_mk_iff] at hU
  obtain ⟨ρ, rfl⟩ := hU
  exact appearsRaised_smul hγ _ (appearsRaised_raiseSingletons hγ S t hSt) _

theorem supports_decodeRaised_of_mem_orbit (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) (U : Support β)
    (hU : U ∈ SupportOrbit.mk S) :
    Supports (Allowable β) {c | c ∈ U}
      (decodeRaised hγ (raiseSingletons hγ S t) U
        (appearsRaised_of_mem_orbit hγ S t hSt U hU)) := by
  simp only [SupportOrbit.mem_mk_iff] at hU
  obtain ⟨ρ₁, rfl⟩ := hU
  intro ρ₂ hρ₂
  rw [decodeRaised_smul hγ _ (appearsRaised_of_mem_orbit hγ S t hSt _ rfl),
    decodeRaised_raiseSingletons hγ S t hSt]
  rw [← inv_smul_eq_iff, smul_smul, smul_smul]
  refine hSt _ ?_
  intros c hc
  rw [mul_smul, mul_smul, inv_smul_eq_iff]
  refine hρ₂ ?_
  rw [mem_setOf_eq, Enumeration.smul_mem_smul_iff]
  exact hc

/-- Converts a tangle to a coding class by going via `raisedCodingFunction γ`. -/
noncomputable def recode (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    CodingFunction β :=
  raisedCodingFunction hγ (raiseSingletons hγ S t)
    (SupportOrbit.mk S)
    (appearsRaised_of_mem_orbit hγ S t hSt)
    (supports_decodeRaised_of_mem_orbit hγ S t hSt)

theorem decode_recode (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    ((recode hγ S t hSt).decode _).get rfl = t := by
  unfold recode
  rw [decode_raisedCodingFunction, decodeRaised_raiseSingletons hγ S t hSt]

/-- The `recode` function yields the original coding function on `t`. -/
theorem recode_eq (S : Support β) (t : TSet β)
    (hSt : Supports (Allowable β) {c | c ∈ S} t) :
    recode hγ S t hSt = CodingFunction.code S t hSt := by
  refine CodingFunction.ext S ?_ ?_ ?_
  · rfl
  · exact CodingFunction.mem_code_self
  · simp only [decode_recode, CodingFunction.code_decode, Part.get_some]

end ConNF
