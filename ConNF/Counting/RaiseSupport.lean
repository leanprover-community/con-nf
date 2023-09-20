import ConNF.Structural.Pretangle
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
    OrdSupport (top α) where
  cpos c := ⟨c ∈ raisedSupportSet S t, fun _ => c.value⟩
  injective := by intros; ext <;> assumption
  dom_small' := raisedSupportSet_small S t hS

-- TODO: New file starting from here.

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
  -- Interestingly enough, from this point on,
  -- the tactic proof of this theorem is syntactically identical to the previous one.
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
def extension (β : Iio α) (t : Tangle (top α)) : Set (Tangle β) :=
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

/-- Take the `β`-extension of `t`, treated as a set of `α`-level singletons, and turn them into
coding functions. -/
def raiseSingletons (β : Iio α) (t : Tangle (top α)) : Set (CodingFunction (top α)) :=
  (fun u => CodingFunction.code
    (raisedSupport (reducedSupport α t) u (reducedSupport α t).small)
    (singleton (top α) β (coe_lt_coe.mpr β.prop) u)
    (raisedSupport_supports (reducedSupport α t) u _)) '' extension β t

end ConNF
