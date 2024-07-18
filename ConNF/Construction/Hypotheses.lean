import ConNF.Fuzz.Hypotheses

/-!
# Hypotheses for constructing tangles

In this file we state the conditions required to generate the `fuzz` maps at all levels below a
given proper type index `α : Λ`. Using these inductive hypotheses we can build the t-sets and
allowable permutations at level `α`. However, with such weak hypotheses (in particular, the lack
of any coherence between type levels) we cannot prove many facts about these new types.

## Main declarations

* `ConNF.ModelDataLt`: The `ModelData` for each `β < α`.
* `ConNF.PositionedTanglesLt`: The `PositionedTangles` for each `β < α`.
* `ConNF.TypedObjectsLt`: The `TypedObjects` for each `β < α`.
* `ConNF.PositionedObjectsLt`: The `PositionedObjects` for each `β < α`.
-/

open Function WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}] [Level]

/-- The `ModelData` for each `β < α`. -/
@[ext]
class ModelDataLt where
  data : ∀ β : Λ, [LtLevel β] → ModelData β

instance ModelDataLt.toModelData [ModelDataLt] :
    ∀ β : TypeIndex, [LtLevel β] → ModelData β
  | ⊥, _ => Bot.modelData
  | (β : Λ), _ => ModelDataLt.data β

/-- The `PositionedTangles` for each `β < α`. -/
@[ext]
class PositionedTanglesLt [ModelDataLt] where
  data : ∀ β : Λ, [LtLevel β] → PositionedTangles β

noncomputable instance PositionedTanglesLt.toPositionedTangles
    [BasePositions] [ModelDataLt] [PositionedTanglesLt] :
    ∀ β : TypeIndex, [LtLevel β] → PositionedTangles β
  | ⊥, _ => Bot.positionedTangles
  | (β : Λ), _ => PositionedTanglesLt.data β

/-- The `TypedObjects` for each `β < α`. -/
abbrev TypedObjectsLt [BasePositions] [ModelDataLt] [PositionedTanglesLt] :=
  ∀ β : Λ, [LtLevel β] → TypedObjects β

/-! We have to give the following things different names in the two places we define them:
here, and in the FOA hypothesis file. -/

def Tangle.set_lt [ModelDataLt] : {β : TypeIndex} → [LtLevel β] → Tangle β → TSet β
  | (β : Λ), _, t => TangleCoe.set t
  | ⊥, _i, a => a

theorem Tangle.set_lt_smul [i : ModelDataLt] {β : TypeIndex} [iβ : LtLevel β]
    (ρ : Allowable β) (t : Tangle β) :
    (ρ • t).set_lt = ρ • t.set_lt := by
  revert i iβ
  change (_ : _) → _
  refine WithBot.recBotCoe ?_ ?_ β
  · intro _ _ ρ t
    rfl
  · intro β _ _ ρ t
    rfl

theorem exists_tangle_lt [i : ModelDataLt] {β : TypeIndex} [iβ : LtLevel β] (t : TSet β) :
    ∃ u : Tangle β, u.set_lt = t := by
  revert i iβ
  change (_ : _) → _
  refine WithBot.recBotCoe ?_ ?_ β
  · intro _ _ t
    exact ⟨t, rfl⟩
  · intro β _ _ t
    obtain ⟨S, hS⟩ := t.has_support
    exact ⟨⟨t, S, hS⟩, rfl⟩

theorem Tangle.ext_lt [i : ModelDataLt] {β : TypeIndex} [iβ : LtLevel β] (t₁ t₂ : Tangle β)
    (hs : t₁.set_lt = t₂.set_lt) (hS : t₁.support = t₂.support) : t₁ = t₂ := by
  revert i iβ t₁ t₂
  change (_ : _) → _
  refine WithBot.recBotCoe ?_ ?_ β
  · intro _ _ t₁ t₂ hs _
    exact hs
  · intro β _ _ t₁ t₂ hs hS
    exact TangleCoe.ext _ _ hs hS

theorem Tangle.smul_set_lt [i : ModelDataLt] {β : TypeIndex} [iβ : LtLevel β]
    (t : Tangle β) (ρ : Allowable β) :
    (ρ • t).set_lt = ρ • t.set_lt := by
  revert i iβ
  change (_ : _) → _
  refine WithBot.recBotCoe ?_ ?_ β <;> intros <;> rfl

theorem Tangle.support_supports_lt [i : ModelDataLt] {β : TypeIndex}
    [iβ : LtLevel β] (t : Tangle β) :
    MulAction.Supports (Allowable β) (t.support : Set (Address β)) t := by
  revert i iβ t
  change (_ : _) → _
  refine WithBot.recBotCoe ?_ ?_ β
  · intro _ _ t ρ h
    simp only [support, Atom.support_carrier, Set.mem_singleton_iff, Allowable.smul_address_eq_iff,
      forall_eq, Sum.smul_inl, Sum.inl.injEq] at h
    exact h
  · intro β _ _ t ρ h
    refine TangleCoe.ext _ _ (TangleCoe.support_supports t ρ h) ?_
    refine Enumeration.ext' rfl ?_
    intro i hi _
    exact h ⟨i, hi, rfl⟩

end ConNF
