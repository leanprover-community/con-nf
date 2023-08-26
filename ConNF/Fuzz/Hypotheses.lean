import ConNF.Structural.Support

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `con_nf.core_TangleData`:
* `con_nf.PositionedTangleData`:
* `con_nf.AlmostTangleData`:
* `con_nf.TangleData`: The data for the first phase of the recursion.
-/


open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}]

section DefineTangleData

/-- The motor of the initial recursion. This contains the data of tangles and allowable permutations
for phase 1 of the recursion. -/
class CoreTangleData (α : TypeIndex) where
  (Tangle Allowable : Type u)
  [allowableGroup : Group Allowable]
  allowableToStructPerm : Allowable →* StructPerm α
  [allowableAction : MulAction Allowable Tangle]
  designatedSupport :
    haveI : MulAction Allowable (SupportCondition α) :=
      MulAction.compHom _ allowableToStructPerm
    (t : Tangle) → Support α Allowable t

attribute [instance] CoreTangleData.allowableGroup CoreTangleData.allowableAction

section

variable (α : TypeIndex) [CoreTangleData α]

/-- The type of tangles that we assume were constructed at stage `α`.
Later in the recursion, we will construct this type explicitly, but for now, we will just assume
that it exists.
Fields in `TangleData` give more information about this type. -/
def Tangle : Type u :=
  CoreTangleData.Tangle α

/-- The type of allowable permutations that we assume exists on `α`-tangles. -/
def Allowable : Type u :=
  CoreTangleData.Allowable α

/-- Allowable permutations at level `α` forms a group with respect to function composition. Note
that at this stage in the recursion, we have not established that the allowable permutations on
`α`-tangles are actually (coercible to) functions, so we cannot compose them with the `∘` symbol; we
must instead use group multiplication `*`. -/
instance : Group (Allowable α) :=
  CoreTangleData.allowableGroup

variable {α} {X : Type _} [MulAction (StructPerm α) X]

namespace Allowable

/-- Allowable permutations can be considered a subtype of structural permutations. However, we
cannot write this explicitly in type theory, so instead we assume this monoid homomorphism from
allowable permutations to structural permutations. This can be thought of as an inclusion map that
preserves the group structure. -/
def toStructPerm : Allowable α →* StructPerm α :=
  CoreTangleData.allowableToStructPerm

instance : MulAction (Allowable α) (Tangle α) :=
  CoreTangleData.allowableAction

/-- Allowable permutations act on tangles. This action commutes with certain other operations; the
exact condition are given in `smul_typed_near_litter`. -/
instance : MulAction (Allowable α) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (f : Allowable α) (x : X) : Allowable.toStructPerm f • x = f • x :=
  rfl

end Allowable

/-- For each tangle, we provide a small support for it. This is known as the designated support of
the tangle. -/
def designatedSupport (t : Tangle α) : Support α (Allowable α) t :=
  CoreTangleData.designatedSupport _

end

/-- The motor of the initial recursion. This contains the data of the position function. -/
class PositionedTangleData (α : TypeIndex) [CoreTangleData α] where
  position : Tangle α ↪ μ

export PositionedTangleData (position)

variable (α : Λ) [CoreTangleData α]

/-- The motor of the initial recursion. This contains the data of the injection to all the
information needed for phase 1 of the recursion. -/
class AlmostTangleData where
  typedAtom : Atom ↪ Tangle α
  typedNearLitter : NearLitter ↪ Tangle α
  smul_typedNearLitter :
    ∀ (π : Allowable α) (N), π • typedNearLitter N = typedNearLitter (π • N)

export AlmostTangleData (typedAtom typedNearLitter)

namespace Allowable

variable {α}
variable [AlmostTangleData α]

@[simp]
theorem smul_fst (π : Allowable α) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

@[simp]
theorem coe_smul (π : Allowable α) (N : NearLitter) : ((π • N) : Set Atom) = π • (N : Set Atom) :=
  rfl

/--
The action of allowable permutations on tangles commutes with the `typed_near_litter` function mapping
near-litters to typed near-litters. This is quite clear to see when representing tangles as codes,
but since at this stage tangles are just a type, we have to state this condition explicitly. -/
theorem smul_typedNearLitter (π : Allowable α) (N : NearLitter) :
    π • (typedNearLitter N : Tangle α) = typedNearLitter (π • N) :=
  AlmostTangleData.smul_typedNearLitter _ _

end Allowable

/-- The position of typed atoms and typed near-litters in the position function at any level.
This is part of the `γ = -1` fix. -/
class PositionData where
  typedAtomPosition : Atom ↪ μ
  typedNearLitterPosition : NearLitter ↪ μ
  litter_lt :
    ∀ (L : Litter),
      ∀ a ∈ litterSet L, typedNearLitterPosition L.toNearLitter < typedAtomPosition a
  litter_le_nearLitter :
    ∀ N : NearLitter, typedNearLitterPosition N.fst.toNearLitter ≤ typedNearLitterPosition N
  symmDiff_lt_nearLitter :
    ∀ (N : NearLitter),
      ∀ a ∈ litterSet N.fst ∆ N.snd, typedAtomPosition a < typedNearLitterPosition N

export PositionData (typedAtomPosition typedNearLitterPosition litter_lt litter_le_nearLitter
    symmDiff_lt_nearLitter)

theorem litter_lt_nearLitter [PositionData] (N : NearLitter) (hN : N.fst.toNearLitter ≠ N) :
    typedNearLitterPosition N.fst.toNearLitter < typedNearLitterPosition N :=
  lt_of_le_of_ne (litter_le_nearLitter N) (typedNearLitterPosition.injective.ne hN)

variable [AlmostTangleData α] [PositionedTangleData α] [PositionData]

/-- The motor of the initial recursion. This contains all the information needed for phase 1 of the
recursion. -/
class TangleData : Prop where
  typedAtomPosition_eq : ∀ a : Atom, position (typedAtom a : Tangle α) = typedAtomPosition a
  typedNearLitterPosition_eq :
    ∀ N : NearLitter, position (typedNearLitter N : Tangle α) = typedNearLitterPosition N
  support_le :
    ∀ (t : Tangle α) (c : SupportCondition α),
      c ∈ designatedSupport t → c.fst.elim typedAtomPosition typedNearLitterPosition ≤ position t

/-- An injection from near-litters into level `α` tangles.
These will be explicitly constructed as "typed near-litters", which are codes of the form
`(α, -1, N)` for `N` a near-litter.

Since we haven't assumed anything about the structure of tangles at this level, we can't construct
these typed near-litters explicitly, so we rely on this function instead. In the blueprint, this is
function `j`. -/
add_decl_doc AlmostTangleData.typedNearLitter

/-- For any atom `a`, we can construct an `α`-tangle that has a `-1`-extension that contains exactly
this atom. This is called a typed singleton. In the blueprint, this is the function `k`. -/
add_decl_doc AlmostTangleData.typedAtom

/-- An injection from level `α` tangles into the type `μ`.
Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two tangles,
simply compare their images under this map.

Conditions satisfied by this injection are given in `litter_lt`, `litter_lt_near_litter`,
`symm_diff_lt_near_litter`, and `support_le`. In the blueprint, this is function `ι`. -/
add_decl_doc PositionedTangleData.position

/-- Each typed litter `L` precedes the typed singletons of all of its elements `a ∈ L`. -/
add_decl_doc PositionData.litter_lt

/-- Each near litter `N` which is not a litter comes later than its associated liter `L = N°`. -/
add_decl_doc litter_lt_nearLitter

/-- Each near litter `N` comes after all elements in the symmetric difference `N ∆ N°` (which is
a small set by construction). Note that if `N` is a litter, this condition is vacuously true. -/
add_decl_doc symmDiff_lt_nearLitter

/-- For all tangles `t` that are not typed singletons and not typed litters, `t` comes later than
all of the support conditions in its designated support. That is, if an atom `a` is in the
designated support for `t`, then `t` lies after `a`, and if a near-litter `N` is in the designated
support for `t`, then `t` lies after `N` (under suitable maps to `μ`). -/
add_decl_doc TangleData.support_le

end DefineTangleData

section Instances

variable {α : Λ} (β : Iio α) [CoreTangleData (iioCoe β)]

instance coreVal : CoreTangleData β.val :=
  ‹CoreTangleData β›

instance coreCoeCoe : CoreTangleData (β : Λ) :=
  ‹CoreTangleData β›

section PositionedTangleData

variable [PositionedTangleData (iioCoe β)]

instance positionedVal : PositionedTangleData β.val :=
  ‹PositionedTangleData _›

instance positionedCoeCoe : PositionedTangleData (β : Λ) :=
  ‹PositionedTangleData _›

end PositionedTangleData

variable [AlmostTangleData β]

instance almostVal : AlmostTangleData β.val :=
  ‹AlmostTangleData β›

end Instances

/-- The tangle data at level `⊥` is constructed by taking the tangles to be the atoms, the allowable
permutations to be near-litter-permutations, and the designated supports to be singletons. -/
noncomputable instance Bot.coreTangleData : CoreTangleData ⊥
    where
  Tangle := Atom
  Allowable := NearLitterPerm
  allowableToStructPerm := StructPerm.toBotIso.toMonoidHom
  allowableAction := inferInstance
  designatedSupport a :=
    { carrier := {toCondition (Sum.inl a, Quiver.Path.nil)}
      supports := fun π => by
        simp only [mem_singleton_iff, forall_eq]
        intro h
        change (Sum.inl _, _) = (_, _) at h
        simp only [MulEquiv.coe_toMonoidHom, StructPerm.coe_toBotIso, toCondition, Equiv.refl_apply,
          StructPerm.derivative_nil, StructPerm.toBot_smul, Prod.mk.injEq, Sum.inl.injEq,
          and_true] at h
        exact h
      small := small_singleton _ }

/-- The tangle data at the bottom level. -/
noncomputable instance Bot.positionedTangleData : PositionedTangleData ⊥ :=
  ⟨Nonempty.some mk_atom.le⟩

variable (α : Λ)

/-- The core tangle data below phase `α`. -/
class CoreTangleCumul (α : Λ) where
  data : ∀ β : Iio α, CoreTangleData β

section CoreTangleCumul

variable [CoreTangleCumul α]

noncomputable instance CoreTangleCumul.toCoreTangleData : ∀ β : IioBot α, CoreTangleData β
  | ⟨⊥, _⟩ => Bot.coreTangleData
  | ⟨(β : Λ), hβ⟩ => CoreTangleCumul.data ⟨β, coe_lt_coe.1 hβ⟩

noncomputable instance CoreTangleCumul.toCoreTangleData' (β : Iio α) : CoreTangleData β :=
  show CoreTangleData (iioCoe β) by infer_instance

noncomputable instance CoreTangleCumul.toCoreTangleData'' (β : TypeIndex) (hβ : β < α) :
    CoreTangleData (show IioBot α from ⟨β, hβ⟩) :=
  CoreTangleCumul.toCoreTangleData α ⟨β, hβ⟩

noncomputable instance CoreTangleCumul.toCoreTangleData''' (β : Λ) (hβ : (β : TypeIndex) < α) :
    CoreTangleData (show IioBot α from ⟨β, hβ⟩) :=
  CoreTangleCumul.toCoreTangleData α ⟨β, hβ⟩

end CoreTangleCumul

/-- The positioned tangle data below phase `α`. -/
class PositionedTangleCumul (α : Λ) [CoreTangleCumul α] where
  data : ∀ β : Iio α, PositionedTangleData β

section PositionedTangleCumul

variable [CoreTangleCumul α] [PositionedTangleCumul α]

noncomputable instance PositionedTangleCumul.toPositionedTangleData :
    ∀ β : IioBot α, PositionedTangleData β
  | ⟨⊥, _⟩ => Bot.positionedTangleData
  | ⟨(β : Λ), hβ⟩ => PositionedTangleCumul.data ⟨β, coe_lt_coe.1 hβ⟩

noncomputable instance PositionedTangleCumul.toPositionedTangleData' (β : Iio α) :
    PositionedTangleData β :=
  show PositionedTangleData (iioCoe β) by infer_instance

end PositionedTangleCumul

/-- The almost tangle data below phase `α`. -/
abbrev AlmostTangleCumul (α : Λ) [CoreTangleCumul α] :=
  ∀ β : Iio α, AlmostTangleData β

/-- The tangle data below phase `α`. -/
abbrev TangleCumul (α : Λ) [CoreTangleCumul α] [PositionedTangleCumul α] [PositionData]
    [AlmostTangleCumul α] :=
  ∀ β : Iio α, TangleData β

end ConNF
