import ConNF.Phase0.Support

#align_import phase1.basic

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `con_nf.core_tangle_data`:
* `con_nf.positioned_tangle_data`:
* `con_nf.almost_tangle_data`:
* `con_nf.tangle_data`: The data for the first phase of the recursion.
-/


open Function Set WithBot

noncomputable section

universe u

namespace ConNf

variable [Params.{u}]

section DefineTangleData

/-- The motor of the initial recursion. This contains the data of tangles and allowable permutations
for phase 1 of the recursion. -/
class CoreTangleData (α : TypeIndex) where
  (Tangle Allowable : Type u)
  [allowableGroup : Group allowable]
  allowableToStructPerm : allowable →* StructPerm α
  [allowableAction : MulAction allowable tangle]
  designatedSupport :
    haveI : MulAction allowable (support_condition α) :=
      MulAction.compHom _ allowable_to_struct_perm
    ∀ t : tangle, support α allowable t

export CoreTangleData (Tangle Allowable designatedSupport)

attribute [instance] core_tangle_data.allowable_group core_tangle_data.allowable_action

section

variable (α : TypeIndex) [CoreTangleData α]

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
preserves the group structure. This allows allowable permutations to act on pretangles. -/
def toStructPerm : Allowable α →* StructPerm α :=
  CoreTangleData.allowableToStructPerm

instance : MulAction (Allowable α) (Tangle α) :=
  CoreTangleData.allowableAction

/-- Allowable permutations act on tangles. This action commutes with certain other operations; the
exact conditions are given in `smul_typed_near_litter` and `smul_pretangle_inj`. -/
instance : MulAction (Allowable α) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (f : Allowable α) (x : X) : f.toStructPerm • x = f • x :=
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
    ∀ (π : Allowable α) (N), π • typed_near_litter N = typed_near_litter (π • N)
  pretangleInj : Tangle α ↪ Pretangle α
  smul_pretangleInj :
    ∀ (π : Allowable α) (t : Tangle α), π • pretangle_inj t = pretangle_inj (π • t)

export AlmostTangleData (typedAtom typedNearLitter pretangleInj)

namespace Allowable

variable {α} [AlmostTangleData α]

/--
The action of allowable permutations on tangles commutes with the `typed_near_litter` function mapping
near-litters to typed near-litters. This is quite clear to see when representing tangles as codes,
but since at this stage tangles are just a type, we have to state this condition explicitly. -/
theorem smul_typedNearLitter (π : Allowable α) (N : NearLitter) :
    π • (typedNearLitter N : Tangle α) = typedNearLitter (π • N) :=
  AlmostTangleData.smul_typedNearLitter _ _

/-- The action of allowable permutations on tangles commutes with the `pretangle_inj` injection
converting tangles into pretangles. -/
theorem smul_pretangleInj (π : Allowable α) (t : Tangle α) :
    π • pretangleInj t = pretangleInj (π • t) :=
  AlmostTangleData.smul_pretangleInj _ _

end Allowable

/-- The position of typed atoms and typed near-litters in the position function at any level.
This is part of the `γ = -1` fix. -/
class PositionData where
  typedAtomPosition : Atom ↪ μ
  typedNearLitterPosition : NearLitter ↪ μ
  litter_lt :
    ∀ (L : Litter),
      ∀ a ∈ litterSet L, typed_near_litter_position L.toNearLitter < typed_atom_position a
  litter_le_nearLitter :
    ∀ N : NearLitter, typed_near_litter_position N.fst.toNearLitter ≤ typed_near_litter_position N
  symmDiff_lt_nearLitter :
    ∀ (N : NearLitter),
      ∀ a ∈ litterSet N.fst ∆ N.snd, typed_atom_position a < typed_near_litter_position N

export
  PositionData (typedAtomPosition typedNearLitterPosition litter_lt litter_le_nearLitter symmDiff_lt_nearLitter)

theorem litter_lt_nearLitter [PositionData] (N : NearLitter) (hN : N.fst.toNearLitter ≠ N) :
    typedNearLitterPosition N.fst.toNearLitter < typedNearLitterPosition N :=
  lt_of_le_of_ne (litter_le_nearLitter N) (typedNearLitterPosition.Injective.Ne hN)

variable [AlmostTangleData α] [PositionedTangleData α] [PositionData]

/-- The motor of the initial recursion. This contains all the information needed for phase 1 of the
recursion. -/
class TangleData : Prop where
  typedAtomPosition_eq : ∀ a : Atom, position (typedAtom a : Tangle α) = typedAtomPosition a
  typedNearLitterPosition_eq :
    ∀ N : NearLitter, position (typedNearLitter N : Tangle α) = typedNearLitterPosition N
  support_le :
    ∀ (t : Tangle α) (c : SupportCondition α) (hc : c ∈ designatedSupport t),
      c.fst.elim typedAtomPosition typedNearLitterPosition ≤ position t

/-- The type of tangles that we assume were constructed at stage `α`.
Later in the recursion, we will construct this type explicitly, but for now, we will just assume
that it exists.
Fields in `tangle_data` give more information about this type. -/
add_decl_doc core_tangle_data.tangle

/-- An injection from near-litters into level `α` tangles.
These will be explicitly constructed as "typed near-litters", which are codes of the form
`(α, -1, N)` for `N` a near-litter.

Since we haven't assumed anything about the structure of tangles at this level, we can't construct
these typed near-litters explicitly, so we rely on this function instead. In the blueprint, this is
function `j`. -/
add_decl_doc almost_tangle_data.typed_near_litter

/-- Tangles can be considered a subtype of pretangles, which are tangles without extensionality and
which are guaranteed to have a `-1`-extension. This injection can be seen as an inclusion map.
Since pretangles have a membership relation, we can use this map to see the members of a tangle at
any given level, by first converting it to a pretangle. -/
add_decl_doc almost_tangle_data.pretangle_inj

/-- For any atom `a`, we can construct an `α`-tangle that has a `-1`-extension that contains exactly
this atom. This is called a typed singleton. In the blueprint, this is the function `k`. -/
add_decl_doc almost_tangle_data.typed_atom

/-- An injection from level `α` tangles into the type `μ`.
Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two tangles,
simply compare their images under this map.

Conditions satisfied by this injection are given in `litter_lt`, `litter_lt_near_litter`,
`symm_diff_lt_near_litter`, and `support_le`. In the blueprint, this is function `ι`. -/
add_decl_doc positioned_tangle_data.position

/-- Each typed litter `L` precedes the typed singletons of all of its elements `a ∈ L`. -/
add_decl_doc position_data.litter_lt

/-- Each near litter `N` which is not a litter comes later than its associated liter `L = N°`. -/
add_decl_doc litter_lt_near_litter

/-- Each near litter `N` comes after all elements in the symmetric difference `N ∆ N°` (which is
a small set by construction). Note that if `N` is a litter, this condition is vacuously true. -/
add_decl_doc symm_diff_lt_near_litter

/-- For all tangles `t` that are not typed singletons and not typed litters, `t` comes later than
all of the support conditions in its designated support. That is, if an atom `a` is in the
designated support for `t`, then `t` lies after `a`, and if a near-litter `N` is in the designated
support for `t`, then `t` lies after `N` (under suitable maps to `μ`). -/
add_decl_doc tangle_data.support_le

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
instance Bot.coreTangleData : CoreTangleData ⊥
    where
  Tangle := Atom
  Allowable := NearLitterPerm
  allowableToStructPerm := StructPerm.toBotIso.toMonoidHom
  allowableAction := inferInstance
  designatedSupport a :=
    { carrier := {toCondition (Sum.inl a, Quiver.Path.nil)}
      Supports := fun π => by
        simp only [mem_singleton_iff, SMul.comp.smul, MulEquiv.coe_toMonoidHom,
          struct_perm.coe_to_bot_iso, Equiv.toFun_as_coe, forall_eq, struct_perm.smul_to_condition,
          struct_perm.derivative_nil, struct_perm.to_bot_smul, Sum.smul_inl,
          EmbeddingLike.apply_eq_iff_eq, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff, imp_self]
      Small := small_singleton _ }

/-- The tangle data at the bottom level. -/
instance Bot.positionedTangleData : PositionedTangleData ⊥ :=
  ⟨Nonempty.some mk_atom.le⟩

variable (α : Λ)

/-- The core tangle data below phase `α`. -/
class CoreTangleCumul (α : Λ) where
  data : ∀ β : Iio α, CoreTangleData β

section CoreTangleCumul

variable [CoreTangleCumul α]

instance CoreTangleCumul.toCoreTangleData : ∀ β : iioIndex α, CoreTangleData β
  | ⟨⊥, h⟩ => Bot.coreTangleData
  | ⟨(β : Λ), hβ⟩ => CoreTangleCumul.data ⟨β, coe_lt_coe.1 hβ⟩

instance CoreTangleCumul.toCoreTangleData' (β : Iio α) : CoreTangleData β :=
  show CoreTangleData (iioCoe β) by infer_instance

end CoreTangleCumul

/-- The positioned tangle data below phase `α`. -/
class PositionedTangleCumul (α : Λ) [CoreTangleCumul α] where
  data : ∀ β : Iio α, PositionedTangleData β

section PositionedTangleCumul

variable [CoreTangleCumul α] [PositionedTangleCumul α]

instance PositionedTangleCumul.toPositionedTangleData : ∀ β : iioIndex α, PositionedTangleData β
  | ⟨⊥, h⟩ => Bot.positionedTangleData
  | ⟨(β : Λ), hβ⟩ => PositionedTangleCumul.data ⟨β, coe_lt_coe.1 hβ⟩

instance PositionedTangleCumul.toPositionedTangleData' (β : Iio α) : PositionedTangleData β :=
  show PositionedTangleData (iioCoe β) by infer_instance

end PositionedTangleCumul

/-- The almost tangle data below phase `α`. -/
abbrev AlmostTangleCumul (α : Λ) [CoreTangleCumul α] :=
  ∀ β : Iio α, AlmostTangleData β

/-- The tangle data below phase `α`. -/
abbrev TangleCumul (α : Λ) [CoreTangleCumul α] [PositionedTangleCumul α] [PositionData]
    [AlmostTangleCumul α] :=
  ∀ β : Iio α, TangleData β

end ConNf
