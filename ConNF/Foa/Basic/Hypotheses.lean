import ConNF.Fuzz

/-!
# Hypotheses for proving freedom of action

This file contains the inductive hypotheses required for proving the freedom of action theorem.

## Main declarations

* `ConNF.PositionedTypedObjects`: Asserts that the positions of typed objects agree with the
    position functions defined on atoms and near-litters in `BasePositions`.
* `ConNF.FoaData`: Contains various kinds of tangle data for all levels below `α`.
* `ConNF.FoaAssumptions`: Describes how the type levels in the `FoaData` tangle together.
-/

open Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}] [BasePositions] [Level]

/-- Asserts that the positions of typed objects agree with the position functions defined on atoms
and near-litters in `BasePositions`. -/
class PositionedTypedObjects (β : Λ) [TangleData β] [TypedObjects β] [PositionedTangles β] : Prop
    where
  pos_atom_eq : ∀ a : Atom, pos (typedAtom a : Tangle β) = pos a
  pos_nearLitter_eq :
    ∀ N : NearLitter, pos (typedNearLitter N : Tangle β) = pos N
  /-- All tangles are positioned later than all of the support conditions in their designated
  support. -/
  pos_atom_le :
    ∀ (t : Tangle β) (A : ExtendedIndex β) (a : Atom),
      ⟨A, Sum.inl a⟩ ∈ designatedSupport t → pos a ≤ pos t
  /-- All tangles are positioned later than all of the support conditions in their designated
  support. -/
  pos_nearLitter_le :
    ∀ (t : Tangle β) (A : ExtendedIndex β) (N : NearLitter),
      ⟨A, Sum.inr N⟩ ∈ designatedSupport t → pos N ≤ pos t

/-- The data that we will use when proving the freedom of action theorem.
This structure combines the following data:
* `Tangle`
* `Allowable`
* `designatedSupport`
* `pos : Tangle β ↪ μ`
* `typedAtom` and `typedNearLitter`
-/
class FoaData where
  lowerTangleData : ∀ β : Λ, [LeLevel β] → TangleData β
  lowerPositionedTangles : ∀ β : Λ, [LtLevel β] → PositionedTangles β
  lowerTypedObjects : ∀ β : Λ, [LeLevel β] → TypedObjects β
  lowerPositionedTypedObjects : ∀ β : Λ, [LtLevel β] → PositionedTypedObjects β

namespace FoaData

variable [FoaData] {β : Λ} [LeLevel β] {γ : Λ} [LtLevel γ]

instance tangleData : TangleData β :=
  lowerTangleData β

instance positionedTangles : PositionedTangles γ :=
  lowerPositionedTangles γ

instance typedObjects : TypedObjects β :=
  lowerTypedObjects β

instance positionedTypedObjects : PositionedTypedObjects γ :=
  lowerPositionedTypedObjects γ

noncomputable instance iicBotTangleData : ∀ β : TypeIndex, [LeLevel β] → TangleData β
  | ⊥, _ => Bot.tangleData
  | (β : Λ), _ => lowerTangleData β

noncomputable instance iioBotPositionedTangles : ∀ β : TypeIndex, [LtLevel β] → PositionedTangles β
  | ⊥, _ => Bot.positionedTangles
  | (β : Λ), _ => lowerPositionedTangles β

end FoaData

/-- Assumptions detailing how the different levels of the tangled structure interact. -/
class FoaAssumptions extends FoaData where
  /-- The one-step derivative map between types of allowable permutations.
  We can think of this map as `cons`ing a single morphism on a path. -/
  allowableCons :
    ∀ {β : TypeIndex} [LeLevel β] {γ : TypeIndex} [LeLevel γ],
      γ < β → Allowable β →* Allowable γ
  /-- The one-step derivative map commutes with `toStructPerm`. -/
  allowableCons_eq :
    ∀ (β : TypeIndex) [LeLevel β] (γ : TypeIndex) [LeLevel γ]
      (hγ : γ < β) (ρ : Allowable β),
      Tree.comp (Quiver.Path.nil.cons hγ) (Allowable.toStructPerm ρ) =
        Allowable.toStructPerm (allowableCons hγ ρ)
  /-- Designated supports commute with allowable permutations. -/
  designatedSupport_smul {β : Λ} [LeLevel β] (t : Tangle β) (ρ : Allowable β) :
    designatedSupport (ρ • t) = ρ • (designatedSupport t : Set (SupportCondition β))
  /-- The `fuzz` map commutes with allowable permutations. -/
  smul_fuzz {β : TypeIndex} [LeLevel β] {γ : TypeIndex} [LtLevel γ] {δ : Λ} [LtLevel δ]
    (hγ : γ < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (ρ : Allowable β) (t : Tangle γ) :
    NearLitterPerm.ofBot (allowableCons (bot_lt_coe _) (allowableCons hδ ρ)) • fuzz hγδ t =
    fuzz hγδ (allowableCons hγ ρ • t)
  /-- We can build an `β`-allowable permutation from a family of allowable permutations at each
  level `γ < β` if they commute with the `fuzz` map. -/
  allowableOfSmulFuzz (β : Λ) [LeLevel β]
    (ρs : ∀ γ : TypeIndex, [LtLevel γ] → (γ : TypeIndex) < β → Allowable γ) :
    (∀ (γ : TypeIndex) [LtLevel γ] (δ : Λ) [LtLevel δ]
        (hγ : γ < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (t : Tangle γ),
        NearLitterPerm.ofBot (allowableCons (bot_lt_coe _) (ρs δ hδ)) • fuzz hγδ t =
        fuzz hγδ (ρs γ hγ • t)) →
      Allowable β
  /-- The allowable permutation we construct in `allowableOfSmulFuzz` has the correct one-step
  derivatives. -/
  allowableOfSmulFuzz_comp_eq {β : Λ} [LeLevel β] {ρs} {h}
    {γ : TypeIndex} [LtLevel γ] {hγ : γ < β} :
    allowableCons hγ (allowableOfSmulFuzz β ρs h) = ρs γ hγ

export FoaAssumptions (allowableCons allowableCons_eq designatedSupport_smul
  smul_fuzz allowableOfSmulFuzz allowableOfSmulFuzz_comp_eq)

attribute [simp] designatedSupport_smul allowableOfSmulFuzz_comp_eq

variable [FoaAssumptions]

/-- A primitive version of `Allowable.comp` with different arguments. This is always the wrong
spelling to use. -/
def Allowable.comp' {β : TypeIndex} [LeLevel β] :
    ∀ {γ : TypeIndex}, (A : Quiver.Path β γ) →
      let _ : LeLevel γ := ⟨(le_of_path A).trans LeLevel.elim⟩; Allowable β →* Allowable γ :=
  Quiver.Path.rec
    (motive := fun γ A =>
      let _ : LeLevel γ := ⟨(le_of_path A).trans LeLevel.elim⟩; Allowable β →* Allowable γ)
    (MonoidHom.id _)
    (fun {γ δ} A h f =>
      let _ : LeLevel γ := ⟨(le_of_path A).trans LeLevel.elim⟩;
      let _ : LeLevel δ := _;
      (allowableCons h).comp f)

/-- Define the full derivative map on allowable permutations by recursion along paths.
This agrees with `Tree.comp`, but yields allowable permutations.
Note that the `LeLevel γ` hypothesis is technically redundant, but is used to give us more
direct access to `Allowable γ`. In practice, we already have this assumption wherever we use
`Allowable.comp`. -/
def Allowable.comp {β γ : TypeIndex} [LeLevel β] [LeLevel γ] (A : Quiver.Path β γ) :
    Allowable β →* Allowable γ :=
  Allowable.comp' A

/-! We prove that `Allowable.comp` is functorial. In addition, we prove a number of lemmas about
`FoaAssumptions`. -/

@[simp]
theorem Allowable.comp_nil {β : TypeIndex} [LeLevel β] :
    Allowable.comp (Quiver.Path.nil : Quiver.Path β β) = MonoidHom.id _ :=
  rfl

@[simp]
theorem Allowable.comp_eq {β γ : TypeIndex} [LeLevel β] [LeLevel γ] (h : γ < β) :
    allowableCons h = Allowable.comp (Quiver.Path.nil.cons h) :=
  rfl

@[simp]
theorem Allowable.comp_cons {β γ δ : TypeIndex} [LeLevel β] [LeLevel γ] [LeLevel δ]
    (A : Quiver.Path β γ) (h : δ < γ) :
    (allowableCons h).comp (Allowable.comp A) = Allowable.comp (A.cons h) :=
  rfl

@[simp]
theorem Allowable.comp_cons_apply {β γ δ : TypeIndex} [LeLevel β] [LeLevel γ] [LeLevel δ]
    (A : Quiver.Path β γ) (h : δ < γ) (π : Allowable β) :
    allowableCons h (Allowable.comp A π) = Allowable.comp (A.cons h) π :=
  rfl

@[simp]
theorem Allowable.comp_comp_apply {β γ δ : TypeIndex} [LeLevel β] [LeLevel γ] [i : LeLevel δ]
    (A : Quiver.Path β γ) (B : Quiver.Path γ δ) (π : Allowable β) :
    Allowable.comp B (Allowable.comp A π) = Allowable.comp (A.comp B) π := by
  revert i
  induction B with
  | nil =>
      intro
      rfl
  | cons B h ih =>
      intro
      have : LeLevel _ := ⟨(le_of_path B).trans LeLevel.elim⟩
      simp_rw [Quiver.Path.comp_cons, ← comp_cons_apply (A.comp B) h, ← ih]
      rfl

@[simp]
theorem Allowable.toStructPerm_comp {β γ : TypeIndex} [LeLevel β] [i : LeLevel γ]
    (A : Quiver.Path β γ) (π : Allowable β) :
    Allowable.toStructPerm (Allowable.comp A π) = Tree.comp A (Allowable.toStructPerm π) := by
  revert i
  induction A with
  | nil =>
      intro i
      rw [Tree.comp_nil, Allowable.comp_nil, MonoidHom.id_apply]
  | cons A h ih =>
      intro i
      have : LeLevel _ := ⟨(le_of_path A).trans LeLevel.elim⟩
      change toStructPerm (allowableCons _ (comp _ π)) = _
      rw [Tree.comp_cons, ← allowableCons_eq, ih]
      rfl

@[simp]
theorem Allowable.toStructPerm_apply {β : TypeIndex} [LeLevel β]
    (A : Quiver.Path β ⊥) (π : Allowable β) :
    NearLitterPerm.ofBot (Allowable.comp A π) = Allowable.toStructPerm π A :=
  congr_fun (Allowable.toStructPerm_comp A π) Quiver.Path.nil

theorem Allowable.comp_bot {β : TypeIndex} [LeLevel β] (A : Quiver.Path β ⊥) (ρ : Allowable β) :
    Allowable.comp A ρ = Allowable.toStructPerm ρ A := by
  refine NearLitterPerm.ext ?_
  ext a : 1
  change NearLitterPerm.ofBot (Allowable.comp A ρ) • a = Allowable.toStructPerm ρ A • a
  simp only [Allowable.toStructPerm_apply]

theorem smul_mem_designatedSupport {β : Λ} [LtLevel β] {c : SupportCondition β} {t : Tangle β}
    (h : c ∈ designatedSupport t) (π : Allowable β) : π • c ∈ designatedSupport (π • t) :=
  (Set.ext_iff.mp (designatedSupport_smul t π) (π • c)).mpr ⟨c, h, rfl⟩

@[simp]
theorem NearLitterPerm.ofBot_comp' {β : TypeIndex} [LeLevel β] {hβ : ⊥ < β} {ρ : Allowable β} :
    NearLitterPerm.ofBot (allowableCons hβ ρ) = Allowable.toStructPerm ρ (Quiver.Hom.toPath hβ) :=
  (congr_fun (allowableCons_eq β ⊥ hβ ρ) Quiver.Path.nil).symm

theorem exists_cons_of_length_ne_zero {V : Type _} [Quiver V] {x y : V}
    (p : Quiver.Path x y) (h : p.length ≠ 0) :
    ∃ t : V, ∃ q : Quiver.Path x t, ∃ e : t ⟶ y, p = q.cons e := by
  cases p
  · cases h rfl
  · exact ⟨_, _, _, rfl⟩

@[simp]
theorem ofBot_smul {X : Type _} [MulAction NearLitterPerm X] (π : Allowable ⊥) (x : X) :
    π • x = NearLitterPerm.ofBot π • x :=
  rfl

@[simp]
theorem comp_bot_smul_atom {β : TypeIndex} [LeLevel β]
    (ρ : Allowable β) (A : Quiver.Path β ⊥) (a : Tangle ⊥) :
    Allowable.comp A ρ • a = Allowable.toStructPerm ρ A • (show Atom from a) := by
  rw [← Allowable.toStructPerm_apply]
  rfl

theorem toStructPerm_smul_fuzz'
    {β : TypeIndex} [LeLevel β] {γ : TypeIndex} [LtLevel γ] {δ : Λ} [LtLevel δ]
    (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (ρ : Allowable β) (t : Tangle γ) :
    Allowable.toStructPerm ρ ((Quiver.Path.nil.cons hδ).cons (bot_lt_coe _)) • fuzz hγδ t =
    fuzz hγδ (allowableCons hγ ρ • t) := by
  have := congr_fun (allowableCons_eq β δ hδ ρ) (Quiver.Hom.toPath (bot_lt_coe _))
  simp only [Tree.comp_apply, Quiver.Hom.comp_toPath] at this
  rw [this, ← smul_fuzz hγ hδ hγδ ρ t, ← Allowable.toStructPerm_apply]
  rfl

@[simp]
theorem toStructPerm_smul_fuzz
    {β : TypeIndex} [LeLevel β] {γ : TypeIndex} [LeLevel γ]
    {δ : TypeIndex} [LtLevel δ] {ε : Λ} [LtLevel ε]
    (hδ : δ < γ) (hε : ε < γ) (hδε : δ ≠ ε)
    (A : Quiver.Path (β : TypeIndex) γ) (ρ : Allowable β) (t : Tangle δ) :
    Allowable.toStructPerm ρ ((A.cons hε).cons (bot_lt_coe _)) • fuzz hδε t =
    fuzz hδε (Allowable.comp (A.cons hδ) ρ • t) := by
  have := toStructPerm_smul_fuzz' hδ hε hδε (Allowable.comp A ρ) t
  simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Quiver.Path.comp_cons,
    Quiver.Path.comp_nil, Allowable.comp_eq] at this
  exact this

end ConNF
