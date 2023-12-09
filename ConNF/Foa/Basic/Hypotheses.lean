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

variable [Params.{u}] [BasePositions] (α : Λ)

instance TangleDataLtCoe (β : Iio α) [inst : TangleData (β : Iic α)] : TangleData β :=
  inst

instance tangleDataIic (β : Iic α) [inst : TangleData β] : TangleData (β : Λ) :=
  inst

instance tangleDataIic' (β : Iio α) [inst : TangleData β] : TangleData (β : Λ) :=
  inst

instance TypedObjectsLt (β : Iio α) [inst_0 : TangleData β]
    [inst : @TypedObjects _ (β : Iic α) inst_0] : TypedObjects β :=
  inst

instance PositionedTanglesLt (β : Iio α) [TangleData β] [inst : PositionedTangles β] :
    PositionedTangles (β : Λ) :=
  inst

/-- Asserts that the positions of typed objects agree with the position functions defined on atoms
and near-litters in `BasePositions`. -/
class PositionedTypedObjects [TangleData α] [TypedObjects α] [PositionedTangles α] : Prop where
  pos_atom_eq : ∀ a : Atom, pos (typedAtom a : Tangle α) = pos a
  pos_nearLitter_eq :
    ∀ N : NearLitter, pos (typedNearLitter N : Tangle α) = pos N
  /-- All tangles are positioned later than all of the support conditions in their designated
  support. -/
  pos_atom_le :
    ∀ (t : Tangle α) (A : ExtendedIndex α) (a : Atom),
      ⟨A, Sum.inl a⟩ ∈ designatedSupport t → pos a ≤ pos t
  /-- All tangles are positioned later than all of the support conditions in their designated
  support. -/
  pos_nearLitter_le :
    ∀ (t : Tangle α) (A : ExtendedIndex α) (N : NearLitter),
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
  lowerTangleData : ∀ β : Iic α, TangleData β
  lowerPositionedTangles : ∀ β : Iio α, PositionedTangles β
  lowerTypedObjects : ∀ β : Iic α, TypedObjects β
  lowerPositionedTypedObjects : ∀ β : Iio α, PositionedTypedObjects β

namespace FoaData

variable [FoaData α] {α} {β : Iic α} {γ : Iio α}

instance tangleData : TangleData β :=
  lowerTangleData β

instance positionedTangles : PositionedTangles γ :=
  lowerPositionedTangles γ

instance typedObjects : TypedObjects β :=
  lowerTypedObjects β

instance positionedTypedObjects : PositionedTypedObjects γ :=
  lowerPositionedTypedObjects γ

noncomputable instance iicBotTangleData : ∀ β : IicBot α, TangleData β
  | ⟨⊥, _⟩ => Bot.tangleData
  | ⟨(β : Λ), hβ⟩ => lowerTangleData ⟨β, coe_le_coe.mp hβ⟩

noncomputable instance iioBotTangleData (β : IioBot α) : TangleData β :=
  show TangleData (⟨β, le_of_lt (IioBot.lt β)⟩ : IicBot α) from inferInstance

noncomputable instance iioBotPositionedTangles : ∀ β : IioBot α, PositionedTangles β
  | ⟨⊥, _⟩ => Bot.positionedTangles
  | ⟨(β : Λ), hβ⟩ => lowerPositionedTangles ⟨β, coe_lt_coe.mp hβ⟩

instance coeIioIicBot : Coe (Iio α) (IicBot α) :=
  ⟨fun β => ⟨(β : Λ), le_of_lt (WithBot.coe_lt_coe.mpr (Iio.lt β))⟩⟩

instance coeIioBotIicBot : Coe (IioBot α) (IicBot α) :=
  ⟨fun β => ⟨(β : TypeIndex), le_of_lt (IioBot.lt β)⟩⟩

instance [FoaData α] {X : Type _} {δ : Iio α} [inst : MulAction (Allowable δ) X] :
    MulAction (Allowable (iioCoe δ)) X :=
  inst

instance mulActionTypeIndex {δ : Iio α} : MulAction (Allowable δ) (Tangle (δ : Λ)) :=
  inferInstanceAs (MulAction (Allowable δ) (Tangle δ))

noncomputable instance mulActionIioIndex {δ : IioBot α} :
    MulAction (Allowable (δ : IicBot α)) (Tangle δ) :=
  inferInstanceAs (MulAction (Allowable δ) (Tangle δ))

end FoaData

/-- Assumptions detailing how the different levels of the tangled structure interact. -/
class FoaAssumptions extends FoaData α where
  /-- The one-step derivative map between types of allowable permutations.
  We can think of this map as `cons`ing a single morphism on a path. -/
  allowableCons :
    ∀ (β : IicBot α) (γ : IicBot α), (γ : TypeIndex) < β → Allowable β →* Allowable γ
  /-- The one-step derivative map commutes with `toStructPerm`. -/
  allowableCons_eq :
    ∀ (β : IicBot α) (γ : IicBot α) (hγ : (γ : TypeIndex) < β) (ρ : Allowable β),
      Tree.comp (Quiver.Path.nil.cons hγ) (Allowable.toStructPerm ρ) =
        Allowable.toStructPerm (allowableCons β γ hγ ρ)
  /-- Designated supports commute with allowable permutations. -/
  smul_designatedSupport {β : Iic α} (t : Tangle β) (ρ : Allowable β) :
    ρ • (designatedSupport t : Set (SupportCondition β)) = designatedSupport (ρ • t)
  /-- The `fuzz` map commutes with allowable permutations. -/
  smul_fuzz {β : IicBot α} (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β)
    (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (ρ : Allowable β) (t : Tangle γ) :
    NearLitterPerm.ofBot (allowableCons δ ⊥ (bot_lt_coe _) (allowableCons β δ hδ ρ)) •
      fuzz (Subtype.coe_injective.ne hγδ) t =
    fuzz (Subtype.coe_injective.ne hγδ) (allowableCons β γ hγ ρ • t)
  /-- We can build an `β`-allowable permutation from a family of allowable permutations at each
  level `γ < β` if they commute with the `fuzz` map. -/
  allowableOfSmulFuzz (β : Iic α) (ρs : ∀ γ : IioBot α, (γ : TypeIndex) < β → Allowable γ) :
    (∀ (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β)
        (hγδ : γ ≠ δ) (t : Tangle γ),
        NearLitterPerm.ofBot (allowableCons δ ⊥ (bot_lt_coe _) (ρs δ hδ)) •
          fuzz (Subtype.coe_injective.ne hγδ) t =
        fuzz (Subtype.coe_injective.ne hγδ) (ρs γ hγ • t)) →
      Allowable (β : IicBot α)
  /-- The allowable permutation we construct in `allowableOfSmulFuzz` has the correct one-step
  derivatives. -/
  allowableOfSmulFuzz_comp_eq {β : Iic α} {ρs} {h} (γ : IioBot α)
    (hγ : (γ : TypeIndex) < β) :
    allowableCons β γ hγ (allowableOfSmulFuzz β ρs h) = ρs γ hγ

export FoaAssumptions (allowableCons allowableCons_eq smul_designatedSupport
  smul_fuzz allowableOfSmulFuzz allowableOfSmulFuzz_comp_eq)

variable {α} [FoaAssumptions α]

/-- Define the full derivative map on allowable permutations by recursion along paths.
This agrees with `Tree.comp`, but yields allowable permutations. -/
noncomputable def Allowable.comp {β : IicBot α} :
    ∀ {γ : IicBot α}, Quiver.Path (β : TypeIndex) γ → Allowable β →* Allowable γ :=
  @Path.iicRec _ α β (fun δ _ => Allowable β →* Allowable δ) (MonoidHom.id _) fun γ δ _ h =>
    (allowableCons γ δ h).comp

/-! We prove that `Allowable.comp` is functorial. In addition, we prove a number of lemmas about
`FoaAssumptions`. -/

@[simp]
theorem Allowable.comp_nil {β : IicBot α} :
    Allowable.comp (Quiver.Path.nil : Quiver.Path (β : TypeIndex) β) = MonoidHom.id _ :=
  rfl

@[simp]
theorem Allowable.comp_eq {β γ : IicBot α} (h : γ < β) :
    allowableCons β γ h = Allowable.comp (Quiver.Path.nil.cons h) :=
  rfl

theorem Allowable.comp_cons {β γ δ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) :
    (allowableCons γ δ h).comp (Allowable.comp A) = Allowable.comp (A.cons h) :=
  rfl

theorem Allowable.comp_cons_apply (β γ δ : IicBot α) (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) (π : Allowable β) :
    allowableCons γ δ h (Allowable.comp A π) = Allowable.comp (A.cons h) π :=
  rfl

theorem Allowable.comp_cons_apply' (β : Iio α) (γ : Iic α) (δ : Iio α)
    (A : Quiver.Path (β : TypeIndex) γ) (h : (δ : TypeIndex) < γ) (π : Allowable β) :
    allowableCons (γ : IicBot α) (δ : IicBot α) h
      (Allowable.comp
        (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) =
    @Allowable.comp _ _ _ _ (β : IicBot α) (δ : IicBot α) (A.cons h) π :=
  rfl

theorem Allowable.comp_cons_apply'' (β : Iio α) (γ : Iic α)
    (A : Quiver.Path (β : TypeIndex) γ) (π : Allowable β) :
    allowableCons (γ : IicBot α) (⊥ : IicBot α) (bot_lt_coe _)
      (Allowable.comp
        (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) =
    @Allowable.comp _ _ _ _ (β : IicBot α) (⊥ : IicBot α) (A.cons <| bot_lt_coe _) π :=
  rfl

theorem Allowable.comp_comp {β γ δ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (B : Quiver.Path (γ : TypeIndex) δ) (π : Allowable β) :
    Allowable.comp B (Allowable.comp A π) = Allowable.comp (A.comp B) π := by
  obtain ⟨γ, hγ⟩ := γ
  obtain ⟨δ, hδ⟩ := δ
  change Quiver.Path γ δ at B
  induction B with
  | nil => simp only [Quiver.Path.comp_nil, Allowable.comp_nil, MonoidHom.id_apply]
  | cons B H ih =>
    rw [Quiver.Path.comp_cons]
    rw [← Allowable.comp_cons (show Quiver.Path
      ((⟨γ, hγ⟩ : IicBot α) : TypeIndex)
      ((⟨_, le_trans (le_of_path B) hγ⟩ : IicBot α) : TypeIndex)
      from B)]
    rw [MonoidHom.coe_comp, Function.comp_apply, ih, Allowable.comp_cons_apply]

@[simp]
theorem Allowable.toStructPerm_comp {β γ : IicBot α}
    (A : Quiver.Path (β : TypeIndex) γ) (π : Allowable β) :
    Allowable.toStructPerm (Allowable.comp A π) =
    Tree.comp A (Allowable.toStructPerm π) := by
  obtain ⟨γ, hγ⟩ := γ
  change Quiver.Path (β : TypeIndex) γ at A
  induction A with
  | nil => rw [Tree.comp_nil, Allowable.comp_nil, MonoidHom.id_apply]
  | cons A h ih =>
      change toStructPerm (allowableCons _ _ _ (comp _ π)) = _
      rw [Tree.comp_cons, ← allowableCons_eq, ih]
      rfl

@[simp]
theorem Allowable.toStructPerm_apply {β : IicBot α}
    (A : Quiver.Path (β : TypeIndex) (⊥ : IicBot α)) (π : Allowable β) :
    NearLitterPerm.ofBot (Allowable.comp A π) = Allowable.toStructPerm π A :=
  congr_fun (Allowable.toStructPerm_comp A π) Quiver.Path.nil

theorem Allowable.comp_bot {β : IicBot α}
    (A : Quiver.Path (β : TypeIndex) (⊥ : IicBot α)) (ρ : Allowable β) :
    Allowable.comp A ρ = Allowable.toStructPerm ρ A := by
  refine NearLitterPerm.ext ?_
  ext a : 1
  change NearLitterPerm.ofBot (Allowable.comp A ρ) • a = Allowable.toStructPerm ρ A • a
  simp only [Allowable.toStructPerm_apply]

theorem smul_mem_designatedSupport {β : Iio α} {c : SupportCondition β} {t : Tangle β}
    (h : c ∈ designatedSupport t) (π : Allowable β) : π • c ∈ designatedSupport (π • t) :=
  (Set.ext_iff.mp (smul_designatedSupport (show Tangle (β : Iic α) from t) π)
        ((show Allowable (β : Iic α) from π) • c)).mp
    ⟨c, h, rfl⟩

@[simp]
theorem ofBot_comp' {β : IicBot α} {hβ : ⊥ < β} {ρ : Allowable β} :
    NearLitterPerm.ofBot (allowableCons β ⊥ hβ ρ) =
    Allowable.toStructPerm ρ (Quiver.Hom.toPath hβ) :=
  (congr_fun (allowableCons_eq β ⊥ hβ ρ) Quiver.Path.nil).symm

theorem exists_cons_of_length_ne_zero {V : Type _} [Quiver V] {x y : V}
    (p : Quiver.Path x y) (h : p.length ≠ 0) :
    ∃ t : V, ∃ q : Quiver.Path x t, ∃ e : t ⟶ y, p = q.cons e := by
  cases p
  · cases h rfl
  · exact ⟨_, _, _, rfl⟩

theorem ofBot_comp {β : IicBot α} {ρ : Allowable β}
    (A : Quiver.Path (β : TypeIndex) (⊥ : IicBot α)) :
    NearLitterPerm.ofBot (Allowable.comp A ρ) = Allowable.toStructPerm ρ A := by
  by_cases h : A.length = 0
  · have : β = ⊥ := Subtype.coe_injective (Quiver.Path.eq_of_length_zero A h)
    cases this
    cases path_eq_nil A
    rfl
  · obtain ⟨γ, A, h', rfl⟩ := exists_cons_of_length_ne_zero A h
    have := Allowable.comp_cons
      (show Quiver.Path (β : TypeIndex) (⟨γ, ?_⟩ : IicBot α) from A)
      (show ⊥ < ⟨γ, _⟩ from h')
    rw [← this, MonoidHom.comp_apply, ofBot_comp', Allowable.toStructPerm_comp]
    simp only [Tree.comp_apply, Quiver.Hom.comp_toPath]
    exact le_trans (le_of_path A) β.prop

@[simp]
theorem ofBot_smul {X : Type _} [MulAction NearLitterPerm X] (π : Allowable ⊥) (x : X) :
    π • x = NearLitterPerm.ofBot π • x :=
  rfl

@[simp]
theorem comp_bot_smul_atom {β : IicBot α}
    (ρ : Allowable β) (A : Quiver.Path (β : TypeIndex) (⊥ : IicBot α)) (a : Tangle ⊥) :
    Allowable.comp A ρ • a = Allowable.toStructPerm ρ A • (show Atom from a) := by
  rw [← ofBot_comp]
  rfl

theorem toStructPerm_smul_fuzz' (β : IicBot α) (γ : IioBot α) (δ : Iio α)
    (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (ρ : Allowable β)
    (t : Tangle γ) :
    Allowable.toStructPerm ρ ((Quiver.Path.nil.cons hδ).cons (bot_lt_coe _)) •
      fuzz (Subtype.coe_injective.ne hγδ) t =
    fuzz (Subtype.coe_injective.ne hγδ) (allowableCons β γ hγ ρ • t) := by
  have := congr_fun (allowableCons_eq β δ hδ ρ) (Quiver.Hom.toPath (bot_lt_coe _))
  simp only [Tree.comp_apply, Quiver.Hom.comp_toPath] at this
  rw [this, ← smul_fuzz γ δ hγ hδ hγδ ρ t, ofBot_comp']

theorem toStructPerm_smul_fuzz (β : IicBot α) (γ : IicBot α) (δ : IioBot α) (ε : Iio α)
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : δ ≠ ε)
    (A : Quiver.Path (β : TypeIndex) γ) (ρ : Allowable β) (t : Tangle δ) :
    Allowable.toStructPerm ρ ((A.cons hε).cons (bot_lt_coe _)) •
      fuzz (Subtype.coe_injective.ne hδε) t =
    fuzz (Subtype.coe_injective.ne hδε) (Allowable.comp (β := β) (γ := δ) (A.cons hδ) ρ • t) := by
  have := toStructPerm_smul_fuzz' γ δ ε hδ hε hδε (Allowable.comp A ρ) t
  simp only [Allowable.toStructPerm_comp, Tree.comp_apply, Quiver.Path.comp_cons,
    Quiver.Path.comp_nil, Allowable.comp_eq] at this
  exact this

end ConNF
