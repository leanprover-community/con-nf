import ConNF.Fuzz

open Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}] [BasePositions] (α : Λ)

instance corePositionedTypedObjectsIic (β : Iio α) [inst : TangleData (β : Iic α)] : TangleData β :=
  inst

instance corePositionedTypedObjectsIic' (β : Iic α) [inst : TangleData β] : TangleData (β : Λ) :=
  inst

instance corePositionedTypedObjectsIio' (β : Iio α) [inst : TangleData β] : TangleData (β : Λ) :=
  inst

instance almostPositionedTypedObjectsIio (β : Iio α) [inst_0 : TangleData β]
    [inst : @TypedObjects _ (β : Iic α) inst_0] : TypedObjects β :=
  inst

instance positionedPositionedTypedObjectsIio (β : Iio α) [TangleData β] [inst : PositionedTangles β] :
    PositionedTangles (β : Λ) :=
  inst

/-- The motor of the initial recursion. This contains all the information needed for phase 1 of the
recursion. -/
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

class Phase2Data where
  lowerTangleData : ∀ β : Iic α, TangleData β
  lowerPositionedTangles : ∀ β : Iio α, PositionedTangles β
  lowerTypedObjects : ∀ β : Iic α, TypedObjects β
  lowerPositionedTypedObjects : ∀ β : Iio α, PositionedTypedObjects β

namespace Phase2Data

variable [Phase2Data α] {α} {β : Iic α} {γ : Iio α}

instance corePositionedTypedObjects : TangleData β :=
  lowerTangleData β

instance positionedPositionedTypedObjects : PositionedTangles γ :=
  lowerPositionedTangles γ

instance almostPositionedTypedObjects : TypedObjects β :=
  lowerTypedObjects β

instance tangleData : PositionedTypedObjects γ :=
  lowerPositionedTypedObjects γ

noncomputable instance IicBotTangleData : ∀ β : IicBot α, TangleData β
  | ⟨⊥, _⟩ => Bot.tangleData
  | ⟨(β : Λ), hβ⟩ => lowerTangleData ⟨β, coe_le_coe.mp hβ⟩

noncomputable instance IioBotTangleData (β : IioBot α) : TangleData β :=
  show TangleData (⟨β, le_of_lt (IioBot.lt β)⟩ : IicBot α) from inferInstance

noncomputable instance IioBotPositionedTangles : ∀ β : IioBot α, PositionedTangles β
  | ⟨⊥, _⟩ => Bot.positionedTangles
  | ⟨(β : Λ), hβ⟩ => lowerPositionedTangles ⟨β, coe_lt_coe.mp hβ⟩

instance hasCoeIioIicIndex : Coe (Iio α) (IicBot α) :=
  ⟨fun β => ⟨(β : Λ), le_of_lt (WithBot.coe_lt_coe.mpr (Iio.lt β))⟩⟩

instance hasCoeIioIndexIicIndex : Coe (IioBot α) (IicBot α) :=
  ⟨fun β => ⟨(β : TypeIndex), le_of_lt (IioBot.lt β)⟩⟩

instance [Phase2Data α] {X : Type _} {δ : Iio α} [inst : MulAction (Allowable δ) X] :
    MulAction (Allowable (iioCoe δ)) X :=
  inst

instance mulActionTypeIndex {δ : Iio α} : MulAction (Allowable δ) (Tangle (δ : Λ)) :=
  show MulAction (Allowable δ) (Tangle δ) from inferInstance

noncomputable instance mulActionIioIndex {δ : IioBot α} :
    MulAction (Allowable (δ : IicBot α)) (Tangle δ) :=
  show MulAction (Allowable δ) (Tangle δ) from inferInstance

end Phase2Data

class Phase2Assumptions extends Phase2Data α where
  allowableDerivative :
    ∀ (β : IicBot α) (γ : IicBot α), (γ : TypeIndex) < β → Allowable β →* Allowable γ
  allowableDerivative_eq :
    ∀ (β : IicBot α) (γ : IicBot α) (hγ : (γ : TypeIndex) < β) (π : Allowable β),
      StructPerm.derivative (Quiver.Path.nil.cons hγ) (Allowable.toStructPerm π) =
        Allowable.toStructPerm (allowableDerivative β γ hγ π)
  smul_designatedSupport {β : Iic α} (t : Tangle β) (π : Allowable β) :
    π • (designatedSupport t : Set (SupportCondition β)) = designatedSupport (π • t)
  smul_fuzz {β : IicBot α} (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β)
    (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (π : Allowable β) (t : Tangle γ) :
    NearLitterPerm.ofBot (allowableDerivative δ ⊥ (bot_lt_coe _) (allowableDerivative β δ hδ π)) •
      fuzz (Subtype.coe_injective.ne hγδ) t =
    fuzz (Subtype.coe_injective.ne hγδ) (allowableDerivative β γ hγ π • t)
  allowableOfSmulFuzz (β : Iic α) (πs : ∀ γ : IioBot α, (γ : TypeIndex) < β → Allowable γ) :
    (∀ (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β)
        (hγδ : γ ≠ δ) (t : Tangle γ),
        NearLitterPerm.ofBot (allowableDerivative δ ⊥ (bot_lt_coe _) (πs δ hδ)) •
          fuzz (Subtype.coe_injective.ne hγδ) t =
        fuzz (Subtype.coe_injective.ne hγδ) (πs γ hγ • t)) →
      Allowable (β : IicBot α)
  allowableOfSmulFuzz_derivative_eq {β : Iic α} {πs} {h} (γ : IioBot α)
    (hγ : (γ : TypeIndex) < β) :
    allowableDerivative β γ hγ (allowableOfSmulFuzz β πs h) = πs γ hγ

export Phase2Assumptions (allowableDerivative allowableDerivative_eq smul_designatedSupport
  smul_fuzz allowableOfSmulFuzz allowableOfSmulFuzz_derivative_eq)

variable {α} [Phase2Assumptions α]

noncomputable def Allowable.derivative {β : IicBot α} :
    ∀ {γ : IicBot α}, Quiver.Path (β : TypeIndex) γ → Allowable β →* Allowable γ :=
  @Path.iicRec _ α β (fun δ _ => Allowable β →* Allowable δ) (MonoidHom.id _) fun γ δ _ h =>
    (allowableDerivative γ δ h).comp

@[simp]
theorem Allowable.derivative_nil {β : IicBot α} :
    Allowable.derivative (Quiver.Path.nil : Quiver.Path (β : TypeIndex) β) = MonoidHom.id _ :=
  rfl

@[simp]
theorem Allowable.derivative_eq {β γ : IicBot α} (h : γ < β) :
    allowableDerivative β γ h = Allowable.derivative (Quiver.Path.nil.cons h) :=
  rfl

theorem Allowable.derivative_cons {β γ δ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) :
    (allowableDerivative γ δ h).comp (Allowable.derivative A) = Allowable.derivative (A.cons h) :=
  rfl

theorem Allowable.derivative_cons_apply (β γ δ : IicBot α) (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) (π : Allowable β) :
    allowableDerivative γ δ h (Allowable.derivative A π) = Allowable.derivative (A.cons h) π :=
  rfl

theorem Allowable.derivative_cons_apply' (β : Iio α) (γ : Iic α) (δ : Iio α)
    (A : Quiver.Path (β : TypeIndex) γ) (h : (δ : TypeIndex) < γ) (π : Allowable β) :
    allowableDerivative (γ : IicBot α) (δ : IicBot α) h
      (Allowable.derivative
        (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) =
    @Allowable.derivative _ _ _ _ (β : IicBot α) (δ : IicBot α) (A.cons h) π :=
  rfl

theorem Allowable.derivative_cons_apply'' (β : Iio α) (γ : Iic α)
    (A : Quiver.Path (β : TypeIndex) γ) (π : Allowable β) :
    allowableDerivative (γ : IicBot α) (⊥ : IicBot α) (bot_lt_coe _)
      (Allowable.derivative
        (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) =
    @Allowable.derivative _ _ _ _ (β : IicBot α) (⊥ : IicBot α) (A.cons <| bot_lt_coe _) π :=
  rfl

theorem Allowable.derivative_derivative {β γ δ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (B : Quiver.Path (γ : TypeIndex) δ) (π : Allowable β) :
    Allowable.derivative B (Allowable.derivative A π) = Allowable.derivative (A.comp B) π := by
  obtain ⟨γ, hγ⟩ := γ
  obtain ⟨δ, hδ⟩ := δ
  change Quiver.Path γ δ at B
  induction B with
  | nil => simp only [Quiver.Path.comp_nil, Allowable.derivative_nil, MonoidHom.id_apply]
  | cons B H ih =>
    rw [Quiver.Path.comp_cons]
    rw [← Allowable.derivative_cons (show Quiver.Path
      ((⟨γ, hγ⟩ : IicBot α) : TypeIndex)
      ((⟨_, le_trans (le_of_path B) hγ⟩ : IicBot α) : TypeIndex)
      from B)]
    rw [MonoidHom.coe_comp, Function.comp_apply, ih, Allowable.derivative_cons_apply]

@[simp]
theorem Allowable.toStructPerm_derivative {β γ : IicBot α}
    (A : Quiver.Path (β : TypeIndex) γ) (π : Allowable β) :
    Allowable.toStructPerm (Allowable.derivative A π) =
    StructPerm.derivative A (Allowable.toStructPerm π) := by
  obtain ⟨γ, hγ⟩ := γ
  change Quiver.Path (β : TypeIndex) γ at A
  induction A with
  | nil => rw [StructPerm.derivative_nil, Allowable.derivative_nil, MonoidHom.id_apply]
  | cons A h ih =>
      change toStructPerm (allowableDerivative _ _ _ (derivative _ π)) = _
      rw [StructPerm.derivative_cons, ← allowableDerivative_eq, ih]
      rfl

@[simp]
theorem Allowable.toStructPerm_apply {β : IicBot α}
    (A : Quiver.Path (β : TypeIndex) (⊥ : IicBot α)) (π : Allowable β) :
    NearLitterPerm.ofBot (Allowable.derivative A π) = Allowable.toStructPerm π A :=
  congr_fun (Allowable.toStructPerm_derivative A π) Quiver.Path.nil

theorem smul_mem_designatedSupport {β : Iio α} {c : SupportCondition β} {t : Tangle β}
    (h : c ∈ designatedSupport t) (π : Allowable β) : π • c ∈ designatedSupport (π • t) :=
  (Set.ext_iff.mp (smul_designatedSupport (show Tangle (β : Iic α) from t) π)
        ((show Allowable (β : Iic α) from π) • c)).mp
    ⟨c, h, rfl⟩

@[simp]
theorem ofBot_derivative' {β : IicBot α} {hβ : ⊥ < β} {π : Allowable β} :
    NearLitterPerm.ofBot (allowableDerivative β ⊥ hβ π) =
    Allowable.toStructPerm π (Quiver.Hom.toPath hβ) :=
  (congr_fun (allowableDerivative_eq β ⊥ hβ π) Quiver.Path.nil).symm

theorem exists_cons_of_length_ne_zero {V : Type _} [Quiver V] {x y : V}
    (p : Quiver.Path x y) (h : p.length ≠ 0) :
    ∃ t : V, ∃ q : Quiver.Path x t, ∃ e : t ⟶ y, p = q.cons e := by
  cases p
  · cases h rfl
  · exact ⟨_, _, _, rfl⟩

theorem ofBot_derivative {β : IicBot α} {π : Allowable β}
    (A : Quiver.Path (β : TypeIndex) (⊥ : IicBot α)) :
    NearLitterPerm.ofBot (Allowable.derivative A π) = Allowable.toStructPerm π A := by
  dsimp only [Iic.coe_bot] at A
  by_cases A.length = 0
  · have : β = ⊥ := Subtype.coe_injective (Quiver.Path.eq_of_length_zero A h)
    cases this
    cases path_eq_nil A
    rfl
  · obtain ⟨γ, A, h', rfl⟩ := exists_cons_of_length_ne_zero A h
    have := Allowable.derivative_cons
      (show Quiver.Path (β : TypeIndex) (⟨γ, ?_⟩ : IicBot α) from A)
      (show ⊥ < ⟨γ, _⟩ from h')
    rw [← this, MonoidHom.comp_apply, ofBot_derivative', Allowable.toStructPerm_derivative]
    simp only [StructPerm.derivative_apply, Quiver.Hom.comp_toPath]
    exact le_trans (le_of_path A) β.prop

@[simp]
theorem ofBot_smul {X : Type _} [MulAction NearLitterPerm X] (π : Allowable ⊥) (x : X) :
    π • x = NearLitterPerm.ofBot π • x :=
  rfl

@[simp]
theorem derivative_bot_smul_atom {β : IicBot α}
    (π : Allowable β) (A : Quiver.Path (β : TypeIndex) (⊥ : IicBot α)) (a : Tangle ⊥) :
    Allowable.derivative A π • a = Allowable.toStructPerm π A • (show Atom from a) := by
  rw [← ofBot_derivative]
  rfl

theorem toStructPerm_smul_fuzz (β : IicBot α) (γ : IioBot α) (δ : Iio α)
    (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (π : Allowable β)
    (t : Tangle γ) :
    Allowable.toStructPerm π ((Quiver.Path.nil.cons hδ).cons (bot_lt_coe _)) •
      fuzz (Subtype.coe_injective.ne hγδ) t =
    fuzz (Subtype.coe_injective.ne hγδ) (allowableDerivative β γ hγ π • t) := by
  have := congr_fun (allowableDerivative_eq β δ hδ π) (Quiver.Hom.toPath (bot_lt_coe _))
  simp only [StructPerm.derivative_apply, Quiver.Hom.comp_toPath] at this
  rw [this, ← smul_fuzz γ δ hγ hδ hγδ π t, ofBot_derivative']

end ConNF
