import ConNF.FMap

open Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}] [PositionData] (α : Λ)

instance coreTangleDataIic (β : Iio α) [inst : CoreTangleData (β : Iic α)] : CoreTangleData β :=
  inst

instance coreTangleDataIic' (β : Iic α) [inst : CoreTangleData β] : CoreTangleData (β : Λ) :=
  inst

instance coreTangleDataIio' (β : Iio α) [inst : CoreTangleData β] : CoreTangleData (β : Λ) :=
  inst

instance almostTangleDataIio (β : Iio α) [inst_0 : CoreTangleData β]
    [inst : @AlmostTangleData _ (β : Iic α) inst_0] : AlmostTangleData β :=
  inst

instance positionedTangleDataIio (β : Iio α) [CoreTangleData β] [inst : PositionedTangleData β] :
    PositionedTangleData (β : Λ) :=
  inst

class Phase2Data where
  lowerCoreTangleData : ∀ β : Iic α, CoreTangleData β
  lowerPositionedTangleData : ∀ β : Iio α, PositionedTangleData β
  lowerAlmostTangleData : ∀ β : Iic α, AlmostTangleData β
  lowerTangleData : ∀ β : Iio α, TangleData β

namespace Phase2Data

variable [Phase2Data α] {α} {β : Iic α} {γ : Iio α}

instance coreTangleData : CoreTangleData β :=
  lowerCoreTangleData β

instance positionedTangleData : PositionedTangleData γ :=
  lowerPositionedTangleData γ

instance almostTangleData : AlmostTangleData β :=
  lowerAlmostTangleData β

instance tangleData : TangleData γ :=
  lowerTangleData γ

noncomputable instance IicBotCoreTangleData : ∀ β : IicBot α, CoreTangleData β
  | ⟨⊥, _⟩ => Bot.coreTangleData
  | ⟨(β : Λ), hβ⟩ => lowerCoreTangleData ⟨β, coe_le_coe.mp hβ⟩

noncomputable instance IioBotCoreTangleData (β : IioBot α) : CoreTangleData β :=
  show CoreTangleData (⟨β, le_of_lt (IioBot.lt β)⟩ : IicBot α) from inferInstance

noncomputable instance IioBotPositionedTangleData : ∀ β : IioBot α, PositionedTangleData β
  | ⟨⊥, _⟩ => Bot.positionedTangleData
  | ⟨(β : Λ), hβ⟩ => lowerPositionedTangleData ⟨β, coe_lt_coe.mp hβ⟩

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
  smul_fMap {β : IicBot α} (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β)
    (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (π : Allowable β) (t : Tangle γ) :
    allowableDerivative β δ hδ π • fMap (Subtype.coe_injective.ne hγδ) t =
      fMap (Subtype.coe_injective.ne hγδ) (allowableDerivative β γ hγ π • t)
  allowableOfSmulFMap (β : Iic α) (πs : ∀ γ : IioBot α, (γ : TypeIndex) < β → Allowable γ) :
    (∀ (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β)
        (hγδ : γ ≠ δ) (t : Tangle γ),
        πs δ hδ • fMap (Subtype.coe_injective.ne hγδ) t =
          fMap (Subtype.coe_injective.ne hγδ) (πs γ hγ • t)) →
      Allowable (β : IicBot α)
  allowableOfSmulFMap_derivative_eq {β : Iic α} {πs} {h} (γ : IioBot α)
    (hγ : (γ : TypeIndex) < β) :
    allowableDerivative β γ hγ (allowableOfSmulFMap β πs h) = πs γ hγ

export Phase2Assumptions (allowableDerivative allowableDerivative_eq smul_designatedSupport
  smul_fMap allowableOfSmulFMap allowableOfSmulFMap_derivative_eq)

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
theorem Allowable.derivative_cons {β γ δ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) :
    Allowable.derivative (A.cons h) = (allowableDerivative γ δ h).comp (Allowable.derivative A) :=
  rfl

theorem Allowable.derivative_cons_apply (β γ δ : IicBot α) (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) (π : Allowable β) :
    Allowable.derivative (A.cons h) π = allowableDerivative γ δ h (Allowable.derivative A π) :=
  rfl

theorem Allowable.derivative_cons_apply' (β : Iio α) (γ : Iic α) (δ : Iio α)
    (A : Quiver.Path (β : TypeIndex) γ) (h : (δ : TypeIndex) < γ) (π : Allowable β) :
    @Allowable.derivative _ _ _ _ (β : IicBot α) (δ : IicBot α) (A.cons h) π =
      allowableDerivative (γ : IicBot α) (δ : IicBot α) h
        (Allowable.derivative
          (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) :=
  rfl

theorem Allowable.derivative_cons_apply'' (β : Iio α) (γ : Iic α)
    (A : Quiver.Path (β : TypeIndex) γ) (π : Allowable β) :
    @Allowable.derivative _ _ _ _ (β : IicBot α) (⊥ : IicBot α) (A.cons <| bot_lt_coe _) π =
      allowableDerivative (γ : IicBot α) (⊥ : IicBot α) (bot_lt_coe _)
        (Allowable.derivative
          (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) :=
  rfl

theorem Allowable.derivative_eq {β γ : IicBot α} (h : γ < β) :
    allowableDerivative β γ h = Allowable.derivative (Quiver.Path.nil.cons h) :=
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
    rw [Allowable.derivative_cons
        (show
          Quiver.Path ((⟨γ, hγ⟩ : IicBot α) : TypeIndex)
            ((⟨_, le_trans (le_of_path B) hγ⟩ : IicBot α) : TypeIndex)
          from B)]
    rw [MonoidHom.coe_comp, Function.comp_apply, ih, ← Allowable.derivative_cons_apply]

theorem Allowable.derivative_toStructPerm {β γ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (π : Allowable β) :
    StructPerm.derivative A (Allowable.toStructPerm π) =
    Allowable.toStructPerm (Allowable.derivative A π) := by
  obtain ⟨γ, hγ⟩ := γ
  change Quiver.Path (β : TypeIndex) γ at A
  induction A with
  | nil => rw [StructPerm.derivative_nil, Allowable.derivative_nil, MonoidHom.id_apply]
  | cons A h ih =>
      change _ = toStructPerm (allowableDerivative _ _ _ (derivative _ π))
      rw [StructPerm.derivative_cons, ← allowableDerivative_eq, ih]

theorem Allowable.derivative_smul {β γ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (π : Allowable β) {X : Type _} [MulAction (StructPerm γ) X] (x : X) :
    Allowable.derivative A π • x =
    StructPerm.derivative A (Allowable.toStructPerm π) • x := by
  rw [Allowable.derivative_toStructPerm]
  rfl

-- TODO: Unify next three lemmas.
@[simp]
theorem Allowable.derivative_bot_smul_atom (β : Iic α) (π : Allowable β) (a : Atom) :
    allowableDerivative (iicCoe β) ⊥ (bot_lt_coe (β : Λ)) π • a = π • a := by
  refine Eq.trans ?_ (StructPerm.derivative_bot_smul (Allowable.toStructPerm π) a)
  have := allowableDerivative_eq (iicCoe β) ⊥ (bot_lt_coe _) π
  exact congr_arg₂ (· • ·) this.symm rfl

@[simp]
theorem Allowable.derivative_bot_smul_litter (β : Iic α) (π : Allowable β) (L : Litter) :
    allowableDerivative (iicCoe β) ⊥ (bot_lt_coe (β : Λ)) π • L = π • L := by
  refine Eq.trans ?_ (StructPerm.derivative_bot_smul (Allowable.toStructPerm π) L)
  have := allowableDerivative_eq (iicCoe β) ⊥ (bot_lt_coe _) π
  exact congr_arg₂ (· • ·) this.symm rfl

@[simp]
theorem Allowable.derivative_bot_smul_nearLitter (β : Iic α) (π : Allowable β) (N : NearLitter) :
    allowableDerivative (iicCoe β) ⊥ (bot_lt_coe (β : Λ)) π • N = π • N := by
  refine Eq.trans ?_ (StructPerm.derivative_bot_smul (Allowable.toStructPerm π) N)
  have := allowableDerivative_eq (iicCoe β) ⊥ (bot_lt_coe _) π
  exact congr_arg₂ (· • ·) this.symm rfl

theorem smul_mem_designatedSupport {β : Iio α} {c : SupportCondition β} {t : Tangle β}
    (h : c ∈ designatedSupport t) (π : Allowable β) : π • c ∈ designatedSupport (π • t) :=
  (Set.ext_iff.mp (smul_designatedSupport (show Tangle (β : Iic α) from t) π)
        ((show Allowable (β : Iic α) from π) • c)).mp
    ⟨c, h, rfl⟩

theorem toStructPerm_smul_fMap (β : IicBot α) (γ : IioBot α) (δ : Iio α)
    (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (π : Allowable β)
    (t : Tangle γ) :
    StructPerm.derivative (Quiver.Path.nil.cons hδ) (Allowable.toStructPerm π) •
        fMap (Subtype.coe_injective.ne hγδ) t =
      fMap (Subtype.coe_injective.ne hγδ) (allowableDerivative β γ hγ π • t) := by
  rw [allowableDerivative_eq β δ hδ π]
  exact smul_fMap γ δ hγ hδ hγδ π t

end ConNF
