import ConNF.Phase1.FMap

#align_import phase2.basic

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

/-- By unfolding here, we get better definitional equality between e.g.
`allowable ((β : Iic α) : Iic_index α)` and `allowable (β : Iic α)`. -/
instance coreTangleData : CoreTangleData β :=
  @id _ lowerCoreTangleData ⟨β, β.Prop⟩

instance positionedTangleData : PositionedTangleData γ :=
  @id _ lowerPositionedTangleData ⟨γ, γ.Prop⟩

instance almostTangleData : AlmostTangleData β :=
  @id _ lowerAlmostTangleData ⟨β, β.Prop⟩

instance tangleData : TangleData γ :=
  @id _ lowerTangleData ⟨γ, γ.Prop⟩

noncomputable instance IicBotCoreTangleData : ∀ β : IicBot α, CoreTangleData β
  | ⟨⊥, h⟩ => Bot.coreTangleData
  | ⟨(β : Λ), hβ⟩ => lowerCoreTangleData ⟨β, coe_le_coe.mp hβ⟩

noncomputable instance IioBotCoreTangleData (β : IioBot α) : CoreTangleData β :=
  show CoreTangleData (⟨β, le_of_lt β.Prop⟩ : IicBot α) from inferInstance

noncomputable instance IioBotPositionedTangleData : ∀ β : IioBot α, PositionedTangleData β
  | ⟨⊥, h⟩ => Bot.positionedTangleData
  | ⟨(β : Λ), hβ⟩ => lowerPositionedTangleData ⟨β, coe_lt_coe.mp hβ⟩

instance hasCoeIioIicIndex : Coe (Iio α) (IicBot α) :=
  ⟨fun β => ⟨some β, le_of_lt (WithBot.coe_lt_coe.mpr β.Prop)⟩⟩

instance hasCoeIioIndexIicIndex : Coe (IioBot α) (IicBot α) :=
  ⟨fun β => ⟨β, le_of_lt β.Prop⟩⟩

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
    ∀ (β : IicBot α) (γ : IicBot α) (hγ : (γ : TypeIndex) < β), Allowable β →* Allowable γ
  allowableDerivative_eq :
    ∀ (β : IicBot α) (γ : IicBot α) (hγ : (γ : TypeIndex) < β) (π : Allowable β),
      StructPerm.derivative (Quiver.Path.nil.cons hγ) π.toStructPerm =
        (allowable_derivative β γ hγ π).toStructPerm
  smul_designatedSupport {β : Iic α} (t : Tangle β) (π : Allowable β) :
    π • (designatedSupport t : Set (SupportCondition β)) = designatedSupport (π • t)
  smul_fMap {β : IicBot α} (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β)
    (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (π : Allowable β) (t : Tangle γ) :
    allowable_derivative β δ hδ π • fMap (Subtype.coe_injective.Ne hγδ) t =
      fMap (Subtype.coe_injective.Ne hγδ) (allowable_derivative β γ hγ π • t)
  allowableOfSmulFMap (β : Iic α) (πs : ∀ γ : IioBot α, (γ : TypeIndex) < β → Allowable γ) :
    (∀ (γ : IioBot α) (δ : Iio α) (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β)
        (hγδ : γ ≠ δ) (t : Tangle γ),
        πs δ hδ • fMap (Subtype.coe_injective.Ne hγδ) t =
          fMap (Subtype.coe_injective.Ne hγδ) (πs γ hγ • t)) →
      Allowable (β : IicBot α)
  allowableOfSmulFMap_derivative_eq {β : Iic α} {πs} {h} (γ : IioBot α)
    (hγ : (γ : TypeIndex) < β) :
    allowable_derivative β γ hγ (allowable_of_smul_f_map β πs h) = πs γ hγ

export
  Phase2Assumptions (allowableDerivative allowableDerivative_eq smul_designatedSupport smul_fMap allowableOfSmulFMap allowableOfSmulFMap_derivative_eq)

variable {α} [Phase2Assumptions α]

noncomputable def Allowable.derivative {β : IicBot α} :
    ∀ {γ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ), Allowable β →* Allowable γ :=
  @Path.iicRec _ α β (fun δ A => Allowable β →* Allowable δ) (MonoidHom.id _) fun γ δ A h =>
    (allowableDerivative γ δ h).comp

@[simp]
theorem Allowable.derivative_nil {β : IicBot α} :
    Allowable.derivative (Quiver.Path.nil : Quiver.Path (β : TypeIndex) β) = MonoidHom.id _ := by
  rw [allowable.derivative, path.Iic_rec_nil]

@[simp]
theorem Allowable.derivative_cons {β γ δ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) :
    Allowable.derivative (A.cons h) = (allowableDerivative γ δ h).comp (Allowable.derivative A) :=
  by rw [allowable.derivative, path.Iic_rec_cons]

theorem Allowable.derivative_cons_apply (β γ δ : IicBot α) (A : Quiver.Path (β : TypeIndex) γ)
    (h : δ < γ) (π : Allowable β) :
    Allowable.derivative (A.cons h) π = allowableDerivative γ δ h (Allowable.derivative A π) := by
  rw [allowable.derivative_cons] <;> rfl

theorem Allowable.derivative_cons_apply' (β : Iio α) (γ : Iic α) (δ : Iio α)
    (A : Quiver.Path (β : TypeIndex) γ) (h : (δ : TypeIndex) < γ) (π : Allowable β) :
    @Allowable.derivative _ _ _ _ (β : IicBot α) (δ : IicBot α) (A.cons h) π =
      allowableDerivative (γ : IicBot α) (δ : IicBot α) h
        (Allowable.derivative
          (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) :=
  by rw [← allowable.derivative_cons_apply]

theorem Allowable.derivative_cons_apply'' (β : Iio α) (γ : Iic α)
    (A : Quiver.Path (β : TypeIndex) γ) (π : Allowable β) :
    @Allowable.derivative _ _ _ _ (β : IicBot α) (⊥ : IicBot α) (A.cons <| bot_lt_coe _) π =
      allowableDerivative (γ : IicBot α) (⊥ : IicBot α) (bot_lt_coe _)
        (Allowable.derivative
          (show Quiver.Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from A) π) :=
  by rw [← allowable.derivative_cons_apply] <;> rfl

theorem Allowable.derivative_eq {β γ : IicBot α} (h : γ < β) :
    allowableDerivative β γ h = Allowable.derivative (Quiver.Path.nil.cons h) := by
  rw [allowable.derivative_cons, allowable.derivative_nil, MonoidHom.comp_id]

theorem Allowable.derivative_derivative {β γ δ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (B : Quiver.Path (γ : TypeIndex) δ) (π : Allowable β) :
    Allowable.derivative B (Allowable.derivative A π) = Allowable.derivative (A.comp B) π :=
  by
  obtain ⟨γ, hγ⟩ := γ
  obtain ⟨δ, hδ⟩ := δ
  change Quiver.Path γ δ at B
  induction' B with ε ζ B h ih
  · simp only [Quiver.Path.comp_nil, allowable.derivative_nil, MonoidHom.id_apply]
  · simp only [Quiver.Path.comp_cons]
    rw [allowable.derivative_cons
        (show
          Quiver.Path ((⟨γ, hγ⟩ : Iic_index α) : type_index)
            ((⟨ε, le_trans (le_of_path B) hγ⟩ : Iic_index α) : type_index)
          from B)]
    simp only [MonoidHom.coe_comp, Function.comp_apply, ih, ← allowable.derivative_cons_apply]

theorem Allowable.derivative_toStructPerm {β γ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (π : Allowable β) :
    StructPerm.derivative A π.toStructPerm = (Allowable.derivative A π).toStructPerm :=
  by
  revert π A γ
  refine' path.Iic_rec _ _
  · intro π
    simp only [struct_perm.derivative_nil, allowable.derivative_nil, MonoidHom.id_apply]
  · intro γ δ A h ih π
    rw [allowable.derivative_cons, MonoidHom.coe_comp, Function.comp_apply, ←
      allowable_derivative_eq, ← ih π, struct_perm.derivative_derivative, Quiver.Path.comp_cons,
      Quiver.Path.comp_nil]

theorem Allowable.derivative_smul {β γ : IicBot α} (A : Quiver.Path (β : TypeIndex) γ)
    (π : Allowable β) {X : Type _} [MulAction (StructPerm γ) X] (x : X) :
    Allowable.derivative A π • x = StructPerm.derivative A π.toStructPerm • x := by
  rw [allowable.derivative_to_struct_perm] <;> rfl

-- TODO: Unify next three lemmas.
@[simp]
theorem Allowable.derivative_bot_smul_atom (β : Iic α) (π : Allowable β) (a : Atom) :
    allowableDerivative (iicCoe β) ⊥ (bot_lt_coe β) π • a = π • a :=
  by
  refine' Eq.trans _ (struct_perm.derivative_bot_smul π.to_struct_perm a)
  have := allowable_derivative_eq (Iic_coe β) ⊥ (bot_lt_coe _) π
  refine' Eq.trans _ (congr_arg₂ (· • ·) this.symm rfl)
  rfl

@[simp]
theorem Allowable.derivative_bot_smul_litter (β : Iic α) (π : Allowable β) (L : Litter) :
    allowableDerivative (iicCoe β) ⊥ (bot_lt_coe β) π • L = π • L :=
  by
  refine' Eq.trans _ (struct_perm.derivative_bot_smul π.to_struct_perm L)
  have := allowable_derivative_eq (Iic_coe β) ⊥ (bot_lt_coe _) π
  refine' Eq.trans _ (congr_arg₂ (· • ·) this.symm rfl)
  rfl

@[simp]
theorem Allowable.derivative_bot_smul_nearLitter (β : Iic α) (π : Allowable β) (N : NearLitter) :
    allowableDerivative (iicCoe β) ⊥ (bot_lt_coe β) π • N = π • N :=
  by
  refine' Eq.trans _ (struct_perm.derivative_bot_smul π.to_struct_perm N)
  have := allowable_derivative_eq (Iic_coe β) ⊥ (bot_lt_coe _) π
  refine' Eq.trans _ (congr_arg₂ (· • ·) this.symm rfl)
  rfl

theorem smul_mem_designatedSupport {β : Iio α} {c : SupportCondition β} {t : Tangle β}
    (h : c ∈ designatedSupport t) (π : Allowable β) : π • c ∈ designatedSupport (π • t) :=
  (Set.ext_iff.mp (smul_designatedSupport (show Tangle (β : Iic α) from t) π)
        ((show Allowable (β : Iic α) from π) • c)).mp
    ⟨c, h, rfl⟩

theorem toStructPerm_smul_fMap (β : IicBot α) (γ : IioBot α) (δ : Iio α)
    (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (π : Allowable β)
    (t : Tangle γ) :
    StructPerm.derivative (Quiver.Path.nil.cons hδ) π.toStructPerm •
        fMap (Subtype.coe_injective.Ne hγδ) t =
      fMap (Subtype.coe_injective.Ne hγδ) (allowableDerivative β γ hγ π • t) :=
  by
  rw [allowable_derivative_eq β δ hδ π]
  exact smul_f_map γ δ hγ hδ hγδ π t

end ConNF
