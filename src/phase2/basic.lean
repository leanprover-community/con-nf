import phase1.f_map

open set with_bot

universe u

namespace con_nf
variables [params.{u}] [position_data.{}] (α : Λ)

instance core_tangle_data_Iic (β : Iio α) [inst : core_tangle_data (β : Iic α)] :
  core_tangle_data β := inst

instance core_tangle_data_Iic' (β : Iic α) [inst : core_tangle_data β] :
  core_tangle_data (β : Λ) := inst

instance core_tangle_data_Iio' (β : Iio α) [inst : core_tangle_data β] :
  core_tangle_data (β : Λ) := inst

instance almost_tangle_data_Iio (β : Iio α)
  [inst_0 : core_tangle_data β] [inst : @almost_tangle_data _ (β : Iic α) inst_0] :
  almost_tangle_data β := inst

instance positioned_tangle_data_Iio (β : Iio α) [core_tangle_data β]
  [inst : positioned_tangle_data β] :
  positioned_tangle_data (β : Λ) := inst

class phase_2_data :=
(lower_core_tangle_data : Π β : Iic α, core_tangle_data β)
(lower_positioned_tangle_data : Π β : Iio α, positioned_tangle_data β)
(lower_almost_tangle_data : Π β : Iic α, almost_tangle_data β)
(lower_tangle_data : Π β : Iio α, tangle_data β)

namespace phase_2_data
variables [phase_2_data α] {α} {β : Iic α} {γ : Iio α}

/-- By unfolding here, we get better definitional equality between e.g.
`allowable ((β : Iic α) : Iic_index α)` and `allowable (β : Iic α)`. -/

instance core_tangle_data : core_tangle_data β :=
@id _ lower_core_tangle_data ⟨β, β.prop⟩
instance positioned_tangle_data : positioned_tangle_data γ :=
@id _ lower_positioned_tangle_data ⟨γ, γ.prop⟩
instance almost_tangle_data : almost_tangle_data β :=
@id _ lower_almost_tangle_data ⟨β, β.prop⟩
instance tangle_data : tangle_data γ :=
@id _ lower_tangle_data ⟨γ, γ.prop⟩

noncomputable instance Iic_index_core_tangle_data : Π (β : Iic_index α), core_tangle_data β
| ⟨⊥, h⟩ := bot.core_tangle_data
| ⟨(β : Λ), hβ⟩ := lower_core_tangle_data ⟨β, coe_le_coe.mp hβ⟩

noncomputable instance Iio_index_core_tangle_data (β : Iio_index α) :
  core_tangle_data β :=
show core_tangle_data (⟨β, le_of_lt β.prop⟩ : Iic_index α), from infer_instance

noncomputable instance Iio_index_positioned_tangle_data :
  Π β : Iio_index α, positioned_tangle_data β
| ⟨⊥, h⟩ := bot.positioned_tangle_data
| ⟨(β : Λ), hβ⟩ := lower_positioned_tangle_data ⟨β, coe_lt_coe.mp hβ⟩

instance has_coe_Iio_Iic_index : has_coe (Iio α) (Iic_index α) :=
⟨λ β, ⟨some β, le_of_lt (with_bot.coe_lt_coe.mpr β.prop)⟩⟩
instance has_coe_Iio_index_Iic_index : has_coe (Iio_index α) (Iic_index α) :=
⟨λ β, ⟨β, le_of_lt β.prop⟩⟩

instance [phase_2_data α] {X : Type*} {δ : Iio α} [inst : mul_action (allowable δ) X] :
  mul_action (allowable (Iio_coe δ)) X := inst

instance mul_action_type_index {δ : Iio α} : mul_action (allowable δ) (tangle (δ : Λ)) :=
show mul_action (allowable δ) (tangle δ), from infer_instance

noncomputable instance mul_action_Iio_index {δ : Iio_index α} :
  mul_action (allowable (δ : Iic_index α)) (tangle δ) :=
show mul_action (allowable δ) (tangle δ), from infer_instance

end phase_2_data

class phase_2_assumptions extends phase_2_data α :=
(allowable_derivative : Π (β : Iic_index α) (γ : Iic_index α) (hγ : (γ : type_index) < β),
  allowable β →* allowable γ)
(allowable_derivative_eq : ∀ (β : Iic_index α) (γ : Iic_index α) (hγ : (γ : type_index) < β)
  (π : allowable β),
  struct_perm.derivative (quiver.path.nil.cons hγ) π.to_struct_perm =
    (allowable_derivative β γ hγ π).to_struct_perm)
(smul_f_map {β : Iic_index α} (γ : Iio_index α) (δ : Iio α)
  (hγ : (γ : type_index) < β) (hδ : (δ : type_index) < β) (hγδ : γ ≠ δ)
  (π : allowable β) (t : tangle γ) :
  (allowable_derivative β δ hδ π) •
    f_map (subtype.coe_injective.ne hγδ) t =
    f_map (subtype.coe_injective.ne hγδ) (allowable_derivative β γ hγ π • t))

export phase_2_assumptions (allowable_derivative allowable_derivative_eq smul_f_map)

variables {α} [phase_2_assumptions α]

noncomputable def allowable.derivative {β : Iic_index α} : Π {γ : Iic_index α}
  (A : quiver.path (β : type_index) γ), allowable β →* allowable γ :=
@path.Iic_rec _ α β (λ δ A, allowable β →* allowable δ) (monoid_hom.id _)
  (λ γ δ A h, (allowable_derivative γ δ h).comp)

@[simp] lemma allowable.derivative_nil {β : Iic_index α} :
  allowable.derivative (quiver.path.nil : quiver.path (β : type_index) β) = monoid_hom.id _ :=
by rw [allowable.derivative, path.Iic_rec_nil]

@[simp] lemma allowable.derivative_cons {β γ δ : Iic_index α}
  (A : quiver.path (β : type_index) γ) (h : δ < γ) :
  allowable.derivative (A.cons h) = (allowable_derivative γ δ h).comp (allowable.derivative A) :=
by rw [allowable.derivative, path.Iic_rec_cons]

lemma allowable.derivative_to_struct_perm {β γ : Iic_index α} (A : quiver.path (β : type_index) γ)
  (π : allowable β) :
  struct_perm.derivative A π.to_struct_perm = (allowable.derivative A π).to_struct_perm :=
begin
  revert π A γ,
  refine path.Iic_rec _ _,
  { intro π,
    simp only [struct_perm.derivative_nil, allowable.derivative_nil, monoid_hom.id_apply], },
  { intros γ δ A h ih π,
    rw [allowable.derivative_cons, monoid_hom.coe_comp, function.comp_app,
      ← allowable_derivative_eq, ← ih π, struct_perm.derivative_derivative,
      quiver.path.comp_cons, quiver.path.comp_nil], },
end

lemma to_struct_perm_smul_f_map {β : Iic_index α} (γ : Iio_index α) (δ : Iio α)
  (hγ : (γ : type_index) < β) (hδ : (δ : type_index) < β) (hγδ : γ ≠ δ)
  (π : allowable β) (t : tangle γ) :
  (struct_perm.derivative (quiver.path.nil.cons hδ) π.to_struct_perm) •
    f_map (subtype.coe_injective.ne hγδ) t =
    f_map (subtype.coe_injective.ne hγδ) (allowable_derivative (β : Iic_index α) γ hγ π • t) :=
begin
  rw allowable_derivative_eq β δ hδ π,
  exact smul_f_map γ δ hγ hδ hγδ π t,
end

end con_nf
