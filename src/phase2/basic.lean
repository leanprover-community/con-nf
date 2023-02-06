import phase1.f_map

open set with_bot

noncomputable theory

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

instance core_tangle_data : core_tangle_data β := lower_core_tangle_data β
instance positioned_tangle_data : positioned_tangle_data γ := lower_positioned_tangle_data γ
instance almost_tangle_data : almost_tangle_data β := lower_almost_tangle_data β
instance tangle_data : tangle_data γ := lower_tangle_data γ

noncomputable instance Iic_index_core_tangle_data :
  Π β : Iic_index α, core_tangle_data β
| ⟨⊥, h⟩ := bot.core_tangle_data
| ⟨(β : Λ), hβ⟩ := lower_core_tangle_data ⟨β, coe_le_coe.mp hβ⟩

noncomputable instance Iio_index_core_tangle_data (β : Iio_index α) :
  core_tangle_data β :=
show core_tangle_data (⟨β, le_of_lt β.prop⟩ : Iic_index α), from infer_instance

noncomputable instance Iio_index_positioned_tangle_data :
  Π β : Iio_index α, positioned_tangle_data β
| ⟨⊥, h⟩ := bot.positioned_tangle_data
| ⟨(β : Λ), hβ⟩ := lower_positioned_tangle_data ⟨β, coe_lt_coe.mp hβ⟩

instance [phase_2_data α] {X : Type*} {δ : Iio α} [inst : mul_action (allowable δ) X] :
  mul_action (allowable (Iio_coe δ)) X := inst

instance {δ : Iio α} : mul_action (allowable δ) (tangle (δ : Λ)) :=
show mul_action (allowable δ) (tangle δ), from infer_instance

end phase_2_data

class phase_2_assumptions extends phase_2_data α :=
(allowable_derivative : Π (β : Iic α) (γ : Iio_index α) (hγ : (γ : type_index) < β),
  allowable β →* allowable γ)
(smul_f_map {β : Iic α} (γ : Iio_index α) (δ : Iio α)
  (hγ : (γ : type_index) < β) (hδ : (δ : Iic α) < β) (hγδ : γ ≠ δ)
  (π : allowable β) (t : tangle γ) :
  (allowable_derivative β (δ : Iio_index α) (coe_lt_coe.mpr hδ) π) •
    f_map (subtype.coe_injective.ne hγδ) t =
    f_map (subtype.coe_injective.ne hγδ) (allowable_derivative β γ hγ π • t))

export phase_2_assumptions (allowable_derivative smul_f_map)

end con_nf
