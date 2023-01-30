import phase1.basic

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

class phase_2_assumptions :=
(lower_core_tangle_data : Π β : Iic α, core_tangle_data β)
(lower_positioned_tangle_data : Π β : Iio α, positioned_tangle_data β)
(lower_almost_tangle_data : Π β : Iic α, almost_tangle_data β)
(lower_tangle_data : Π β : Iio α, tangle_data β)

namespace phase_2_assumptions
variables [phase_2_assumptions α] {α} {β : Iic α} {γ : Iio α}

instance core_tangle_data : core_tangle_data β := lower_core_tangle_data β
instance positioned_tangle_data : positioned_tangle_data γ := lower_positioned_tangle_data γ
instance almost_tangle_data : almost_tangle_data β := lower_almost_tangle_data β
instance tangle_data : tangle_data γ := lower_tangle_data γ

end phase_2_assumptions

end con_nf
