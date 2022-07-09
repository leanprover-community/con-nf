import data.set.pointwise

open_locale pointwise

section
variables (G H : Type*) {α β : Type*} [has_smul G α] [has_smul G β] [has_smul H α] [has_smul H β]
  [has_smul G H] [is_scalar_tower G H β]

/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
def supports (s : set α) (b : β) := ∀ g : G, (∀ ⦃a⦄, a ∈ s → g • a = a) → g • b = b

variables {s t : set α} {b : β}

lemma supports.mono (h : s ⊆ t) (hs : supports G s b) : supports G t b :=
λ g hg, hs _ $ λ a ha, hg $ h ha

lemma supports_of_mem {a : α} (ha : a ∈ s) : supports G s a := λ g h, h ha

end

variables {G H α β : Type*} [group H] [has_smul G α] [has_smul G β] [mul_action H α] [has_smul H β]
  [has_smul G H] [is_scalar_tower G H β] {s t : set α} {b : β}

lemma supports.smul [smul_comm_class G H β] [smul_comm_class G H α] (g : H) (h : supports G s b) :
  supports G (g • s) (g • b) :=
begin
  rintro g' hg',
  rw [smul_comm, h],
  rintro a ha,
  have := set.ball_image_iff.1 hg' a ha,
  rwa [smul_comm, smul_left_cancel_iff] at this,
end
