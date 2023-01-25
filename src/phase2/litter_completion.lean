import phase2.flexible_completion
import phase2.strong_support

open quiver set sum with_bot
open_locale classical

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [core_tangle_cumul α] [positioned_tangle_cumul α]
  [position_data.{}] [almost_tangle_cumul α] [tangle_cumul α] {β : Iio α}
  {γ δ ε : Iio α} (hδ : δ < γ) (hε : ε < γ) (hδε : δ ≠ ε)
  {A : path (β : type_index) γ} {t : tangle δ}
  (H : hypothesis ⟨inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
    (A.cons (coe_lt hε)).cons (bot_lt_coe _)⟩)

lemma atom_mem_constrains_closure (a : atom) (B : extended_index δ)
  (ha : (⟨inl a, B⟩ : support_condition δ) ∈
    constrains_closure α (designated_support t : set (support_condition δ))) :
  relation.trans_gen (constrains α β) (inl a, (A.cons (coe_lt hδ)).comp B)
    (inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
      (A.cons (coe_lt hε)).cons (bot_lt_coe _)) :=
begin
  obtain ⟨d, hd₁, hd₂⟩ := ha.2,
  exact relation.trans_gen.tail' (refl_trans_gen_constrains_comp hd₂ (A.cons (coe_lt hδ)))
    (constrains.f_map hδ hε hδε A t d hd₁),
end

noncomputable def constrains_closure_atom_map (a : atom) (B : extended_index δ)
  (ha : (⟨inl a, B⟩ : support_condition δ) ∈
    constrains_closure α (designated_support t : set (support_condition δ))) : atom :=
H.atom_image a ((A.cons (coe_lt hδ)).comp B) (atom_mem_constrains_closure hδ hε hδε a B ha)

lemma near_litter_mem_constrains_closure (N : near_litter) (B : extended_index δ)
  (ha : (⟨inr N, B⟩ : support_condition δ) ∈
    constrains_closure α (designated_support t : set (support_condition δ))) :
  relation.trans_gen (constrains α β) (inr N, (A.cons (coe_lt hδ)).comp B)
    (inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
      (A.cons (coe_lt hε)).cons (bot_lt_coe _)) :=
begin
  obtain ⟨d, hd₁, hd₂⟩ := ha.2,
  exact relation.trans_gen.tail' (refl_trans_gen_constrains_comp hd₂ (A.cons (coe_lt hδ)))
    (constrains.f_map hδ hε hδε A t d hd₁),
end

noncomputable def constrains_closure_near_litter_map (N : near_litter) (B : extended_index δ)
  (hN : (⟨inr N, B⟩ : support_condition δ) ∈
    constrains_closure α (designated_support t : set (support_condition δ))) : near_litter :=
H.near_litter_image N ((A.cons (coe_lt hδ)).comp B)
  (near_litter_mem_constrains_closure hδ hε hδε N B hN)

/-- A litter that is not allowed to be used as a sandbox because it appears somewhere that
we need to preserve. -/
@[mk_iff] inductive banned_litter (B : extended_index δ) : litter → Prop
| support_atom (a : atom) :
    (⟨inl a, B⟩ : support_condition δ) ∈
      constrains_closure α (designated_support t : set (support_condition δ)) → banned_litter a.1
| support_litter (L : litter) :
    (⟨inr L.to_near_litter, B⟩ : support_condition δ) ∈
      constrains_closure α (designated_support t : set (support_condition δ)) → banned_litter L
| map_atom (a : atom) (h) :
    banned_litter (constrains_closure_atom_map hδ hε hδε H a B h).1
| map_litter (N : near_litter) (h) :
    banned_litter (constrains_closure_near_litter_map hδ hε hδε H N B h).1
| map_diff (N : near_litter) (h) (a : atom) :
    a ∈ (constrains_closure_near_litter_map hδ hε hδε H N B h : set atom) \
      litter_set (constrains_closure_near_litter_map hδ hε hδε H N B h).1 → banned_litter a.1

lemma banned_litter_small (B : extended_index δ) : small {L | banned_litter hδ hε hδε H B L} :=
begin
  simp only [banned_litter_iff, set_of_or, exists_and_distrib_right],
  refine small.union _ (small.union _ (small.union _ (small.union _ _))),
  { refine lt_of_le_of_lt _ (constrains_closure_small α (designated_support t).small),
    refine ⟨⟨λ a, ⟨_, a.prop.some_spec.1⟩, λ a₁ a₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := a₁.prop.some_spec.2,
    rw h.1 at this,
    exact subtype.coe_injective (this.trans a₂.prop.some_spec.2.symm), },
  { refine lt_of_le_of_lt _ (constrains_closure_small α (designated_support t).small),
    refine ⟨⟨λ L, ⟨_, L.prop⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    exact subtype.coe_injective (litter.to_near_litter_injective h.1), },
  { refine lt_of_le_of_lt _ (constrains_closure_small α (designated_support t).small),
    refine ⟨⟨λ L, ⟨_, L.prop.some_spec.some⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec,
    simp_rw h.1 at this,
    exact subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm), },
  { refine lt_of_le_of_lt _ (constrains_closure_small α (designated_support t).small),
    refine ⟨⟨λ L, ⟨_, L.prop.some_spec.some⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec,
    simp_rw h.1 at this,
    exact subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm), },
  { have : small ⋃ (N : near_litter) (h : (inr N, B) ∈
      constrains_closure α (designated_support t : set (support_condition δ))),
      (constrains_closure_near_litter_map hδ hε hδε H N B h : set atom) \
        litter_set (constrains_closure_near_litter_map hδ hε hδε H N B h).1,
    { refine small.bUnion _ _,
      { refine lt_of_le_of_lt _ (constrains_closure_small α (designated_support t).small),
        refine ⟨⟨λ N, ⟨_, N.prop⟩, λ N₁ N₂ h, _⟩⟩,
        simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
        ext : 1, exact h.1, },
      { intros N hN,
        refine small.mono _ (constrains_closure_near_litter_map hδ hε hδε H N B hN).2.prop,
        exact λ x hx, or.inr hx, }, },
    refine lt_of_le_of_lt _ this,
    refine ⟨⟨λ L, ⟨L.prop.some_spec.some_spec.some, _⟩, λ L₁ L₂ h, _⟩⟩,
    { simp only [mem_Union],
      exact ⟨_, _, L.prop.some_spec.some_spec.some_spec.1⟩, },
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec.some_spec.2,
    rw h at this,
    exact subtype.coe_injective
      (this.trans L₂.prop.some_spec.some_spec.some_spec.2.symm), },
end

/-- An atom and `δ`-extended index is called *without preimage* if it is not mapped to by
anything in the support, but it is in a litter near some near-litter that was mapped to.
Atoms without preimage need to have something map to it, so that the resulting map that we use in
the freedom of action theorem actually maps to the correct near-litter. -/
@[mk_iff] structure without_preimage (a : atom) (B : extended_index δ) : Prop :=
(mem_map : ∃ L h,
  a ∈ litter_set (constrains_closure_near_litter_map hδ hε hδε H (litter.to_near_litter L) B h).1)
(not_mem_map : ∀ L h,
  a ∉ (constrains_closure_near_litter_map hδ hε hδε H (litter.to_near_litter L) B h : set atom))
(not_mem_domain : ∀ b h, a ≠ constrains_closure_atom_map hδ hε hδε H b B h)

lemma without_preimage_small (B : extended_index δ) :
  small {a | without_preimage hδ hε hδε H a B} :=
begin
  simp only [without_preimage_iff, set_of_and],
  rw ← inter_assoc,
  refine small.mono (inter_subset_left _ _) _,
  suffices : small ⋃ (L : litter) (h),
    litter_set (constrains_closure_near_litter_map hδ hε hδε H (litter.to_near_litter L) B h).1 \
      constrains_closure_near_litter_map hδ hε hδε H (litter.to_near_litter L) B h,
  { refine small.mono _ this,
    rintro a ⟨⟨L, hL, ha₁⟩, ha₂⟩,
    simp only [mem_Union],
    exact ⟨L, hL, ha₁, ha₂ _ _⟩, },
  refine small.bUnion _ _,
  { refine lt_of_le_of_lt _ (constrains_closure_small α (designated_support t).small),
    refine ⟨⟨λ L, ⟨_, L.prop⟩, _⟩⟩,
    intros L₁ L₂ h,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff, eq_self_iff_true, and_true,
      litter.to_near_litter_injective.eq_iff, subtype.coe_inj] at h,
    exact h, },
  { intros L hL,
    refine small.mono _
      (constrains_closure_near_litter_map hδ hε hδε H L.to_near_litter B hL).2.prop,
    exact λ x hx, or.inl hx, },
end

end struct_approx

end con_nf
