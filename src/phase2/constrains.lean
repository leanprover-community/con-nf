import order.extension.well
import phase1.A_map

/-!
# Constraints
Support conditions can be said to *constrain* each other in a number of ways.
This is detailed below. The `constrains` relation is well-founded.
-/

open quiver set sum with_bot
open_locale classical

universe u

namespace con_nf
variables [params.{u}]

section extended_index
variable {α : type_index}

/-!
We construct a well-order on the type of extended indices.
The details are unimportant, we probably don't actually need AC here.
-/

instance : has_lt (extended_index α) := ⟨(well_founded.exists_well_order_ge empty_wf).some⟩
instance : is_well_order (extended_index α) (<) :=
(well_founded.exists_well_order_ge empty_wf).some_spec.2
instance : has_well_founded (extended_index α) := is_well_order.to_has_well_founded
noncomputable instance : linear_order (extended_index α) := linear_order_of_STO (<)

end extended_index

variables {α : Λ} [core_tangle_cumul α] [positioned_tangle_cumul α]
  [position_data.{}] [almost_tangle_cumul α] [tangle_cumul α] {β : Λ}

lemma coe_ne' {γ : Iio α} {β : Iio α} : γ ≠ β → (γ : Λ) ≠ (β : Λ) :=
by contrapose!; simp only [subtype.coe_inj, imp_self]

lemma coe_lt {γ : Iio α} {β : Iio α} : γ < β → (γ : type_index) < (β : type_index) :=
begin
  intro h,
  cases β,
  cases γ,
  simpa only [coe_coe, subtype.coe_mk, coe_lt_coe, subtype.mk_lt_mk] using h,
end

variables (α) (β)

/--
Support conditions can be said to *constrain* each other in a number of ways. This is discussed
in the "freedom of action discussion".
1. `⟨L, A⟩ ≺ ⟨a, A⟩` when `a ∈ L` and `L` is a litter. We can say that an atom is constrained by the
    litter it belongs to.
2. `⟨N°, A⟩ ≺ ⟨N, A⟩` when `N` is a near-litter not equal to its corresponding litter `N°`.
3. `⟨a, A⟩ ≺ ⟨N, A⟩` for all `a ∈ N ∆ N°`.
4. `⟨x, A ≫ (γ ⟶ δ) ≫ B⟩ ≺ ⟨f_{γ,δ}(t), A ≫ (γ ⟶ ε) ≫ (ε ⟶ ⊥)⟩` for all paths `A : β ⟶ γ` and
    `δ, ε < γ` with `δ ≠ ε`, `t ∈ τ_γ`, where `⟨x, B⟩` lies in the designated `δ`-support of `t`.
-/
@[mk_iff] inductive constrains : support_condition β → support_condition β → Prop
| atom (a : atom) (A : extended_index β) :
    constrains ⟨inr a.1.to_near_litter, A⟩ ⟨inl a, A⟩
| near_litter (N : near_litter) (hN : litter_set N.fst ≠ N.snd) (A : extended_index β) :
    constrains ⟨inr N.fst.to_near_litter, A⟩ ⟨inr N, A⟩
| symm_diff (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd) (A : extended_index β) :
    constrains ⟨inl a, A⟩ ⟨inr N, A⟩
| f_map ⦃γ : Iio α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : δ < γ) (hε : ε < γ) (hδε : δ ≠ ε)
    (A : path (β : type_index) γ) (t : tangle δ) (c ∈ (designated_support t).carrier) :
    constrains
      ⟨c.fst, path.comp (A.cons (coe_lt hδ)) c.snd⟩
      ⟨inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
        (A.cons (coe_lt hε)).cons (bot_lt_coe _)⟩
| f_map_bot ⦃γ : Iio α⦄ ⦃ε : Iio α⦄ (hε : ε < γ)
    (A : path (β : type_index) γ) (a : atom) :
    constrains
      ⟨inl a, A.cons (bot_lt_coe _)⟩
      ⟨inr (f_map (show (⊥ : type_index) ≠ (ε : Λ), from bot_ne_coe) a).to_near_litter,
        (A.cons (coe_lt hε)).cons (bot_lt_coe _)⟩

/-! We declare new notation for the "constrains" relation on support conditions. -/
notation c ` ≺[`:50 α `] ` d:50 := constrains α _ c d

instance : has_lt (support_condition β) :=
⟨prod.lex (inv_image (<) (λ c, c.elim typed_atom_position typed_near_litter_position)) (<)⟩

instance : is_well_founded (support_condition β) (<) :=
prod.lex.is_well_founded

lemma constrains_subrelation : subrelation (constrains α β) (<) :=
begin
  rintros c d h,
  obtain (⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ |
    ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩) := h;
  left,
  { exact litter_lt a.1 a rfl, },
  { refine litter_lt_near_litter N _,
    contrapose! hN,
    rw ← hN,
    refl, },
  { exact symm_diff_lt_near_litter N a ha, },
  { have := f_map_position (coe_ne_coe.mpr $ coe_ne' hδε) t _ (is_near_litter_litter_set _),
    rw tangle_data.typed_near_litter_position_eq at this,
    refine lt_of_le_of_lt _ this,
    convert tangle_data.support_le (show tangle (h_δ : Λ), from t) _ hc, },
  { simp only [inv_image, elim_inr],
    convert typed_atom_position_lt_f_map a,
    rw tangle_data.typed_near_litter_position_eq (f_map bot_ne_coe a).to_near_litter,
    apply_instance, },
end

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `⟨x, A⟩ ≺ ⟨y, B⟩`,
then `x < y` in `µ`, under the `typed_near_litter` or `typed_atom` maps. -/
lemma constrains_wf : well_founded (constrains α β) :=
subrelation.wf (constrains_subrelation α β) (is_well_founded.to_has_well_founded _).wf

instance : has_well_founded (support_condition β) := ⟨constrains α β, constrains_wf α β⟩

@[simp] lemma constrains_atom {c : support_condition β} {a : atom} {A : extended_index β} :
  c ≺[α] ⟨inl a, A⟩ ↔ c = ⟨inr a.1.to_near_litter, A⟩ :=
begin
  split,
  { rintro ⟨⟩, refl, },
  { rintro rfl, exact constrains.atom a A, },
end

end con_nf
