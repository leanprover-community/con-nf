import phase1.A_map
import phase2.basic

/-!
# Constraints
Support conditions can be said to *constrain* each other in a number of ways.
This is detailed below. The `constrains` relation is well-founded.
-/

open quiver set sum with_bot
open_locale cardinal classical

universe u

namespace con_nf
variables [params.{u}]

section extended_index
variable {α : type_index}

/-!
We construct a well-order on the type of extended indices.
The details are unimportant, we probably don't actually need AC here.
-/

instance : has_lt (extended_index α) := ⟨well_ordering_rel⟩
instance : is_well_order (extended_index α) (<) := well_ordering_rel.is_well_order
instance : has_well_founded (extended_index α) := is_well_order.to_has_well_founded
noncomputable instance : linear_order (extended_index α) := linear_order_of_STO (<)

end extended_index

variables {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Λ}

lemma coe_ne' {γ : Iio α} {β : Iio α} : γ ≠ β → (γ : Λ) ≠ (β : Λ) :=
by contrapose!; simp only [subtype.coe_inj, imp_self]

lemma coe_lt {γ : Iio α} {β : Iic α} : (γ : Λ) < β → (γ : type_index) < (β : type_index) :=
begin
  intro h,
  cases β,
  cases γ,
  exact coe_lt_coe.mpr h,
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
TODO: Refactor `near_litter` to use `¬N.is_litter`.
-/
@[mk_iff] inductive constrains : support_condition β → support_condition β → Prop
| atom (a : atom) (A : extended_index β) :
    constrains ⟨inr a.1.to_near_litter, A⟩ ⟨inl a, A⟩
| near_litter (N : near_litter) (hN : litter_set N.fst ≠ N.snd) (A : extended_index β) :
    constrains ⟨inr N.fst.to_near_litter, A⟩ ⟨inr N, A⟩
| symm_diff (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd) (A : extended_index β) :
    constrains ⟨inl a, A⟩ ⟨inr N, A⟩
| f_map ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
    (A : path (β : type_index) γ) (t : tangle δ) (c ∈ (designated_support t).carrier) :
    constrains
      ⟨c.fst, (A.cons (coe_lt hδ)).comp c.snd⟩
      ⟨inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
        (A.cons (coe_lt hε)).cons (bot_lt_coe _)⟩
| f_map_bot ⦃γ : Iic α⦄ ⦃ε : Iio α⦄ (hε : (ε : Λ) < γ)
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
  obtain (⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩) := h;
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

variable {α}

@[simp] lemma constrains_atom {c : support_condition β} {a : atom} {A : extended_index β} :
  c ≺[α] ⟨inl a, A⟩ ↔ c = ⟨inr a.1.to_near_litter, A⟩ :=
begin
  split,
  { rintro ⟨⟩, refl, },
  { rintro rfl, exact constrains.atom a A, },
end

/-- The constrains relation is stable under composition of paths. -/
lemma constrains_comp {β γ : Λ} {c d : support_condition γ} (h : c ≺[α] d)
  (B : path (β : type_index) γ) : ⟨c.fst, B.comp c.snd⟩ ≺[α] ⟨d.fst, B.comp d.snd⟩ :=
begin
  obtain (⟨a, A⟩ | ⟨N, hN, A⟩ | ⟨N, a, ha, A⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩) := h,
  { exact constrains.atom _ _, },
  { exact constrains.near_litter _ hN _, },
  { exact constrains.symm_diff _ _ ha _, },
  { rw [path.comp_cons, ← path.comp_assoc, path.comp_cons],
    exact constrains.f_map hδ hε hδε (B.comp A) t c hc, },
  { rw path.comp_cons,
    exact constrains.f_map_bot hδ (B.comp A) a, },
end

notation c ` <[`:50 α `] ` d:50 := relation.trans_gen (constrains α _) c d
notation c ` ≤[`:50 α `] ` d:50 := relation.refl_trans_gen (constrains α _) c d

lemma refl_trans_gen_constrains_comp {β γ : Λ} {c d : support_condition γ}
  (h : c ≤[α] d) (B : path (β : type_index) γ) :
  ⟨c.fst, B.comp c.snd⟩ ≤[α] ⟨d.fst, B.comp d.snd⟩ :=
begin
  induction h with e f hce hef ih,
  exact relation.refl_trans_gen.refl,
  exact relation.refl_trans_gen.tail ih (constrains_comp hef B),
end

lemma trans_gen_constrains_comp {β γ : Λ} {c d : support_condition γ}
  (h : c <[α] d) (B : path (β : type_index) γ) :
  ⟨c.fst, B.comp c.snd⟩ <[α] ⟨d.fst, B.comp d.snd⟩ :=
begin
  induction h with e hce e f hce hef ih,
  exact relation.trans_gen.single (constrains_comp hce B),
  exact relation.trans_gen.tail ih (constrains_comp hef B),
end

lemma refl_trans_gen_near_litter {β : Λ} {N : near_litter} {B : extended_index β}
  {c : support_condition β} (h : (inr N, B) ≤[α] c) :
  (inr N.1.to_near_litter, B) ≤[α] c :=
begin
  by_cases h' : N.is_litter,
  { obtain ⟨L, rfl⟩ := h'.exists_litter_eq,
    exact h, },
  { exact relation.refl_trans_gen.head
      (constrains.near_litter N (near_litter.not_is_litter h') B) h, },
end

lemma trans_gen_near_litter {β : Λ} {N : near_litter} {B : extended_index β}
  {c : support_condition β}
  (h : c <[α] (inr N.1.to_near_litter, B)) :
  c <[α] (inr N, B) :=
begin
  by_cases h' : N.is_litter,
  { obtain ⟨L, rfl⟩ := h'.exists_litter_eq,
    exact h, },
  { exact relation.trans_gen.tail h
      (constrains.near_litter N (near_litter.not_is_litter h') B), },
end

lemma trans_gen_near_litter' {β : Λ} {N : near_litter} {B : extended_index β}
  {c : support_condition β}
  (h : (inr N, B) <[α] c) :
  (inr N.1.to_near_litter, B) <[α] c :=
begin
  by_cases h' : N.is_litter,
  { obtain ⟨L, rfl⟩ := h'.exists_litter_eq,
    exact h, },
  { exact relation.trans_gen.head
      (constrains.near_litter N (near_litter.not_is_litter h') B) h, },
end

lemma small_constrains {β : Λ} (c : support_condition β) : small {d | d ≺[α] c} :=
begin
  obtain ⟨a | N, A⟩ := c,
  { simp only [constrains_atom, set_of_eq_eq_singleton, small_singleton], },
  simp_rw constrains_iff,
  refine small.union _ (small.union _ (small.union _ (small.union _ _)));
    rw small_set_of,
  { simp only [prod.mk.inj_iff, false_and, and_false,
      exists_false, set_of_false, small_empty], },
  { simp only [ne.def, prod.mk.inj_iff, exists_eq_right_right'],
    by_cases litter_set N.fst = N.snd,
    simp only [h, eq_self_iff_true, not_true, false_and, set_of_false, small_empty],
    simp only [h, not_false_iff, true_and, set_of_eq_eq_singleton, small_singleton], },
  { simp only [prod.mk.inj_iff, exists_eq_right_right'],
    have : small {c : support_condition β | ∃ a, a ∈ litter_set N.fst ∆ N.snd ∧ c = (inl a, A)},
    { refine lt_of_le_of_lt _ N.2.prop,
      refine ⟨⟨λ c, ⟨_, c.2.some_spec.1⟩, _⟩⟩,
      rintros ⟨c, hc⟩ ⟨d, hd⟩,
      simp only [subtype.val_eq_coe, subtype.mk_eq_mk],
      intro h,
      rw [hc.some_spec.2, hd.some_spec.2, h], },
    convert this using 1,
    ext ⟨a | N, A⟩ : 1,
    { simp only [mem_set_of_eq, prod.mk.inj_iff],
      split,
      { rintro ⟨_, a', h₁, h₂, rfl⟩,
        exact ⟨a', h₁, h₂⟩, },
      { rintro ⟨a', h₁, h₂⟩,
        exact ⟨N, a', h₁, h₂, rfl⟩, } },
    { simp only [mem_set_of_eq, prod.mk.inj_iff, false_and, and_false, exists_false], }, },
  { by_cases ∃ ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ)
      (hδε : δ ≠ ε) (B : path (β : type_index) γ) (t : tangle δ),
      N = (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter ∧
      A = (B.cons (coe_lt hε)).cons (bot_lt_coe _),
    { obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h,
      refine lt_of_le_of_lt _ (designated_support t).small,
      suffices : #{a : support_condition β | ∃ c : designated_support t,
        a = ⟨c.val.fst, (B.cons (coe_lt hδ)).comp c.val.snd⟩} ≤ #(designated_support t),
      { refine le_trans (cardinal.mk_subtype_le_of_subset _) this,
        rintros x ⟨_, _, _, _, _, _, _, _, c, hc, rfl, h⟩,
        simp only [prod.mk.inj_iff, litter.to_near_litter_injective.eq_iff, f_map] at h,
        cases subtype.coe_inj.mp (coe_inj.mp h.1.2.1),
        cases subtype.coe_inj.mp h.1.2.2,
        cases choose_wf_injective h.1.1,
        cases subtype.coe_inj.mp (coe_inj.mp
          (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons h.2).eq)),
        cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons h.2).eq).eq,
        exact ⟨⟨c, hc⟩, rfl⟩, },
      refine ⟨⟨λ a, a.prop.some, _⟩⟩,
      intros a b h,
      refine subtype.coe_inj.mp _,
      simp only [subtype.val_eq_coe] at h,
      rw [a.prop.some_spec, b.prop.some_spec],
      simp only [h, subtype.val_eq_coe], },
    { refine small_of_forall_not_mem _,
      rintro x ⟨γ, δ, ε, hδ, hε, hδε, B, t, c, hN, rfl, hA⟩,
      simp only [prod.mk.inj_iff] at hA,
      refine h ⟨γ, δ, ε, hδ, hε, hδε, B, t, hA⟩, }, },
  { refine subsingleton.small _,
    rintros ⟨c, C⟩ ⟨γ, ε, hε, C', a, hc₁, hc₂⟩ ⟨d, D⟩ ⟨γ, ε, hε, D', b, hd₁, hd₂⟩,
    simp only [prod.mk.inj_iff] at hc₁ hc₂ hd₁ hd₂,
    rw [hc₁.1, hc₁.2, hd₁.1, hd₁.2],
    rw [hc₂.1, hc₂.2, litter.to_near_litter_injective.eq_iff] at hd₂,
    cases subtype.coe_inj.mp (coe_inj.mp (path.obj_eq_of_cons_eq_cons hd₂.2)),
    cases subtype.coe_inj.mp (coe_inj.mp (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hd₂.2).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hd₂.2).eq).eq,
    rw (f_map_injective bot_ne_coe).eq_iff at hd₂,
    cases hd₂.1,
    refl, },
end

end con_nf
