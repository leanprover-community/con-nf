import phase2.freedom_of_action

open quiver
open_locale pointwise

universe u

namespace con_nf
variables [params.{u}] {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [phase_2_assumptions α] (B : le_index α)

/-- A support `carrier` with a well-order `r` is called a *well-ordered support*. -/
structure word_support :=
(carrier : set (support_condition B))
(r : carrier → carrier → Prop)
(wo : is_well_order carrier r)

/-- A well-ordered support is *strong* if whenever `c ∈ S` and `d` constrains `c`, then `d ∈ S` and
`d < c` in the well-order associated with the support. -/
structure strong_support extends word_support B :=
(strong : ∀ c (hc : c ∈ carrier), ∀ d ≺ c, ∃ (hd : d ∈ carrier), r ⟨d, hd⟩ ⟨c, hc⟩)

structure small_strong_support extends strong_support B :=
(small : small carrier)

instance : mul_action (allowable_path B) (word_support B) := {
  smul := λ π S, {
    carrier := (π.to_struct_perm) • S.carrier,
    r := λ c₁ c₂, begin
      refine S.r ⟨(π.to_struct_perm)⁻¹ • c₁, _⟩
        ⟨(π.to_struct_perm)⁻¹ • c₂, _⟩;
      rw [← set.mem_inv_smul_set_iff, inv_inv],
      exact c₁.property, exact c₂.property,
    end,
  wo := { trichotomous := begin intros,
    have : ∀ c₁ : ↥(allowable_path.to_struct_perm π • S.carrier), (allowable_path.to_struct_perm π)⁻¹ • ↑c₁ ∈ S.carrier,
    intro c₁, rw [← set.mem_inv_smul_set_iff, inv_inv], exact c₁.property,
    have : a = b ↔ (⟨(allowable_path.to_struct_perm π)⁻¹ • ↑a, this a⟩ :  {x // x ∈ S.carrier})
                   =(⟨(allowable_path.to_struct_perm π)⁻¹ • ↑b, this b⟩  :  {x // x ∈ S.carrier}),
    {split, intro h, subst h, intro h, cases a, cases b,
    simp only [smul_left_cancel_iff, subtype.coe_mk] at h, subst h},
    rw this, apply S.wo.trichotomous, end,
  irrefl := begin intros, apply S.wo.irrefl, end,
  trans := begin intros,apply S.wo.trans, apply ᾰ, apply ᾰ_1 end,
  wf := begin have := @inv_image.is_well_founded _ _ S.r ⟨S.wo.wf⟩, convert (this _).wf, end },
  },
  one_smul := begin intros, cases b, unfold has_smul.smul, simp only [struct_perm.coe_to_near_litter_perm, map_one, inv_one, one_smul, eq_self_iff_true, true_and],
  dsimp [(sum.map)], have backup: (↥((1 : allowable_path B) • b_carrier) : Type u) = (↥b_carrier : Type u), rw mul_action.one_smul,have : (↥((1 : allowable_path B) • b_carrier) : Type u) = (↥b_carrier : Type u), rw mul_action.one_smul,convert heq_of_eq _, rw mul_action.one_smul, clear b_wo,
  suffices : b_r == λ o1 o2, b_r (cast this o1) (cast this o2), exact this,
  revert b_r this, rw backup,
  intros, apply heq_of_eq, funext, refl, funext,
  cases c₁, cases c₂, cases c₁_val, cases c₂_val,
  simp only [subtype.coe_mk, one_smul, eq_self_iff_true, set_coe_cast], congr,
  cases c₁_val_fst,
  simp only [has_smul.comp.smul, sum.elim_inl, function.comp_app, struct_perm.of_bot_one, one_smul],
  simp only [has_smul.comp.smul, sum.elim_inr, function.comp_app, struct_perm.of_bot_one, one_smul],
  cases c₂_val_fst,
  simp only [has_smul.comp.smul, sum.elim_inl, function.comp_app, struct_perm.of_bot_one, one_smul],
  simp only [has_smul.comp.smul, sum.elim_inr, function.comp_app, struct_perm.of_bot_one, one_smul],
  end,
  mul_smul := begin intros, cases b, unfold has_smul.smul, sorry end,
}

/-- We can lower a support to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping support conditions whose paths begin with `A`. -/
def word_support.lower {β : type_index} (S : word_support B) (A : path B.index β) :
  word_support ⟨β, B.path.comp A⟩ := {
  carrier := {c | c.extend_path A ∈ S.carrier},
  r := λ c₁ c₂, S.r ⟨c₁.val.extend_path A, c₁.property⟩ ⟨c₂.val.extend_path A, c₂.property⟩,
  wo := sorry,
}

/-- The lowering operation reflects the constrains `≺` relation. -/
lemma lower_constrains {β : type_index} (A : path B.index β)
  (c d : support_condition (⟨β, B.path.comp A⟩ : le_index α)) :
  c ≺ d → d.extend_path A ≺ c.extend_path A :=
sorry

/-- The lowering of a strong support is strong. This is proven with the above lemma. -/
lemma lower_strong {β : type_index} (S : strong_support B) (A : path B.index β) :
  ∀ c (hc : c ∈ (S.to_word_support.lower B A).carrier), ∀ d ≺ c,
  ∃ (hd : d ∈ (S.to_word_support.lower B A).carrier),
    (S.to_word_support.lower B A).r ⟨d, hd⟩ ⟨c, hc⟩ :=
sorry

/-- Since the lowering of any strong support is strong, we keep track of this fact here. -/
def strong_support.lower {β : type_index} (S : strong_support B) (A : path B.index β) :
  strong_support ⟨β, B.path.comp A⟩ :=
⟨S.to_word_support.lower B A, lower_strong B S A⟩

/-- Any small support can be 'strengthened' into a strong support that is also small.
Check the blueprint for more information. -/
lemma strengthen_small_support (t : tangle_path B)
  (S : small_support (allowable_path_to_struct_perm B) t) :
  ∃ (T : small_strong_support B), S.carrier ⊆ T.carrier :=
sorry

/-- There exists a small strong support for any tangle, along any path. -/
lemma exists_strong_support (t : tangle_path B) :
  ∃ (T : small_strong_support B), supports (allowable_path_to_struct_perm B) T.carrier t :=
let ⟨T, hT⟩ := strengthen_small_support B t (designated_support_path t) in
⟨T, supports_mono hT (designated_support_path t).supports⟩

end con_nf
