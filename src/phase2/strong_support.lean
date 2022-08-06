import phase2.freedom_of_action

noncomputable theory

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

noncomputable! def proto_smul : allowable_path B → word_support B → word_support B :=
λ π S,
{ carrier := (π.to_struct_perm) • S.carrier,
    r := λ c₁ c₂, begin
      refine S.r ⟨(π.to_struct_perm)⁻¹ • c₁, _⟩
        ⟨(π.to_struct_perm)⁻¹ • c₂, _⟩;
      rw [← set.mem_inv_smul_set_iff, inv_inv],
      exact c₁.property, exact c₂.property,
    end,
  wo := { trichotomous := begin intros,
    have : ∀ c₁ : ↥(allowable_path.to_struct_perm π • S.carrier), (allowable_path.to_struct_perm π)⁻¹ • ↑c₁ ∈ S.carrier,
    intro c₁, rw [← set.mem_inv_smul_set_iff, inv_inv], exact c₁.property,
    have : a = b ↔ (⟨(allowable_path.to_struct_perm π)⁻¹ • ↑a, this a⟩ : {x // x ∈ S.carrier})
                   = (⟨(allowable_path.to_struct_perm π)⁻¹ • ↑b, this b⟩ : {x // x ∈ S.carrier}),
    { simp [subtype.coe_inj] },
    rw this, apply S.wo.trichotomous, end,
  irrefl := begin intros, apply S.wo.irrefl, end,
  trans := begin intros,apply S.wo.trans, apply ᾰ, apply ᾰ_1 end,
  wf := begin have := @inv_image.is_well_founded _ _ S.r ⟨S.wo.wf⟩, convert (this _).wf, end } }

noncomputable! instance : mul_action (allowable_path B) (word_support B) :=
{ smul := proto_smul B,
  one_smul := begin intros, cases b, dsimp [proto_smul], simp only [struct_perm.coe_to_near_litter_perm, map_one, inv_one, one_smul, eq_self_iff_true, true_and],
  dsimp [(sum.map)], have backup: (↥((1 : allowable_path B) • b_carrier) : Type u) = (↥b_carrier : Type u), rw mul_action.one_smul,have : (↥((1 : allowable_path B) • b_carrier) : Type u) = (↥b_carrier : Type u), rw mul_action.one_smul,
  convert heq_of_eq _, rw mul_action.one_smul, clear b_wo,
  suffices : b_r == λ o1 o2, b_r (cast this o1) (cast this o2), exact this,
  revert b_r this, rw backup,
  intros, apply heq_of_eq, funext, refl, funext,
  cases c₁, cases c₂, cases c₁_val, cases c₂_val,
  simp only [subtype.coe_mk, one_smul, eq_self_iff_true, set_coe_cast],
  end,
  mul_smul := begin intros, cases b, dsimp[proto_smul], simp only [prod.mk.inj_iff], split, apply mul_action.mul_smul,
  simp only [map_mul, mul_inv_rev],
  have h: ↥((x * y) • b_carrier) = ↥(x • y • b_carrier), rw mul_action.mul_smul,
  have h2: ↥((x * y) • b_carrier) = ↥(x • y • b_carrier) , rw mul_action.mul_smul,
  let f : ↥((x * y) • b_carrier) → ↥((x * y) • b_carrier) → Prop := (λ c₁ c₂ : ↥((x * y) • b_carrier), _),
  let g : ↥(x • y • b_carrier) → ↥(x • y • b_carrier) → Prop := λ d₁ d₂ : ↥(x • y • b_carrier), f (cast (eq.symm h) d₁) (cast (eq.symm h) d₂),
  suffices : (λ (c₁ c₂ : ↥((x * y) • b_carrier)), g (cast (h2) c₁) (cast (h2) c₂))== _,
  dsimp [(g)] at this,
  simp only [eq_self_iff_true, subtype.val_eq_coe, cast_cast, set_coe_cast, subtype.coe_eta] at this,
  exact this, revert h2, rw h, intro h2, apply heq_of_eq, funext,  dsimp [(g), (f)],
  have : ∀ c : ↥(x • y • b_carrier), (↑(cast (eq.symm h) c) : support_condition ↑B)= ↑c, intros,
  have h2 :((x * y) • b_carrier) = (x • y • b_carrier), rw mul_action.mul_smul,
  clear g,
  cases c,
  simp only [subtype.coe_mk],
  revert c_property h,
  rw ← h2,
  intros,
  simp only [set_coe_cast, subtype.coe_mk],
  apply congr, apply congr,
  refl,
  simp only, rw mul_action.mul_smul, apply congr, refl, apply congr, refl, exact this c₁,
  simp only, rw mul_action.mul_smul, apply congr, refl, apply congr, refl, exact this c₂,
end,
}

/-- We can lower a support to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping support conditions whose paths begin with `A`. -/
def word_support.lower {β : type_index} (S : word_support B) (A : path B.index β) :
  word_support ⟨β, B.path.comp A⟩ := {
  carrier := {c | c.extend_path A ∈ S.carrier},
  r := λ c₁ c₂, S.r ⟨c₁.val.extend_path A, c₁.property⟩ ⟨c₂.val.extend_path A, c₂.property⟩,
  wo := { trichotomous := begin intros,
  have : a=b ↔ (⟨a.val.extend_path A, _⟩ : {x // x ∈ S.carrier}) = ⟨b.val.extend_path A, _⟩,
  {split, intro h, simp only [subtype.val_eq_coe], rw h, intro h, simp only [subtype.val_eq_coe] at h,
  dsimp [(support_condition.extend_path)] at h, simp only [prod.mk.inj_iff] at h,
  cases a, cases b, cases a_val, cases b_val, simp only [subtype.coe_mk] at h,
  have h_len: (a_val_snd).length = (b_val_snd).length,
  rw [← add_right_inj, ← path.length_distrib, ← path.length_distrib, h.right],
  have := h.left, subst this, have := (quiver.path.comp_inj A A a_val_snd b_val_snd h_len h.right).right, subst this},
  rw this, apply S.wo.trichotomous, end,
  irrefl := begin intros, apply S.wo.irrefl, end,
  trans := begin intros,apply S.wo.trans, apply ᾰ, apply ᾰ_1 end,
  wf := begin have := @inv_image.is_well_founded _ _ S.r ⟨S.wo.wf⟩, convert (this _).wf, end },
}

/-- The lowering operation reflects the constrains `≺` relation. -/
lemma lower_constrains {β : type_index} (A : path B.index β)
  (c d : support_condition (⟨β, B.path.comp A⟩ : le_index α)) :
  c ≺ d → c.extend_path A ≺ d.extend_path A :=
begin
intro h, dsimp [(support_condition.extend_path)], cases h,
simp only, apply con_nf.constrains.mem_litter, exact h_H,
simp only, apply con_nf.constrains.near_litter, exact h_hN,
simp only, apply con_nf.constrains.symm_diff, exact h_H,
dsimp [(le_index.path)] at *, revert h_t h_c, rw path.comp_assoc, intros,
have := con_nf.constrains.f_map h_hγ h_hδ h_hγδ (A.comp h_A) h_t h_c _,
have h2 : ((A.comp h_A).cons h_hγ).comp h_c.snd = A.comp ((h_A.cons h_hγ).comp h_c.snd),
{rw ← path.comp_cons, rw path.comp_assoc},
rw h2 at this,
exact this,
exact h_H,
end

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
lemma strengthen_small_support (t : tangle_path B) (S : small_support B (allowable_path B) t) :
  ∃ T : small_strong_support B, S.carrier ⊆ T.carrier :=
sorry

/-- There exists a small strong support for any tangle, along any path. -/
lemma exists_strong_support (t : tangle_path B) :
  ∃ (T : small_strong_support B), supports (allowable_path B) T.carrier t :=
let ⟨T, hT⟩ := strengthen_small_support B t (designated_support_path t) in
⟨T, (designated_support_path t).supports.mono hT⟩

end con_nf
