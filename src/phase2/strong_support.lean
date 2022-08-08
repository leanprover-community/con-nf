import phase2.freedom_of_action.constrains

noncomputable theory

open cardinal quiver relation
open_locale cardinal pointwise

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

/-- A small strong support is a strong support which supports some tangle `t`, and contains only
a small amount of support conditions. -/
structure small_strong_support {B : le_index α} (t : tangle_path B) extends strong_support B :=
(supports : supports (allowable_path B) carrier t)
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
begin
intros,
dsimp [(le_index.path)] at *,
exact S.strong (c.extend_path A) hc (d.extend_path A) (lower_constrains _ _ _ _ H),
end

/-- Since the lowering of any strong support is strong, we keep track of this fact here. -/
def strong_support.lower {β : type_index} (S : strong_support B) (A : path B.index β) :
  strong_support ⟨β, B.path.comp A⟩ :=
⟨S.to_word_support.lower B A, lower_strong B S A⟩

infix ` ≺≺ `:50 := (refl_trans_gen $ constrains _)

variable {B}

namespace potential_support

/-- The down-closure of a set of support conditions under the `constrains` relation.
Everything that (recursively) constrains a condition in `S` is included in its down-closure. -/
def closure (S : set (support_condition B)) : set (support_condition B) :=
⋃ c ∈ S, {d | d ≺≺ c}

lemma mem_closure_iff (S : set (support_condition B)) : ∀ c, c ∈ closure S ↔ ∃ d ∈ S, c ≺≺ d :=
begin
  intro c,
  split,
  { intro hc, obtain ⟨T, ⟨d, rfl⟩, hcT⟩ := hc,
    dsimp only at hcT, simp only [set.mem_Union, set.mem_set_of_eq, exists_prop] at hcT,
    exact ⟨d, hcT.1, hcT.2⟩, },
  { rintro ⟨d, hdS, hdc⟩,
    exact ⟨_, ⟨d, rfl⟩, ⟨_, ⟨hdS, rfl⟩, hdc⟩⟩, },
end

/-- The closure of a potential support is a superset of the original potential support. -/
lemma subset_closure (S : set (support_condition B)) : S ⊆ closure S :=
begin
  intros c hc,
  rw mem_closure_iff,
  exact ⟨c, hc, refl_trans_gen.refl⟩,
end

/-- The down-closure of a set that supports a tangle also supports that tangle. This is because
being a support is preserved under set union. -/
lemma closure_supports (t : tangle_path B) (S : support B (allowable_path B) t) :
  supports (allowable_path B) (closure S.carrier) t :=
supports.mono (subset_closure S) S.supports

end potential_support

/-- This really should be computable. However, Lean's computability checker is a bit broken. -/
noncomputable! def support.closure {t : tangle_path B} (S : support B (allowable_path B) t) :
  support B (allowable_path B) t :=
⟨potential_support.closure S, potential_support.closure_supports t S⟩

/-- Each condition has `<κ`-many immediate predecessors. -/
lemma mk_constrains (c : support_condition B) : small {d | d ≺ c} :=
begin
  have iff_imp_set_eq : ∀ (p q : support_condition B → Prop), (∀ d, p d ↔ q d) → {d | p d} = {d | q d} := λ p q h, set.ext (λ d, ⟨λ hd, (h d).1 hd, λ hd, (h d).2 hd⟩),
  have := λ d, constrains_iff B d c,
  specialize iff_imp_set_eq (λ d, d ≺ c) _ this,
  dsimp only at iff_imp_set_eq,
  rw iff_imp_set_eq,
  clear this iff_imp_set_eq,

  obtain ⟨c | c, C⟩ := c,
  { simp only [prod.mk.inj_iff, exists_eq_right_right', false_and, and_false, exists_false, or_false],
    convert lt_of_eq_of_lt (mk_singleton _) (lt_of_lt_of_le one_lt_aleph_0 κ_regular.aleph_0_le) using 1,
    swap, exact (sum.inr c.fst.to_near_litter, C),
    ext,
    refine ⟨_, λ hx, ⟨_, rfl, hx⟩⟩,
    rintro ⟨_, h1, h⟩,
    cases h1,
    exact set.mem_singleton_iff.2 h },
  { have eq_union : ∀ (p q : support_condition B → Prop), {d | p d ∨ q d} = {d | p d} ∪ {d | q d},
    { refine λ p q, set.ext (λ d, _),
      dsimp only,
      refl, },
    rw [eq_union, eq_union, eq_union],
    clear eq_union,

    unfold small,
    refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le _ _),
    { simp only [prod.mk.inj_iff, false_and, and_false, exists_false, set.set_of_false, mk_emptyc],
      exact lt_of_lt_of_le cardinal.aleph_0_pos κ_regular.aleph_0_le },
    refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le _ _),
    { by_cases litter_set c.fst = c.snd,
      { simp only [ne.def, prod.mk.inj_iff, exists_eq_right_right', set.coe_set_of],
        refine lt_of_eq_of_lt (cardinal.mk_emptyc_iff.2 _) (lt_of_lt_of_le aleph_0_pos κ_regular.aleph_0_le),
        refine set.ext (λ x, ⟨_, λ h, h.rec _⟩),
        rintro ⟨hnot, -⟩,
        exact hnot h },
      { convert lt_of_eq_of_lt (mk_singleton _) (lt_of_lt_of_le one_lt_aleph_0 κ_regular.aleph_0_le) using 3,
        swap, exact (sum.inr c.fst.to_near_litter, C),
        refine set.ext (λ x, ⟨_, λ hx, ⟨c, h, C, hx, rfl⟩⟩),
        rintro ⟨_, _, _, ⟨⟩, ⟨⟩⟩,
        exact rfl } },
    refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le _ _),
    { convert lt_of_le_of_lt (@cardinal.mk_image_le _ _ _ _) c.snd.prop using 4,
      swap, exact λ a, (sum.inl a, C),
      refine funext (λ x, eq_iff_iff.2 _),
      cases x with x A,
      split,
      { rintro ⟨_, a, ha, _, ⟨⟩, ⟨⟩⟩,
        exact ⟨a, ha, rfl⟩ },
      { rintro ⟨a, ha, ⟨⟩⟩,
        exact ⟨c, a, ha, C, rfl, rfl⟩ } },
    sorry }
end

/-- There are only `<κ`-many things that recursively constrain any given support condition.
This is because `constrains` is well-founded and each condition has `<κ` immediate predecessors. -/
lemma constrains_small : ∀ (c : support_condition B), small {d | d ≺≺ c}
| c := begin
  -- lemmas that probably exist but i don't know the names of
  have cases_tail_iff : ∀ x, {d : support_condition B | d ≺≺ x} = {d | d = x ∨ (∃ e, d ≺≺ e ∧ e ≺ x)},
  { refine λ x, set.ext (λ d, _),
    dsimp,
    rw refl_trans_gen.cases_tail_iff (constrains B),
    split; exact λ hx, or.rec (λ h, or.inl h.symm) (λ h, or.inr h) hx },
  have eq_union : ∀ (p q : support_condition B → Prop), {d | p d ∨ q d} = {d | p d} ∪ {d | q d},
  { refine λ p q, set.ext (λ d, _),
    dsimp only,
    refl, },
  have eq_Union : {d : support_condition B | ∃ (e : support_condition B), d ≺≺ e ∧ e ≺ c} =
      ⋃ (e : {e : support_condition B // e ≺ c}), {d : support_condition B | d ≺≺ e.val},
  { ext,
    simp only [set.mem_set_of_eq, set.mem_Union, exists_prop],
    split; rintro ⟨e, he⟩,
    { exact ⟨⟨e, he.2⟩, he.1⟩ },
    { exact ⟨e.val, he, e.prop⟩ } },

  unfold small at ⊢,
  rw [cases_tail_iff, eq_union, eq_Union],
  refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le
      (lt_of_eq_of_lt (by rw [set.set_of_eq_eq_singleton, mk_singleton]) $ lt_of_lt_of_le
        one_lt_aleph_0 κ_regular.aleph_0_le) $ lt_of_le_of_lt cardinal.mk_Union_le_sum_mk _),
  refine cardinal.sum_lt_of_is_regular κ_regular (mk_constrains c) _,
  rintro ⟨e, he⟩,
  exact constrains_small e,
end
using_well_founded { dec_tac := `[assumption] }

/-- An application of the above lemma, since there are only `<κ`-many support conditions in `S`. -/
lemma small_support.closure_small {t : tangle_path B} (S : small_support B (allowable_path B) t) :
  small S.to_support.closure.carrier :=
sorry

/-- Any well-founded relation can be extended to a well-ordering on that type. Hopefully this is
already in mathlib, but I couldn't find it.
Check the blueprint for more information (Lemma 3.26). -/
lemma well_order_of_well_founded {α : Type*} {r : α → α → Prop} (wf : well_founded r) :
  ∃ s ≥ r, is_well_order α s :=
sorry

/-- Any small support can be 'strengthened' into a strong support that is also small.
Check the blueprint for more information. -/
lemma strengthen_small_support (t : tangle_path B) (S : small_support B (allowable_path B) t) :
  ∃ T : small_strong_support t, S.carrier ⊆ T.carrier :=
begin
  refine ⟨_, _⟩,
  refine_struct {
    carrier := S.to_support.closure.carrier,
    r := (well_order_of_well_founded (inv_image.wf _ (constrains_wf B))).some,
    wo := (well_order_of_well_founded (inv_image.wf _ (constrains_wf B))).some_spec.some_spec,
    supports := S.to_support.closure.supports,
    small := small_support.closure_small S,
  },
  { -- The `strong` condition remains to be shown.
    intros c hc d hd,
    split,
    refine (well_order_of_well_founded
        (inv_image.wf subtype.val (constrains_wf B))).some_spec.some ⟨d, _⟩ ⟨c, hc⟩ hd,
    unfold support.closure at hc ⊢,
    rw potential_support.mem_closure_iff at hc ⊢,
    obtain ⟨e, he₁, he₂⟩ := hc,
    exact ⟨e, he₁, refl_trans_gen.head hd he₂⟩, },
  { exact potential_support.subset_closure _, },
end

/-- There exists a small strong support for any tangle, along any path. -/
lemma exists_strong_support (t : tangle_path B) : nonempty (small_strong_support t) :=
⟨(strengthen_small_support t (designated_support_path t)).some⟩

end con_nf
