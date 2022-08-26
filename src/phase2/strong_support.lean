import phase2.freedom_of_action.constrains

noncomputable theory

open cardinal quiver relation
open_locale cardinal pointwise

universe u

namespace con_nf
variables [params.{u}] {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] (B : le_index α)

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

private lemma mk_path_n_lt_kappa : ∀ (A B : type_index) (n : ℕ), #{p : path A B // p.length = n} < #κ
| A B 0 := begin
  by_cases A = B,
  { subst h,
    convert lt_of_eq_of_lt (mk_singleton $ @path.nil _ _ A) (lt_of_lt_of_le one_lt_aleph_0 κ_regular.aleph_0_le) using 3,
    ext,
    split,
    { intro hx,
      cases x,
      { exact set.mem_singleton _, },
      { rw path.length_cons at hx,
        cases hx } },
    { rintro ⟨⟩,
      exact path.length_nil, } },
  { convert lt_of_eq_of_lt (mk_emptyc $ @path _ _ A B) (lt_of_lt_of_le aleph_0_pos κ_regular.aleph_0_le) using 3,
    ext,
    split,
    { intro hx,
      cases x,
      { exact h rfl, },
      { rw path.length_cons at hx,
        cases hx } },
    { rintro ⟨⟩, } }
end
| A B (nat.succ N) := begin
  have : {p : path A B // p.length = N.succ} ≃ Σ (C : type_index), {q : path A C // q.length = N ∧ hom C B},
  { refine ⟨_, _, _, _⟩,
    { rintro ⟨⟨⟩ | ⟨C, _, q, hhom⟩, hp⟩,
      { cases hp },
      { simp only [path.length_cons, nat.add_one] at hp,
        refine ⟨C, q, hp, hhom⟩, } },
    { rintro ⟨C, q, hp, hhom⟩,
      refine ⟨q.cons hhom, _⟩,
      rw [← nat.add_one, ← hp, path.length_cons], },
  { rintro ⟨p, hp⟩,
    cases p,
    { cases hp },
    simp only [eq_self_iff_true, heq_iff_eq, and_self] },
  { rintro ⟨C, q, hq, hhom⟩,
    simp only [eq_self_iff_true, heq_iff_eq, and_self] }, },
  rw [mk_congr this, mk_sigma _],refine sum_lt_of_is_regular κ_regular (lt_of_eq_of_lt mk_type_index Λ_lt_κ) _,
  intro C,
  refine lt_of_le_of_lt (mk_subtype_mono $ λ x, and.left) (mk_path_n_lt_kappa A C N),
end

private lemma mk_path_lt_kappa {B β : type_index} : cardinal.mk (@path type_index _ B β) < #κ :=
begin
  have : (Σ (n : ℕ), {p : path B β // p.length = n}) ≃ path B β,
  { refine ⟨λ p, p.snd.val, λ p, ⟨p.length, p, rfl⟩, _, λ p, rfl⟩,
    rintro ⟨n, p, rfl⟩, refl },
  rw [← mk_congr this, mk_sigma _],
  refine sum_lt_lift_of_is_regular κ_regular _ (mk_path_n_lt_kappa _ _),
  rw [mk_denumerable, lift_aleph_0],
  exact lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ
end

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

    -- litter and its atoms
    unfold small,
    refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le _ _),
    { simp only [prod.mk.inj_iff, false_and, and_false, exists_false, set.set_of_false, mk_emptyc],
      exact lt_of_lt_of_le cardinal.aleph_0_pos κ_regular.aleph_0_le },

    -- near-litter and its litter
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

    -- atom and its near-litters
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

    -- litter and its f-map
    have tangle_path_unique : ∀ (β : Λ) (γ : type_index) (δ : Λ) (hγ : γ < β) (hδ : δ < β) (A : path (B : type_index) β), {t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α) | ((sum.inr c : atom ⊕ near_litter), C) = (sum.inr (f_map_path hγ hδ t).to_near_litter, (A.cons (with_bot.coe_lt_coe.2 hδ)).cons (with_bot.bot_lt_coe δ))}.subsingleton,
    { rintros β γ δ hγ hδ A t ht t' ht',
      obtain ⟨-, hheq⟩ := f_map_path_injective (litter.to_near_litter_injective
        (sum.inr.inj (prod.eq_iff_fst_eq_snd_eq.1 $ ht.symm.trans ht').1)),
      exact eq_of_heq hheq },
    have small_carrier : ∀ (β : Λ) (γ : type_index) (δ : Λ) (hγ : γ < β) (hδ : δ < β) (A : path (B : type_index) β) (t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α)), small ((designated_support_path t).to_support.carrier) := λ _ _ _ _ _ _ t, (designated_support_path t).small,
    have image_of : ∀ (β : Λ) (γ : type_index) (δ : Λ) (hγ : γ < β) (hδ : δ < β) (A : path (B : type_index) β), {d :
   support_condition ↑B | ∃ (t : tangle_path ↑(lt_index.mk' hγ (B.path.comp A)))
   (c_1 : support_condition (lt_index.mk' hγ (B.path.comp A) : le_index α).index),
   c_1 ∈ (designated_support_path t).to_support.carrier ∧
     d = (prod.fst c_1, (A.cons hγ).comp c_1.snd) ∧
       ((sum.inr c : atom ⊕ near_litter), C) = (sum.inr (f_map_path hγ hδ t).to_near_litter, (A.cons (with_bot.coe_lt_coe.2 hδ)).cons (with_bot.bot_lt_coe δ))} = (λ d, (prod.fst d, (A.cons hγ).comp d.snd)) '' ⋃₀ ((λ x : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α), (designated_support_path x).to_support.carrier) '' {t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α) | ((sum.inr c : atom ⊕ near_litter), C) = (sum.inr (f_map_path hγ hδ t).to_near_litter, (A.cons (with_bot.coe_lt_coe.2 hδ)).cons (with_bot.bot_lt_coe δ))}),
    { intros _ _ _ _ _ _,
      ext ⟨x, y⟩,
      split,
      { rintro ⟨t, e, he, ⟨⟩, hc⟩,
        exact ⟨_, ⟨_, ⟨_, hc, rfl⟩, he⟩, rfl⟩, },
      { rintro ⟨_, ⟨_, ⟨_, hc, ⟨⟩⟩, he⟩, ⟨⟩⟩,
        exact ⟨_, _, he, rfl, hc⟩, }, },
    have type_index_lt_κ := lt_of_eq_of_lt mk_type_index Λ_lt_κ,

    have exists_Union : ∀ T (p : support_condition B → T → Prop), {d | ∃ a, p d a} = ⋃ a, {d | p d a},
    { refine λ _ p, set.ext (λ x, ⟨_, _⟩),
      { rintro ⟨a, hx⟩,
        exact ⟨_, ⟨a, rfl⟩, hx⟩, },
      { rintro ⟨_, ⟨a, rfl⟩, hx⟩,
        exact ⟨a, hx⟩, } },
    have exists_Prop : ∀ ⦃T : Prop⦄ ⦃p : support_condition B → T → Prop⦄, (∀ a, #{d | p d a} < #κ) → #{d | ∃ a, p d a} < #κ,
    { intros _ p h,
      by_cases a : T,
      { refine lt_of_eq_of_lt _ (h a),
        convert rfl using 4,
        ext,
        refine ⟨λ hx, ⟨a, hx⟩, _⟩,
        rintro ⟨a', hx⟩,
        obtain rfl : a = a' := rfl,
        exact hx },
      { convert (cardinal.mk_emptyc _).trans_lt κ_regular.pos using 3,
        ext,
        exact ⟨λ hx, a hx.some, λ f, f.rec _⟩, } },
    have eq_inter : ∀ (p q : support_condition B → Prop), {d | p d ∧ q d} = {d | p d} ∩ {d | q d},
    { refine λ p q, set.ext (λ d, _),
      dsimp only,
      refl, },

    rw exists_Union,
    refine lt_of_le_of_lt cardinal.mk_Union_le_sum_mk (cardinal.sum_lt_of_is_regular κ_regular Λ_lt_κ $ λ β, _),
    rw exists_Union,
    refine lt_of_le_of_lt cardinal.mk_Union_le_sum_mk (cardinal.sum_lt_of_is_regular κ_regular type_index_lt_κ $ λ γ, _),
    rw exists_Union,
    refine lt_of_le_of_lt cardinal.mk_Union_le_sum_mk (cardinal.sum_lt_of_is_regular κ_regular Λ_lt_κ $ λ δ, _),
    refine exists_Prop (λ hγ, _),
    refine exists_Prop (λ hδ, _),
    rw eq_inter,
    refine lt_of_le_of_lt (cardinal.mk_le_mk_of_subset $ set.inter_subset_right _ _) _,
    rw exists_Union,
    refine lt_of_le_of_lt cardinal.mk_Union_le_sum_mk (cardinal.sum_lt_of_is_regular κ_regular mk_path_lt_kappa $ λ A, _),
    rw image_of,
    refine lt_of_le_of_lt mk_image_le (lt_of_le_of_lt (mk_sUnion_le _) $ mul_lt_of_lt κ_regular.aleph_0_le _ _),
    { refine lt_of_le_of_lt mk_image_le _,
      exact lt_of_le_of_lt (le_one_iff_subsingleton.2 $ (set.subsingleton_coe _).2 $
          tangle_path_unique β γ δ hγ hδ A) (lt_of_lt_of_le one_lt_aleph_0 κ_regular.aleph_0_le), },
    refine supr_lt_of_is_regular κ_regular _ _,
    { refine lt_of_le_of_lt mk_image_le _,
      exact lt_of_le_of_lt (le_one_iff_subsingleton.2 $ (set.subsingleton_coe _).2 $
          tangle_path_unique β γ δ hγ hδ A) (lt_of_lt_of_le one_lt_aleph_0 κ_regular.aleph_0_le), },
    rintro ⟨s, ⟨t, ht, rfl⟩⟩,
    exact small_carrier β γ δ hγ hδ A t, }
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
lt_of_le_of_lt (cardinal.mk_bUnion_le _ _) (cardinal.mul_lt_of_lt κ_regular.aleph_0_le S.2 $
  cardinal.supr_lt_of_is_regular κ_regular S.2 $ λ x, constrains_small x)

/-- Any well-founded relation can be extended to a well-ordering on that type. Hopefully this is
already in mathlib, but I couldn't find it.
Check the blueprint for more information (Lemma 3.26). -/
lemma well_order_of_well_founded {α : Type*} {r : α → α → Prop} (wf : well_founded r) :
  ∃ s ≥ r, is_well_order α s :=
begin
  have wo_po: partial_order {x : set α × (α → α → Prop) // is_well_order x.1 (λ a1 a2, x.2 a1 a2) ∧ x.2 ≥ r ∧ ∀ y1 y2, (y1 ∉ x.1 ∨ y2 ∉ x.1) → (x.2 y1 y2) = true} := {
    le := (λ x1 x2, x1.1.1 ⊆ x2.1.1 ∧ (∀ y1 y2 ∈ x1.1.1, x2.1.2 y1 y2 = x1.1.2 y1 y2) ∧ (∀ y1 ∈ x1.1.1, ∀ y2 ∈ x2.1.1 \ x1.1.1, x2.1.2 y1 y2) ),
    lt := (λ x1 x2, x1.1.1 ≠ x2.1.1 ∧ x1.1.1 ⊆ x2.1.1 ∧ (∀ y1 y2 ∈ x1.1.1, x2.1.2 y1 y2 = x1.1.2 y1 y2) ∧ ∀ y1 ∈ x1.1.1, ∀ y2 ∈ x2.1.1 \ x1.1.1, x2.1.2 y1 y2 ),
    le_refl := begin intros, unfold has_le.le, simp only [eq_iff_iff, iff_self, set.diff_self, set.mem_empty_eq, is_empty.forall_iff, implies_true_iff, and_true], end,
    le_trans := begin unfold has_le.le, intros a b c h1 h2, split,
    exact set.subset.trans h1.1 h2.1, split, intros, apply eq.trans,
    apply h2.2.1 y1 (set.mem_of_subset_of_mem h1.1 H) y2 (set.mem_of_subset_of_mem h1.1 H_1),
    apply h1.2.1 y1 H y2 H_1,
    intros,
    by_cases h3 : y2 ∈ b.val.fst,
    rw h2.2.1 y1 (set.mem_of_subset_of_mem h1.1 H) y2 h3,
    apply h1.2.2 y1 H y2 (set.mem_diff_of_mem h3 (set.not_mem_of_mem_diff H_1)),
    apply h2.2.2 y1 (set.mem_of_subset_of_mem h1.1 H) y2 (set.mem_diff_of_mem (set.mem_of_mem_diff H_1) h3),
    end,
    lt_iff_le_not_le := begin intros, unfold has_lt.lt, split, intro h, split, exact h.right,
    unfold has_le.le, by_contra h2, apply h.left, apply set.subset.antisymm h.2.1 h2.1,
    intro h, split, by_contra h2,
    cases a, cases b, cases a_val, cases b_val, simp only at h2, subst h2, apply h.right, unfold has_le.le at h ⊢,
    simp only at h ⊢, split, apply set.subset.refl, split, intros, apply eq.symm, apply h.1.2.1 y1 H y2 H_1,
    simp only [set.diff_self, set.mem_empty_eq, is_empty.forall_iff, implies_true_iff], exact h.1,
    end,
    le_antisymm := begin intros a b h1 h2, cases a, cases b, cases a_val, cases b_val, simp only [prod.mk.inj_iff],
     have : a_val_fst = b_val_fst, apply (set.subset.antisymm h1.1 h2.1), subst this, split, refl,
    ext, by_cases (x ∉ a_val_fst ∨ x_1 ∉ a_val_fst), simp only at a_property b_property, rw [(a_property.2.2 x x_1 h), (b_property.2.2 x x_1 h)],
    push_neg at h, dsimp only [(has_le.le)] at h1 h2, rw h1.2.1 x h.left x_1 h.right,  end
  },
  have :=  @zorn_nonempty_partial_order₀ _ wo_po set.univ
  begin

  intros c hc hc2 y hy,
  {
    --use ⟨ set.Union (λ p, p.1.1.1: c → set α), (λ a a', ∃ x : c, a ∈ x.1.1.1 ∧ a' ∈ x.1.1.1 ∧ x.1.1.2 a a' ∨ (∀ x : c, ¬ (a ∈ x.1.1.1 ∧ a' ∈ x.1.1.1)))⟩,
    sorry,
  }
  end
  begin
  have :  is_well_order ↥(((∅ : set α), (λ a b, true : α → α → Prop)).fst) (λ (a1 a2 : ↥(((∅ : set α),
  (λ a b, true : α → α → Prop)).fst)), ((∅ : set α), (λ a b, true : α → α → Prop)).snd ↑a1 ↑a2) ∧
    (((∅ : set α)), (λ a b, true : α → α → Prop)).snd ≥ r ∧ ∀ (y1 y2 : α), y1 ∉ ((∅ : set α),
    (λ a b, true : α → α → Prop)).fst ∨ y2 ∉ ((∅ : set α), (λ a b, true : α → α → Prop)).fst → ((∅ : set α), (λ a b, true : α → α → Prop)).snd y1 y2 = true,
  { split,
    apply @is_empty.is_well_order _ _,
    simp only, rw @set.is_empty_coe_sort α ∅, simp only, split, dsimp [(≥)], intros i i2, rw le_Prop_eq, simp only, simp only [implies_true_iff],
    intros, refl, },
  exact ⟨({}, (λ a b, true : α → α → Prop)), this ⟩,
  end
  (by simp only [set.mem_univ]),
  obtain ⟨s, hs₁, rs, hs₂⟩ := this,
  cases s, cases s_val,
  use s_val_snd,
  split,
  exact s_property.right.left,
  simp only at s_property,
  have all_type : ∀ a : α, ∃ b : ↥(s_val_fst), a = b, {by_contra, push_neg at h, obtain ⟨ha, hb ⟩ := h,
  have : ha ∉ s_val_fst, by_contra h2, specialize hb ⟨ha, h2⟩, apply hb, refl,
  sorry, -- Maximal subset contains all elements
  },
  have coe_inj :∀ a b : α, ∀ a' b' : ↥s_val_fst, (a = ↑a') → (b = b') → ((a' = b') ↔ (a = b)),
  {intros a b a' b' h1 h2, split, intro h3, rw [h3, ← h2] at h1, exact h1,
   intro h, rw [h1, h2] at h, obtain ⟨a'', ha'⟩ := a', obtain ⟨b'', hb'⟩ := b',
   simp only [subtype.mk_eq_mk], simp only [subtype.coe_mk] at h, exact h},
  refine_struct({..} : is_well_order α s_val_snd),
  {intros,
  obtain ⟨a', ha⟩ := all_type a, obtain ⟨b', hb⟩ := all_type b,
  rw [ha, hb], have := s_property.1.trichotomous, specialize this a' b', simp only at this,
  rw [← ha, ← hb,← coe_inj a b a' b' ha hb, ha, hb], exact this},
  {intros a b c h1 h2, obtain ⟨a', ha⟩ := all_type a, obtain ⟨b', hb⟩ := all_type b, obtain ⟨c', hc⟩ := all_type c,
  rw ha,
  have := s_property.1.trans, have := this a' b' c', simp only at this, rw [← ha, ← hb, ← hc] at this,
  rw ← ha, exact this h1 h2},
  {split, intros,
  have : ∀ (b : ↥(s_val_fst)) (a' : α), a' = b → acc s_val_snd a',
  {intro b, have := well_founded.induction s_property.1.wf b, apply this, intros, split, intros,
  apply ᾰ (all_type y).some _ y, exact (all_type y).some_spec, rw [← (all_type y).some_spec, ← ᾰ_1],
  exact ᾰ_2, },
  exact this (all_type a).some a (all_type a).some_spec}
end

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
