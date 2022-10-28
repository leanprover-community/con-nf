import mathlib.well_founded
import phase2.freedom_of_action.constrains

noncomputable theory

open cardinal quiver relation set
open_locale cardinal pointwise

universe u

namespace con_nf
variables [params.{u}] {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] (B : le_index α)

/-- A support `carrier` with a well-order `r` is called a *well-ordered support*. -/
@[ext]
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

variables {B}

noncomputable! def proto_smul : allowable_path B → word_support B → word_support B :=
λ π S,
{ carrier := π • S.carrier,
  r := λ a b, S.r ⟨π⁻¹ • a, mem_smul_set_iff_inv_smul_mem.1 a.2⟩
    ⟨π⁻¹ • b, mem_smul_set_iff_inv_smul_mem.1 b.2⟩,
  wo :=
    { trichotomous := λ a b, begin
        convert S.wo.trichotomous ⟨π⁻¹ • ↑a, _⟩ ⟨π⁻¹ • ↑b, _⟩ using 2,
        simp [subtype.coe_inj],
      end,
      trans := begin intros,apply S.wo.trans, apply ᾰ, apply ᾰ_1 end,
      wf := begin have := @inv_image.is_well_founded _ _ S.r ⟨S.wo.wf⟩, convert (this _).wf, end } }

noncomputable! instance : has_smul (allowable_path B) (word_support B) := ⟨proto_smul⟩

@[simp] lemma carrier_smul (π : allowable_path B) (S : word_support B) :
  (π • S).carrier = π • S.carrier := rfl

@[simp] lemma r_smul (π : allowable_path B) (S : word_support B) :
  (π • S).r =  λ a b, S.r ⟨π⁻¹ • a, mem_smul_set_iff_inv_smul_mem.1 a.2⟩
    ⟨π⁻¹ • b, mem_smul_set_iff_inv_smul_mem.1 b.2⟩ := rfl

noncomputable! instance : mul_action (allowable_path B) (word_support B) :=
{ smul := proto_smul,
  one_smul := λ S, begin
    cases S,
    dsimp [proto_smul],
    simp only [struct_perm.coe_to_near_litter_perm, map_one, inv_one, one_smul, eq_self_iff_true,
      true_and],
    dsimp [sum.map],
    have backup : (↥((1 : allowable_path B) • S_carrier) : Type u) = (↥S_carrier : Type u),
    rw mul_action.one_smul,
    have : (↥((1 : allowable_path B) • S_carrier) : Type u) = (↥S_carrier : Type u),
    rw mul_action.one_smul,
    convert heq_of_eq _,
    rw mul_action.one_smul,
    suffices : S_r == λ o1 o2, S_r (cast this o1) (cast this o2), exact this,
    revert S_r this,
    rw backup,
    intros,
    apply heq_of_eq,
    funext,
    refl,
    funext,
    obtain ⟨⟨a, _⟩, _⟩ := a,
    obtain ⟨⟨b, _⟩, _⟩ := b,
    simp only [subtype.coe_mk, one_smul, eq_self_iff_true, set_coe_cast],
  end,
  mul_smul := λ x y S, begin
    cases S,
    dsimp [proto_smul],
    simp only [prod.mk.inj_iff],
    split,
    apply mul_action.mul_smul,
    simp only [map_mul, mul_inv_rev],
    have h : ↥((x * y) • S_carrier) = ↥(x • y • S_carrier), rw mul_action.mul_smul,
    have h2 : ↥((x * y) • S_carrier) = ↥(x • y • S_carrier), rw mul_action.mul_smul,
    let f : ↥((x * y) • S_carrier) → ↥((x * y) • S_carrier) → Prop :=
      λ c₁ c₂ : ↥((x * y) • S_carrier), _,
    let g : ↥(x • y • S_carrier) → ↥(x • y • S_carrier) → Prop :=
      λ d₁ d₂ : ↥(x • y • S_carrier), f (cast (eq.symm h) d₁) (cast (eq.symm h) d₂),
    suffices : (λ (c₁ c₂ : ↥((x * y) • S_carrier)), g (cast (h2) c₁) (cast (h2) c₂)) == _,
    dsimp [g] at this,
    simp only [eq_self_iff_true, subtype.val_eq_coe, cast_cast, set_coe_cast, subtype.coe_eta]
      at this,
    exact this,
    revert h2,
    rw h,
    intro h2,
    apply heq_of_eq,
    funext,
    dsimp [g, f],
    have : ∀ c : ↥(x • y • S_carrier), (↑(cast (eq.symm h) c) : support_condition ↑B) = ↑c, intros,
    have h2 : ((x * y) • S_carrier) = (x • y • S_carrier), rw mul_action.mul_smul,
    clear g,
    cases c,
    simp only [subtype.coe_mk],
    revert c_property h,
    rw ←h2,
    intros,
    simp only [set_coe_cast, subtype.coe_mk],
    apply congr, apply congr,
    refl,
    simp only,
    rw mul_action.mul_smul,
    congr' 2,
    exact this c₁,
    simp only,
    rw mul_action.mul_smul,
    congr' 2,
    exact this c₂,
  end }

/-- We can lower a support to a lower proper type index with respect to a path `A : α ⟶ β` by only
keeping support conditions whose paths begin with `A`. -/
def word_support.lower {β : type_index} (S : word_support B) (A : path B.index β) :
  word_support ⟨β, B.path.comp A⟩ :=
{ carrier := {c | c.extend_path A ∈ S.carrier},
  r := λ c₁ c₂, S.r ⟨c₁.val.extend_path A, c₁.prop⟩ ⟨c₂.val.extend_path A, c₂.prop⟩,
  wo :=
    { trichotomous := λ a b, begin
        convert S.wo.trichotomous _ _ using 2,
        simp_rw [subtype.ext_iff, subtype.coe_mk, support_condition.extend_path_inj,
          subtype.val_eq_coe],
      end,
      trans := λ _ _ _, S.wo.trans _ _ _,
      wf := (@inv_image.is_well_founded _ _ S.r ⟨S.wo.wf⟩ _).wf } }

/-- The lowering operation reflects the constrains `≺` relation. -/
lemma constrains.extend_path {β : type_index} {A : path B.index β} :
  ∀ {c d : support_condition (⟨β, B.path.comp A⟩ : le_index α)},
    c ≺ d → c.extend_path A ≺ d.extend_path A
| _ _ (constrains.mem_litter L a ha _) := constrains.mem_litter _ _ ha (A.comp _)
| _ _ (constrains.near_litter N hN _) := constrains.near_litter _ hN (A.comp _)
| _ _ (constrains.symm_diff N a ha _) := constrains.symm_diff _ _ ha (A.comp _)
| _ _ (constrains.f_map hγ hδ hγδ p t c hc) := begin
    dsimp [le_index.path] at *,
    revert t c,
    rw path.comp_assoc,
    intros,
    have := constrains.f_map hγ hδ hγδ (A.comp p) t c hc,
    rwa [←path.comp_cons, path.comp_assoc] at this,
end
using_well_founded { dec_tac := `[sorry] }

/-- Since the lowering of any strong support is strong, we keep track of this fact here. -/
def strong_support.lower {β : type_index} (S : strong_support B) (A : path B.index β) :
  strong_support ⟨β, B.path.comp A⟩ :=
⟨S.to_word_support.lower A, begin
  intros,
  dsimp [le_index.path] at *,
  exact S.strong (c.extend_path A) hc (d.extend_path A) H.extend_path,
end⟩

infix ` ≺≺ `:50 := refl_trans_gen (constrains _)

variable {B}

namespace potential_support

/-- The down-closure of a set of support conditions under the `constrains` relation.
Everything that (recursively) constrains a condition in `S` is included in its down-closure. -/
def closure (S : set (support_condition B)) : set (support_condition B) := ⋃ c ∈ S, {d | d ≺≺ c}

@[simp] lemma mem_closure {S : set (support_condition B)} {c} : c ∈ closure S ↔ ∃ d ∈ S, c ≺≺ d :=
mem_Union₂

/-- The closure of a potential support is a superset of the original potential support. -/
lemma subset_closure (S : set (support_condition B)) : S ⊆ closure S :=
λ c hc, mem_closure.2 ⟨c, hc, refl_trans_gen.refl⟩

/-- The down-closure of a set that supports a tangle also supports that tangle. This is because
being a support is preserved under set union. -/
lemma closure_supports (t : tangle_path B) (S : support B (allowable_path B) t) :
  supports (allowable_path B) (closure S.carrier) t :=
S.supports.mono $ subset_closure S

end potential_support

namespace support
variables {t : tangle_path B}

/-- This really should be computable. However, Lean's computability checker is a bit broken. -/
noncomputable! def closure (S : support B (allowable_path B) t) : support B (allowable_path B) t :=
⟨potential_support.closure S, potential_support.closure_supports t S⟩

@[simp] lemma mem_closure {S : support B (allowable_path B) t} {c} :
  c ∈ closure S ↔ ∃ d ∈ S, c ≺≺ d :=
mem_Union₂

end support

private lemma mk_path_n_lt_regular (c : cardinal) (hc : c.is_regular) (hcΛ : #Λ < c) : ∀ (A B : type_index) (n : ℕ), #{p : path A B // p.length = n} < c
| A B 0 := begin
  by_cases A = B,
  { subst h,
    convert lt_of_eq_of_lt (mk_singleton $ @path.nil _ _ A) (lt_of_lt_of_le one_lt_aleph_0 hc.aleph_0_le) using 3,
    ext,
    split,
    { intro hx,
      cases x,
      { exact mem_singleton _ },
      { rw path.length_cons at hx,
        cases hx } },
    { rintro ⟨⟩,
      exact path.length_nil } },
  { convert lt_of_eq_of_lt (mk_emptyc $ @path _ _ A B) (lt_of_lt_of_le aleph_0_pos hc.aleph_0_le) using 3,
    ext,
    split,
    { intro hx,
      cases x,
      { exact h rfl },
      { rw path.length_cons at hx,
        cases hx } },
    { rintro ⟨⟩ } }
end
| A B (nat.succ N) := begin
  have : {p : path A B // p.length = N.succ} ≃ Σ (C : type_index), {q : path A C // q.length = N ∧ hom C B},
  sorry { refine ⟨_, _, _, _⟩,
    { rintro ⟨⟨⟩ | ⟨C, _, q, hhom⟩, hp⟩,
      { cases hp },
      { simp only [path.length_cons, nat.add_one] at hp,
        refine ⟨C, q, hp, hhom⟩ } },
    { rintro ⟨C, q, hp, hhom⟩,
      refine ⟨q.cons hhom, _⟩,
      rw [←nat.add_one, ←hp, path.length_cons] },
  { rintro ⟨p, hp⟩,
    cases p,
    { cases hp },
    simp only [eq_self_iff_true, heq_iff_eq, and_self] },
  { rintro ⟨C, q, hq, hhom⟩,
    simp only [eq_self_iff_true, heq_iff_eq, and_self] } },
  rw [mk_congr this, mk_sigma _],
  refine sum_lt_of_is_regular hc (lt_of_eq_of_lt mk_type_index hcΛ) _,
  refine λ C, lt_of_le_of_lt (mk_subtype_mono $ λ x, and.left) (mk_path_n_lt_regular A C N),
end

private lemma mk_path_lt_regular {c : cardinal} (hc : c.is_regular) (hcΛ : #Λ < c)
  {B β : type_index} : #(@path type_index _ B β) < c :=
begin
  have : (Σ (n : ℕ), {p : path B β // p.length = n}) ≃ path B β,
  sorry { refine ⟨λ p, p, λ p, ⟨p.length, p, rfl⟩, _, λ p, rfl⟩,
    rintro ⟨n, p, rfl⟩, refl },
  rw [←mk_congr this, mk_sigma _],
  refine sum_lt_lift_of_is_regular hc _ (mk_path_n_lt_regular c hc hcΛ _ _),
  rw [mk_denumerable, lift_aleph_0],
  exact lt_of_le_of_lt Λ_limit.aleph_0_le hcΛ
end

/-- Each condition has a small number of immediate predecessors. -/
lemma small_mk_constrains (c : support_condition B) : small {d | d ≺ c} :=
begin
  simp_rw constrains_iff,
  obtain ⟨c | c, C⟩ := c,
  { exact (small_singleton (sum.inr c.fst.to_near_litter, C)).mono (by simp) },
  simp only [prod.mk.inj_iff, false_and, and_false, exists_false, false_or, exists_eq_right_right',
    ←and_assoc, ne.def, exists_and_distrib_right, exists_eq_right', set_of_or],
  refine small.union ((small_singleton (sum.inr c.fst.to_near_litter, C)).mono $ by simp)
    (small.union _ _),
  -- atom and its near-litters
  { simp_rw @eq_comm _ _ (_, _),
    exact small.image c.2.2 },

  -- litter and its f-map
  ---- extracting vars
  simp only [set_of_exists, set_of_and, set_of_eq_eq_singleton],
  refine small_Union Λ_lt_κ (λ β, small_Union (mk_type_index.trans_lt Λ_lt_κ) $ λ γ,
    small_Union Λ_lt_κ $ λ δ, small_Union_Prop $ λ hγ, small_Union_Prop $ λ hδ, small.mono
    (inter_subset_right _ _) $ small_Union (mk_path_lt_regular κ_regular Λ_lt_κ) $ λ A, _),

  ---- small supports are in fact small
  have tangle_path_unique : ∀ (β : Λ) (γ : type_index) (δ : Λ) (hγ : γ < β) (hδ : δ < β)
    (A : path (B : type_index) β),
      {t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α) |
        ((sum.inr c : atom ⊕ near_litter), C) = (sum.inr (f_map_path hγ hδ t).to_near_litter,
          (A.cons (with_bot.coe_lt_coe.2 hδ)).cons (with_bot.bot_lt_coe δ))}.subsingleton,
  { intros β γ δ hγ hδ A t ht t' ht',
    obtain ⟨-, hheq⟩ := f_map_path_injective (litter.to_near_litter_injective
        (sum.inr.inj (prod.eq_iff_fst_eq_snd_eq.1 $ ht.symm.trans ht').1)),
    exact eq_of_heq hheq },
  have small_carrier : ∀ (β : Λ) (γ : type_index) (δ : Λ) (hγ : γ < β) (hδ : δ < β)
    (A : path (B : type_index) β)
      (t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α)),
        small ((designated_support_path t).to_support.carrier) :=
    λ _ _ _ _ _ _ t, (designated_support_path t).small,
  have image_of : ∀ (β : Λ) (γ : type_index) (δ : Λ) (hγ : γ < β) (hδ : δ < β)
    (A : path (B : type_index) β), {d : support_condition ↑B |
      ∃ (t : tangle_path ↑(lt_index.mk' hγ (B.path.comp A)))
  (c_1 : support_condition (lt_index.mk' hγ (B.path.comp A) : le_index α).index),
  c_1 ∈ (designated_support_path t).to_support.carrier ∧
    d = (prod.fst c_1, (A.cons hγ).comp c_1.snd) ∧
      ((sum.inr c : atom ⊕ near_litter), C) = (sum.inr (f_map_path hγ hδ t).to_near_litter,
        (A.cons (with_bot.coe_lt_coe.2 hδ)).cons (with_bot.bot_lt_coe δ))} = (λ d, (prod.fst d,
          (A.cons hγ).comp d.snd)) ''
            ⋃₀ ((λ x : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α),
              (designated_support_path x).to_support.carrier) ''
                {t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α) |
                  ((sum.inr c : atom ⊕ near_litter), C) =
                    (sum.inr (f_map_path hγ hδ t).to_near_litter,
                      (A.cons (with_bot.coe_lt_coe.2 hδ)).cons (with_bot.bot_lt_coe δ))}),
  { refine λ _ _ _ _ _ _, set.ext (λ _, ⟨_, _⟩),
    { rintro ⟨t, e, he, ⟨⟩, hc⟩,
      exact ⟨_, ⟨_, ⟨_, hc, rfl⟩, he⟩, rfl⟩ },
    { rintro ⟨_, ⟨_, ⟨_, hc, ⟨⟩⟩, he⟩, ⟨⟩⟩,
      exact ⟨_, _, he, rfl, hc⟩ } },
  refine small.mono (inter_subset_left _ _) _,
  sorry,

  -- refine lt_of_le_of_lt mk_image_le
  --   (lt_of_le_of_lt (mk_sUnion_le _) $ mul_lt_of_lt κ_regular.aleph_0_le _ _),
  -- { refine lt_of_le_of_lt mk_image_le _,
  --   exact lt_of_le_of_lt
  --     (le_one_iff_subsingleton.2 $ (set.subsingleton_coe _).2 $ tangle_path_unique β γ δ hγ hδ A)
  --     (lt_of_lt_of_le one_lt_aleph_0 κ_regular.aleph_0_le) },
  -- refine supr_lt_of_is_regular κ_regular _ _,
  -- { refine lt_of_le_of_lt mk_image_le _,
  --   exact lt_of_le_of_lt
  --     (le_one_iff_subsingleton.2 $ (set.subsingleton_coe _).2 $ tangle_path_unique β γ δ hγ hδ A)
  --     (lt_of_lt_of_le one_lt_aleph_0 κ_regular.aleph_0_le) },
  -- rintro ⟨s, t, ht, rfl⟩,
  -- exact small_carrier β γ δ hγ hδ A t,
end

/-- There are only `<κ`-many things that recursively constrain any given support condition.
This is because `constrains` is well-founded and each condition has `< κ` immediate predecessors. -/
lemma small_mk_gen_constrains : ∀ (c : support_condition B), small {d | d ≺≺ c}
| c := begin
  simp_rw [refl_trans_gen.cases_tail_iff _ _ c, set_of_or, set_of_eq_eq_singleton', ←exists_prop,
    set_of_exists, exists_prop, and.comm, ←exists_prop, set_of_exists],
  exact (small_singleton _).union ((small_mk_constrains c).bUnion $ λ d _,
    small_mk_gen_constrains _),
end
using_well_founded { dec_tac := `[exact ‹_ ≺ _›] }

/-- An application of the above lemma, since there are only `<κ`-many support conditions in `S`. -/
lemma small_support.closure_small {t : tangle_path B} (S : small_support B (allowable_path B) t) :
  small (S.to_support.closure : set (support_condition B)) :=
S.2.bUnion $ λ _ _, small_mk_gen_constrains _

/-- Any small support can be 'strengthened' into a strong support that is also small.
Check the blueprint for more information. -/
lemma strengthen_small_support (t : tangle_path B) (S : small_support B (allowable_path B) t) :
  ∃ T : small_strong_support t, S.carrier ⊆ T.carrier :=
⟨{ carrier := S.to_support.closure.carrier,
   r := (inv_image.wf _ (constrains_wf B)).exists_well_order_ge.some,
   wo := (inv_image.wf _ (constrains_wf B)).exists_well_order_ge.some_spec.2,
   supports := S.to_support.closure.supports,
   small := small_support.closure_small S,
   strong := λ c hc d hd, begin
     split,
     refine (inv_image.wf subtype.val $ constrains_wf B).exists_well_order_ge.some_spec.1
       ⟨d, _⟩ ⟨c, hc⟩ hd,
     simp only [support.carrier_eq_coe, set_like.mem_coe, support.mem_closure] at ⊢ hc,
     obtain ⟨e, he₁, he₂⟩ := hc,
     exact ⟨e, he₁, refl_trans_gen.head hd he₂⟩,
   end }, potential_support.subset_closure _⟩

/-- There exists a small strong support for any tangle, along any path. -/
lemma exists_strong_support (t : tangle_path B) : nonempty (small_strong_support t) :=
⟨(strengthen_small_support t (designated_support_path t)).some⟩

end con_nf
