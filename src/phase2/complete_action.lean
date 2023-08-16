import order.extension.well
import phase2.atom_completion
import phase2.near_litter_completion

open equiv function quiver set sum with_bot
open_locale classical pointwise

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α]
  {β : Iic α} [freedom_of_action_hypothesis β]

/-!
We now construct the completed action of a structural approximation using well-founded recursion
on support conditions. It remains to prove that this map yields an allowable permutation.
TODO: Rename `complete_atom_map`, `atom_completion` etc.
-/

noncomputable def complete_atom_map (π : struct_approx β) :
  extended_index β → atom → atom :=
hypothesis.fix_atom π.atom_completion π.near_litter_completion

noncomputable def complete_near_litter_map (π : struct_approx β) :
  extended_index β → near_litter → near_litter :=
hypothesis.fix_near_litter π.atom_completion π.near_litter_completion

noncomputable def complete_litter_map (π : struct_approx β)
  (A : extended_index β) (L : litter) : litter :=
(π.complete_near_litter_map A L.to_near_litter).1

noncomputable def foa_hypothesis (π : struct_approx β) {c : support_condition β} :
  hypothesis c :=
⟨λ B b hb, π.complete_atom_map B b, λ B N hb, π.complete_near_litter_map B N⟩

variables {π : struct_approx β}

section map_spec
variables {A : extended_index β} {a : atom} {L : litter} {N : near_litter}

lemma complete_atom_map_eq :
  π.complete_atom_map A a = π.atom_completion A a π.foa_hypothesis :=
hypothesis.fix_atom_eq _ _ _ _

lemma complete_near_litter_map_eq :
  π.complete_near_litter_map A N = π.near_litter_completion A N π.foa_hypothesis :=
hypothesis.fix_near_litter_eq _ _ _ _

lemma complete_litter_map_eq :
  π.complete_litter_map A L = π.litter_completion A L π.foa_hypothesis :=
by rw [complete_litter_map, complete_near_litter_map_eq]; refl

lemma complete_near_litter_map_fst_eq :
  (π.complete_near_litter_map A L.to_near_litter).1 = π.complete_litter_map A L := rfl

@[simp] lemma complete_near_litter_map_fst_eq' :
  (π.complete_near_litter_map A N).1 = π.complete_litter_map A N.1 :=
begin
  rw [complete_near_litter_map_eq, near_litter_completion, complete_litter_map_eq],
  refl,
end

@[simp] lemma foa_hypothesis_atom_image {c : support_condition β}
  (h : (inl a, A) <[α] c) :
  (π.foa_hypothesis : hypothesis c).atom_image A a h = π.complete_atom_map A a := rfl

@[simp] lemma foa_hypothesis_near_litter_image {c : support_condition β}
  (h : (inr N, A) <[α] c) :
  (π.foa_hypothesis : hypothesis c).near_litter_image A N h = π.complete_near_litter_map A N := rfl

end map_spec

lemma complete_atom_map_eq_of_mem_domain {a} {A} (h : a ∈ (π A).atom_perm.domain) :
  π.complete_atom_map A a = π A • a :=
by rw [complete_atom_map_eq, atom_completion, dif_pos h]

lemma complete_atom_map_eq_of_not_mem_domain {a} {A} (h : a ∉ (π A).atom_perm.domain) :
  π.complete_atom_map A a = ((π A).largest_sublitter a.1).order_iso
    ((π A).largest_sublitter (π.complete_litter_map A a.1))
    ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a h⟩ :=
by rw [complete_atom_map_eq, atom_completion, dif_neg h]; refl

@[simp] def near_litter_hypothesis_eq (A : extended_index β) (N : near_litter) :
  near_litter_hypothesis A N π.foa_hypothesis = π.foa_hypothesis := rfl

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_coe {A : extended_index β} {L : litter}
  (h : inflexible_coe L A) (h₁ h₂) :
  π.complete_litter_map A L =
  f_map (with_bot.coe_ne_coe.mpr $ coe_ne' h.hδε)
    ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).hypothesised_allowable
      h h₁ h₂ • h.t) :=
by rw [complete_litter_map_eq, litter_completion_of_inflexible_coe]

lemma complete_litter_map_eq_of_inflexible_coe' {A : extended_index β} {L : litter}
  (h : inflexible_coe L A) :
  π.complete_litter_map A L =
  if h' : _ ∧ _ then
    f_map (with_bot.coe_ne_coe.mpr $ coe_ne' h.hδε)
      ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).hypothesised_allowable
        h h'.1 h'.2 • h.t)
  else L :=
by rw [complete_litter_map_eq, litter_completion_of_inflexible_coe']

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_bot {A : extended_index β} {L : litter}
  (h : inflexible_bot L A) :
  π.complete_litter_map A L =
  f_map (show (⊥ : type_index) ≠ (h.ε : Λ), from with_bot.bot_ne_coe)
    (π.complete_atom_map (h.B.cons (with_bot.bot_lt_coe _)) h.a) :=
by rw [complete_litter_map_eq, litter_completion_of_inflexible_bot]; refl

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_flexible {A : extended_index β} {L : litter}
  (h : flexible α L A) :
  π.complete_litter_map A L = near_litter_approx.flexible_completion α (π A) A • L :=
by rw [complete_litter_map_eq, litter_completion_of_flexible _ _ _ _ h]

def trans_constrained (c d : support_condition β) : set (support_condition β) :=
{e | e <[α] c} ∪ {e | e <[α] d}

def refl_trans_constrained (c d : support_condition β) : set (support_condition β) :=
{e | e ≤[α] c} ∪ {e | e ≤[α] d}

lemma trans_constrained_symm (c d : support_condition β) :
  trans_constrained c d = trans_constrained d c := union_comm _ _

lemma refl_trans_constrained_symm (c d : support_condition β) :
  refl_trans_constrained c d = refl_trans_constrained d c := union_comm _ _

@[simp] lemma trans_constrained_self (c : support_condition β) :
  trans_constrained c c = {e | e <[α] c} := union_self _

@[simp] lemma refl_trans_constrained_self (c : support_condition β) :
  refl_trans_constrained c c = {e | e ≤[α] c} := union_self _

lemma mem_refl_trans_constrained_of_mem_trans_constrained {c d e : support_condition β}
  (he : e ∈ trans_constrained c d) : e ∈ refl_trans_constrained c d :=
begin
  cases he,
  exact or.inl he.to_refl,
  exact or.inr he.to_refl,
end

lemma trans_constrained_trans {c d e f : support_condition β}
  (he : e ∈ trans_constrained c d) (hf : f ≤[α] e) : f ∈ trans_constrained c d :=
begin
  cases he,
  exact or.inl (relation.trans_gen.trans_right hf he),
  exact or.inr (relation.trans_gen.trans_right hf he),
end

lemma refl_trans_constrained_trans {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f ≤[α] e) : f ∈ refl_trans_constrained c d :=
begin
  cases he,
  exact or.inl (hf.trans he),
  exact or.inr (hf.trans he),
end

lemma trans_constrained_of_refl_trans_constrained_of_trans_constrains
  {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f <[α] e) : f ∈ trans_constrained c d :=
begin
  cases he,
  exact or.inl (hf.trans_left he),
  exact or.inr (hf.trans_left he),
end

lemma trans_constrained_of_constrains {c d e f : support_condition β}
  (he : e ∈ trans_constrained c d) (hf : f ≺[α] e) : f ∈ trans_constrained c d :=
trans_constrained_trans he (relation.refl_trans_gen.single hf)

lemma refl_trans_constrained_of_constrains {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f ≺[α] e) : f ∈ refl_trans_constrained c d :=
refl_trans_constrained_trans he (relation.refl_trans_gen.single hf)

lemma trans_constrained_of_refl_trans_constrained_of_constrains {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f ≺[α] e) : f ∈ trans_constrained c d :=
trans_constrained_of_refl_trans_constrained_of_trans_constrains he (relation.trans_gen.single hf)

lemma fst_trans_constrained {c d : support_condition β}
  {A : extended_index β} {a : atom}
  (hac : (inl a, A) ∈ refl_trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
trans_constrained_of_refl_trans_constrained_of_constrains hac (constrains.atom a A)

lemma fst_mem_trans_constrained' {c d : support_condition β} {A : extended_index β} {a : atom}
  (h : (inl a, A) ∈ trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
trans_constrained_of_constrains h (constrains.atom a A)

lemma fst_mem_trans_constrained {c d : support_condition β} {A : extended_index β} {N : near_litter}
  (hN : (inr N, A) ∈ trans_constrained c d) :
  (inr N.fst.to_near_litter, A) ∈ trans_constrained c d :=
begin
  cases hN,
  exact or.inl (trans_gen_near_litter' hN),
  exact or.inr (trans_gen_near_litter' hN),
end

lemma fst_mem_refl_trans_constrained' {c d : support_condition β} {A : extended_index β} {a : atom}
  (h : (inl a, A) ∈ refl_trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ refl_trans_constrained c d :=
refl_trans_constrained_of_constrains h (constrains.atom a A)

lemma fst_mem_refl_trans_constrained {c d : support_condition β} {A : extended_index β}
  {N : near_litter} (hN : (inr N, A) ∈ refl_trans_constrained c d) :
  (inr N.fst.to_near_litter, A) ∈ refl_trans_constrained c d :=
begin
  cases hN,
  exact or.inl (refl_trans_gen_near_litter hN),
  exact or.inr (refl_trans_gen_near_litter hN),
end

lemma fst_mem_trans_constrained_of_mem_symm_diff {c d : support_condition β}
  {A : extended_index β} {N : near_litter} {a : atom} (h : a ∈ litter_set N.1 ∆ N)
  (hN : (inr N, A) ∈ trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
begin
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h,
  { rw mem_litter_set at h₁,
    rw h₁,
    exact fst_mem_trans_constrained hN, },
  { cases hN,
    { refine fst_mem_trans_constrained' (or.inl _),
      exact relation.trans_gen.head (constrains.symm_diff N a (or.inr ⟨h₁, h₂⟩) A) hN, },
    { refine fst_mem_trans_constrained' (or.inr _),
      exact relation.trans_gen.head (constrains.symm_diff N a (or.inr ⟨h₁, h₂⟩) A) hN, }, },
end

lemma fst_mem_refl_trans_constrained_of_mem_symm_diff {c d : support_condition β}
  {A : extended_index β} {N : near_litter} {a : atom} (h : a ∈ litter_set N.1 ∆ N)
  (hN : (inr N, A) ∈ refl_trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ refl_trans_constrained c d :=
begin
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h,
  { rw mem_litter_set at h₁,
    rw h₁,
    exact fst_mem_refl_trans_constrained hN, },
  { cases hN,
    { refine fst_mem_refl_trans_constrained' (or.inl _),
      exact relation.refl_trans_gen.head (constrains.symm_diff N a (or.inr ⟨h₁, h₂⟩) A) hN, },
    { refine fst_mem_refl_trans_constrained' (or.inr _),
      exact relation.refl_trans_gen.head (constrains.symm_diff N a (or.inr ⟨h₁, h₂⟩) A) hN, }, },
end

lemma fst_mem_trans_constrained_of_mem {c d : support_condition β}
  {A : extended_index β} {N : near_litter} {a : atom} (h : a ∈ N)
  (hN : (inr N, A) ∈ trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
begin
  by_cases ha : a.1 = N.1,
  { rw ha,
    exact fst_mem_trans_constrained hN, },
  { exact fst_mem_trans_constrained_of_mem_symm_diff (or.inr ⟨h, ha⟩) hN, },
end

lemma eq_of_sublitter_bijection_apply_eq {π : near_litter_approx} {L₁ L₂ L₃ L₄ : litter} {a b} :
  ((π.largest_sublitter L₁).order_iso (π.largest_sublitter L₂) a : atom) =
  (π.largest_sublitter L₃).order_iso (π.largest_sublitter L₄) b →
  L₁ = L₃ → L₂ = L₄ → (a : atom) = b :=
begin
  rintros h₁ rfl rfl,
  simp only [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at h₁,
  rw h₁,
end

noncomputable def constrained_action (π : struct_approx β) (s : set (support_condition β))
  (hs : small s) : struct_action β :=
λ B, {
  atom_map := λ a, ⟨∃ c : support_condition β, c ∈ s ∧ (inl a, B) ≤[α] c,
    λ h, π.complete_atom_map B a⟩,
  litter_map := λ L, ⟨∃ c : support_condition β, c ∈ s ∧ (inr L.to_near_litter, B) ≤[α] c,
    λ h, π.complete_near_litter_map B L.to_near_litter⟩,
  atom_map_dom_small := begin
    change small ((λ a : atom, (inl a, B)) ⁻¹'
      {c : support_condition β | ∃ d : support_condition β, d ∈ s ∧ c ≤[α] d}),
    simp_rw ← exists_prop,
    refine small.preimage _ (reduction_small' α hs),
    intros a b h,
    cases h,
    refl,
  end,
  litter_map_dom_small := begin
    change small ((λ L : litter, (inr L.to_near_litter, B)) ⁻¹'
      {c : support_condition β | ∃ d : support_condition β, d ∈ s ∧ c ≤[α] d}),
    simp_rw ← exists_prop,
    refine small.preimage _ (reduction_small' α hs),
    intros a b h,
    cases h,
    refl,
  end,
}

/-- An object like `ih_action` that can take two support conditions. -/
noncomputable def ihs_action (π : struct_approx β) (c d : support_condition β) : struct_action β :=
λ B, {
  atom_map := λ a, ⟨(inl a, B) ∈ trans_constrained c d,
    λ h, π.complete_atom_map B a⟩,
  litter_map := λ L, ⟨(inr L.to_near_litter, B) ∈ trans_constrained c d,
    λ h, π.complete_near_litter_map B L.to_near_litter⟩,
  atom_map_dom_small := small.union
    (ih_action π.foa_hypothesis B).atom_map_dom_small
    (ih_action π.foa_hypothesis B).atom_map_dom_small,
  litter_map_dom_small := small.union
    (ih_action π.foa_hypothesis B).litter_map_dom_small
    (ih_action π.foa_hypothesis B).litter_map_dom_small,
}

@[simp] lemma constrained_action_atom_map {π : struct_approx β} {s : set (support_condition β)}
  {hs : small s} {B : extended_index β} {a : atom} :
  (constrained_action π s hs B).atom_map a =
  ⟨∃ c : support_condition β, c ∈ s ∧ (inl a, B) ≤[α] c,
    λ h, complete_atom_map π B a⟩ := rfl

@[simp] lemma constrained_action_litter_map {π : struct_approx β} {s : set (support_condition β)}
  {hs : small s} {B : extended_index β} {L : litter} :
  (constrained_action π s hs B).litter_map L =
  ⟨∃ c : support_condition β, c ∈ s ∧ (inr L.to_near_litter, B) ≤[α] c,
    λ h, π.complete_near_litter_map B L.to_near_litter⟩ := rfl

@[simp] lemma ihs_action_atom_map {π : struct_approx β} {c d : support_condition β}
  {B : extended_index β} {a : atom} :
  (ihs_action π c d B).atom_map a =
  ⟨(inl a, B) ∈ trans_constrained c d,
    λ h, complete_atom_map π B a⟩ := rfl

@[simp] lemma ihs_action_litter_map {π : struct_approx β} {c d : support_condition β}
  {B : extended_index β} {L : litter} :
  (ihs_action π c d B).litter_map L =
  ⟨(inr L.to_near_litter, B) ∈ trans_constrained c d,
    λ h, π.complete_near_litter_map B L.to_near_litter⟩ := rfl

lemma ihs_action_symm (π : struct_approx β) (c d : support_condition β) :
  ihs_action π c d = ihs_action π d c :=
begin
  ext,
  rw [ihs_action_atom_map, ihs_action_atom_map, trans_constrained_symm],
  rw [ihs_action_litter_map, ihs_action_litter_map, trans_constrained_symm],
end

@[simp] lemma ihs_action_self (π : struct_approx β) (c : support_condition β) :
  ihs_action π c c = ih_action (π.foa_hypothesis : hypothesis c) :=
begin
  ext,
  { rw [ihs_action_atom_map, ih_action_atom_map, trans_constrained_self],
    refl, },
  { rw [ihs_action_litter_map, ih_action_litter_map, trans_constrained_self],
    refl, },
end

lemma constrained_action_mono {π : struct_approx β} {s t : set (support_condition β)}
  {hs : small s} {ht : small t} (h : s ⊆ t) :
  constrained_action π s hs ≤ constrained_action π t ht :=
λ B, ⟨
  ⟨λ a ha, ⟨ha.some, h ha.some_spec.1, ha.some_spec.2⟩, λ a h, rfl⟩,
  ⟨λ L hL, ⟨hL.some, h hL.some_spec.1, hL.some_spec.2⟩, λ L h, rfl⟩,
⟩

lemma ih_action_le_constrained_action {π : struct_approx β} {s : set (support_condition β)}
  {hs : small s} (c : support_condition β) (hc : ∃ d : support_condition β, d ∈ s ∧ c ≤[α] d) :
  ih_action (π.foa_hypothesis : hypothesis c) ≤ constrained_action π s hs :=
λ B, ⟨
  ⟨λ a ha, ⟨hc.some, hc.some_spec.1, trans ha.to_refl hc.some_spec.2⟩, λ a h, rfl⟩,
  ⟨λ L hL, ⟨hc.some, hc.some_spec.1, trans hL.to_refl hc.some_spec.2⟩, λ L h, rfl⟩,
⟩

lemma ih_action_eq_constrained_action (π : struct_approx β) (c : support_condition β) :
  ih_action (π.foa_hypothesis : hypothesis c) =
  constrained_action π {d | d ≺[α] c} (small_constrains c) :=
begin
  ext,
  { simp only [ih_action_atom_map, foa_hypothesis_atom_image, part.mem_mk_iff, exists_prop,
      mem_set_of_eq, constrained_action_atom_map, and.congr_left_iff, relation.trans_gen.tail'_iff],
    intro h,
    simp_rw and_comm,
    refl, },
  { simp only [ih_action_litter_map, part.mem_mk_iff, exists_prop, mem_set_of_eq,
      and.congr_left_iff, relation.trans_gen.tail'_iff, foa_hypothesis_near_litter_image,
      constrained_action_litter_map],
    intro h,
    simp_rw and_comm,
    refl, },
end

lemma ihs_action_eq_constrained_action (π : struct_approx β) (c d : support_condition β) :
  ihs_action π c d =
  constrained_action π ({e | e ≺[α] c} ∪ {e | e ≺[α] d})
    ((small_constrains c).union (small_constrains d)) :=
begin
  ext,
  { simp only [relation.trans_gen.tail'_iff, trans_constrained, mem_union, ihs_action_atom_map,
      part.mem_mk_iff, exists_prop, mem_set_of_eq, constrained_action_atom_map, and.congr_left_iff],
    intro h,
    split,
    { rintro (⟨b, hb₁, hb₂⟩ | ⟨b, hb₁, hb₂⟩),
      { exact ⟨b, or.inl hb₂, hb₁⟩, },
      { exact ⟨b, or.inr hb₂, hb₁⟩, }, },
    { rintro ⟨b, (hb₁ | hb₁), hb₂⟩,
      { exact or.inl ⟨b, hb₂, hb₁⟩, },
      { exact or.inr ⟨b, hb₂, hb₁⟩, }, }, },
  { simp only [relation.trans_gen.tail'_iff, trans_constrained, mem_union, part.mem_mk_iff,
      exists_prop, mem_set_of_eq,and.congr_left_iff, ihs_action_litter_map,
      constrained_action_litter_map],
    intro h,
    split,
    { rintro (⟨b, hb₁, hb₂⟩ | ⟨b, hb₁, hb₂⟩),
      { exact ⟨b, or.inl hb₂, hb₁⟩, },
      { exact ⟨b, or.inr hb₂, hb₁⟩, }, },
    { rintro ⟨b, (hb₁ | hb₁), hb₂⟩,
      { exact or.inl ⟨b, hb₂, hb₁⟩, },
      { exact or.inr ⟨b, hb₂, hb₁⟩, }, }, },
end

lemma ih_action_le_ihs_action (π : struct_approx β) (c d : support_condition β) :
  ih_action (π.foa_hypothesis : hypothesis c) ≤ ihs_action π c d :=
λ B, ⟨⟨λ a, or.inl, λ a h, rfl⟩, ⟨λ L, or.inl, λ L h, rfl⟩⟩

lemma ih_action_le {π : struct_approx β} {c d : support_condition β} (h : c ≤[α] d) :
  ih_action (π.foa_hypothesis : hypothesis c) ≤ ih_action (π.foa_hypothesis : hypothesis d) :=
begin
  refine λ B, ⟨⟨_, λ a h, rfl⟩, ⟨_, λ L h, rfl⟩⟩,
  { intros a ha,
    exact relation.trans_gen.trans_left ha h, },
  { intros a ha,
    exact relation.trans_gen.trans_left ha h, },
end

lemma ih_action_supports {A : extended_index β} {L : litter} (h : inflexible_coe L A) :
  ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons (coe_lt h.hδ))).supports h.t := {
  atom_mem := begin
    intros a B ha,
    simp only [struct_action.comp_apply, ih_action_atom_map],
    have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ ha,
    rw [← h.hL, ← h.hA] at this,
    exact this,
  end,
  litter_mem := begin
    intros L B hL,
    simp only [struct_action.comp_apply, ih_action_litter_map],
    have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ hL,
    rw [← h.hL, ← h.hA] at this,
    exact this,
  end,
}

lemma trans_gen_constrains_of_mem_designated_support
  {A : extended_index β} {L : litter} {h : inflexible_coe L A}
  {γ : Iic α} {δ ε : Iio α} {hδ : (δ : Λ) < γ} {hε : (ε : Λ) < γ} (hδε : δ ≠ ε)
  {C : path (h.δ : type_index) γ} {t : tangle δ} {d : support_condition h.δ}
  (hd₂ : (inr (f_map (subtype.coe_injective.ne (Iio.coe_injective.ne hδε)) t).to_near_litter,
    (C.cons (coe_lt hε)).cons (bot_lt_coe _)) ≤[α] d)
  (hd : (d.fst, (h.B.cons (coe_lt h.hδ)).comp d.snd) ≺[α] (inr L.to_near_litter, A))
  {B : extended_index δ} {a : atom}
  (hc : (inl a, B) ∈ (designated_support t).carrier) :
  (inl a, (h.B.cons (coe_lt h.hδ)).comp ((C.cons (coe_lt hδ)).comp B)) <[α]
    (inr L.to_near_litter, A) :=
begin
  refine relation.trans_gen.tail' _ hd,
  refine @refl_trans_gen_constrains_comp _ _ _ _ _ _ (inl a, _) d
    _ (h.B.cons $ coe_lt h.hδ),
  refine relation.refl_trans_gen.trans _ hd₂,
  exact relation.refl_trans_gen.single (constrains.f_map hδ hε hδε C t _ hc),
end

-- TODO: move to struct_perm
@[simp] lemma _root_.con_nf.struct_perm.derivative_fst {α β : type_index} (π : struct_perm α)
  (A : path α β) (N : near_litter) :
  (struct_perm.derivative A π • N).fst = struct_perm.derivative A π • N.fst := rfl

lemma to_struct_perm_bot : (allowable.to_struct_perm : allowable ⊥ → struct_perm ⊥) =
  struct_perm.to_bot_iso.to_monoid_hom := rfl

/-- I think it's quite a big deal that this isn't a defeq.
We should probably refactor structural permutations to be like structural approximations,
a function from extended indices to near-litter permutations. -/
@[simp] lemma to_struct_perm_to_near_litter_perm (π : allowable ⊥) :
  π.to_struct_perm.to_near_litter_perm = π :=
begin
  ext a : 2,
  rw [to_struct_perm_bot, struct_perm.coe_to_near_litter_perm],
  simp only [mul_equiv.coe_to_monoid_hom, struct_perm.coe_to_bot_iso, struct_perm.of_bot_to_bot],
end

-- TODO: move earlier and use
lemma complete_near_litter_map_eq' (A : extended_index β) (N : near_litter) :
  (π.complete_near_litter_map A N : set atom) =
  (π.complete_near_litter_map A N.fst.to_near_litter) ∆
    (π.complete_atom_map A '' litter_set N.fst ∆ ↑N) :=
begin
  simp only [complete_near_litter_map_eq, near_litter_completion, near_litter_completion_map,
    near_litter_hypothesis_eq, near_litter_approx.coe_largest_sublitter, mem_diff,
    foa_hypothesis_atom_image, near_litter.coe_mk, subtype.coe_mk, litter.coe_to_near_litter,
    litter.to_near_litter_fst, symm_diff_self, bot_eq_empty, mem_empty_iff_false, false_and,
    Union_neg', not_false_iff, Union_empty, symm_diff_empty],
  ext a : 1,
  split,
  { rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨_, ⟨b, rfl⟩, _, ⟨⟨hb₁, hb₂⟩, rfl⟩, ha⟩, ha₂⟩),
    { refine or.inl ⟨or.inl ha₁, _⟩,
      simp only [mem_image, not_exists, not_and],
      intros b hb,
      by_cases b ∈ (π A).atom_perm.domain,
      { rw complete_atom_map_eq_of_mem_domain h,
        rintro rfl,
        exact ha₁.2 ((π A).atom_perm.map_domain h), },
      { simp only [mem_Union, mem_singleton_iff, not_exists, and_imp] at ha₂,
        exact ne.symm (ha₂ b hb h), }, },
    { by_cases a ∈ litter_set N.fst,
      { refine or.inl ⟨or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, _⟩,
        simp only [mem_image, not_exists, not_and],
        intros b hb,
        by_cases hb' : b ∈ (π A).atom_perm.domain,
        { rw complete_atom_map_eq_of_mem_domain hb',
          intro hab,
          cases (π A).atom_perm.inj_on hb' ha₁.2 hab,
          cases hb,
          exact hb.2 ha₁.1,
          exact hb.2 h, },
        { simp only [mem_Union, mem_singleton_iff, not_exists, and_imp] at ha₂,
          exact ne.symm (ha₂ b hb hb'), }, },
      { refine or.inr ⟨⟨a, or.inr ⟨ha₁.1, h⟩, _⟩, _⟩,
        { simp only [complete_atom_map_eq_of_mem_domain ha₁.2], },
        rintro (ha | ⟨b, hb₁, hb₂⟩),
        { exact ha.2 ((π A).atom_perm.map_domain ha₁.2), },
        { cases (π A).atom_perm.inj_on hb₁.2 ha₁.2 hb₂,
          exact h hb₁.1, }, }, },
    { simp only [mem_singleton_iff] at ha,
      subst ha,
      refine or.inr ⟨⟨b, hb₁, rfl⟩, _⟩,
      contrapose! ha₂,
      cases ha₂,
      { exact or.inl ha₂, },
      obtain ⟨a, ha₁, ha₂⟩ := ha₂,
      by_cases a ∈ N,
      { rw ← ha₂,
        exact or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, },
      rw complete_atom_map_eq_of_not_mem_domain hb₂,
      simp only [mem_union, mem_diff, mem_litter_set, sublitter.order_iso_apply_fst_eq,
        near_litter_approx.largest_sublitter_litter],
      refine or.inl ⟨_, _⟩,
      { suffices : b ∈ litter_set N.fst,
        { rw mem_litter_set at this,
          rw [this, complete_litter_map_eq], },
        cases hb₁,
        { exact hb₁.1, },
        exfalso,
        rw complete_atom_map_eq_of_not_mem_domain hb₂ at ha₂,
        have : π A • a ∈ _ := (π A).atom_perm.map_domain ha₁.2,
        rw ha₂ at this,
        exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
          (sublitter.order_iso_apply_mem _) this, },
      { exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
          (sublitter.order_iso_apply_mem _), }, }, },
  { rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨a, ha₁, rfl⟩, ha₂⟩),
    { refine or.inl ⟨or.inl ha₁, _⟩,
      simp only [mem_Union, mem_singleton_iff, not_exists, and_imp],
      rintros b hb₁ hb₂ rfl,
      exact ha₂ ⟨b, hb₁, rfl⟩, },
    { refine or.inl ⟨_, _⟩,
      { by_cases a ∈ N,
        { exact or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, },
        { simp only [mem_image, not_exists, not_and] at ha₂,
          have := ha₂ a (or.inl ⟨ha₁.1, h⟩),
          rw complete_atom_map_eq_of_mem_domain ha₁.2 at this,
          cases this rfl, }, },
      { contrapose! ha₂,
        obtain ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, ha₂⟩ := ha₂,
        simp only [mem_singleton_iff] at ha₂,
        rw ha₂,
        exact ⟨b, hb.1, rfl⟩, }, },
    { rw [mem_union, not_or_distrib] at ha₂,
      by_cases ha : a ∈ litter_set N.fst,
      { have : a ∉ (π A).atom_perm.domain,
        { intro h,
          refine ha₂.2 ⟨a, ⟨ha, h⟩, _⟩,
          simp only [complete_atom_map_eq_of_mem_domain h], },
        refine or.inr ⟨_, _⟩,
        { exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, this⟩, rfl⟩, rfl⟩, },
        { rintro (h | ⟨b, hb₁, hb₂⟩),
          { exact ha₂.1 h, },
          simp only [complete_atom_map_eq_of_not_mem_domain this] at hb₂,
          have : π A • b ∈ _ := (π A).atom_perm.map_domain hb₁.2,
          rw hb₂ at this,
          exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
            (sublitter.order_iso_apply_mem _) this, }, },
      { by_cases a ∈ (π A).atom_perm.domain,
        { refine or.inl ⟨_, _⟩,
          { simp only [complete_atom_map_eq_of_mem_domain h],
            refine or.inr ⟨a, ⟨_, h⟩, rfl⟩,
            cases ha₁,
            cases ha ha₁.1,
            exact ha₁.1, },
          { simp only [mem_Union, mem_singleton_iff, not_exists, and_imp],
            intros b hb₁ hb₂ hab,
            rw [complete_atom_map_eq_of_mem_domain h,
              complete_atom_map_eq_of_not_mem_domain hb₂] at hab,
            have : π A • a ∈ _ := (π A).atom_perm.map_domain h,
            rw hab at this,
            exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
              (sublitter.order_iso_apply_mem _) this, }, },
        { refine or.inr ⟨_, _⟩,
          { exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, h⟩, rfl⟩, rfl⟩, },
          rintro (h' | ⟨b, hb₁, hb₂⟩),
          { exact ha₂.1 h', },
          simp only [complete_atom_map_eq_of_not_mem_domain h] at hb₂,
          have : π A • b ∈ _ := (π A).atom_perm.map_domain hb₁.2,
          rw hb₂ at this,
          exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
            (sublitter.order_iso_apply_mem _) this, }, }, }, },
end

lemma complete_near_litter_map_to_near_litter_eq (A : extended_index β) (L : litter) :
  (complete_near_litter_map π A L.to_near_litter : set atom) =
  (litter_set (complete_litter_map π A L) \ (π A).atom_perm.domain) ∪
  π A • (litter_set L ∩ (π A).atom_perm.domain) :=
begin
  rw [complete_near_litter_map_eq, near_litter_completion, near_litter.coe_mk,
    subtype.coe_mk, near_litter_completion_map],
  simp only [near_litter_hypothesis_eq, near_litter_approx.coe_largest_sublitter,
    litter.coe_to_near_litter, mem_diff, litter.to_near_litter_fst, symm_diff_self, bot_eq_empty,
    mem_empty_iff_false, false_and, Union_neg', not_false_iff, Union_empty, symm_diff_empty],
  rw complete_litter_map_eq,
  refl,
end

lemma eq_of_mem_complete_near_litter_map
  {L₁ L₂ : litter} {A : extended_index β}
  (a : atom)
  (ha₁ : a ∈ π.complete_near_litter_map A L₁.to_near_litter)
  (ha₂ : a ∈ π.complete_near_litter_map A L₂.to_near_litter) :
  π.complete_litter_map A L₁ = π.complete_litter_map A L₂ :=
begin
  rw [← set_like.mem_coe, complete_near_litter_map_to_near_litter_eq] at ha₁ ha₂,
  obtain (⟨ha₁, ha₁'⟩ | ha₁) := ha₁;
  obtain (⟨ha₂, ha₂'⟩ | ha₂) := ha₂,
  { exact eq_of_mem_litter_set_of_mem_litter_set ha₁ ha₂, },
  { obtain ⟨b, hb, rfl⟩ := ha₂,
    cases ha₁' ((π A).atom_perm.map_domain hb.2), },
  { obtain ⟨b, hb, rfl⟩ := ha₁,
    cases ha₂' ((π A).atom_perm.map_domain hb.2), },
  { obtain ⟨b, hb, rfl⟩ := ha₁,
    obtain ⟨c, hc, hc'⟩ := ha₂,
    cases (π A).atom_perm.inj_on hc.2 hb.2 hc',
    rw eq_of_mem_litter_set_of_mem_litter_set hb.1 hc.1, },
end

lemma eq_of_complete_litter_map_inter_nonempty
  {L₁ L₂ : litter} {A : extended_index β}
  (h : ((π.complete_near_litter_map A L₁.to_near_litter : set atom) ∩
    π.complete_near_litter_map A L₂.to_near_litter).nonempty) :
  π.complete_litter_map A L₁ = π.complete_litter_map A L₂ :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := h,
  exact eq_of_mem_complete_near_litter_map a ha₁ ha₂,
end

lemma atom_injective_extends {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful)
  {a b : atom} {A : extended_index β}
  (hac : (inl a, A) ∈ refl_trans_constrained c d)
  (hbc : (inl b, A) ∈ refl_trans_constrained c d)
  (h : π.complete_atom_map A a = π.complete_atom_map A b) :
  a = b :=
begin
  by_cases ha : a ∈ (π A).atom_perm.domain;
  by_cases hb : b ∈ (π A).atom_perm.domain,
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    exact (π A).atom_perm.inj_on ha hb h, },
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h.symm).some)
      ((π A).atom_perm.map_domain ha), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h).some)
      ((π A).atom_perm.map_domain hb), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    have h₁ := (subtype.coe_eq_iff.mp h).some.1,
    have h₂ := (((π A).largest_sublitter b.1).order_iso
      ((π A).largest_sublitter (π.complete_litter_map A b.1))
      ⟨b, (π A).mem_largest_sublitter_of_not_mem_domain b hb⟩).prop.1,
    have := (hcd A).litter_map_injective
      (fst_trans_constrained hac) (fst_trans_constrained hbc) _,
    { have := eq_of_sublitter_bijection_apply_eq h this (by rw this),
      rw [set_like.coe_mk, set_like.coe_mk] at this,
      exact this, },
    { refine near_litter.inter_nonempty_of_fst_eq_fst _,
      simp only [ihs_action_litter_map, complete_near_litter_map_fst_eq],
      exact eq_of_mem_litter_set_of_mem_litter_set h₁ h₂, }, },
end

def in_out (π : near_litter_perm) (a : atom) (L : litter) : Prop :=
xor (a.1 = L) ((π • a).1 = π • L)

lemma in_out_def {π : near_litter_perm} {a : atom} {L : litter} :
  in_out π a L ↔ xor (a.1 = L) ((π • a).1 = π • L) := iff.rfl

structure _root_.con_nf.near_litter_perm.biexact (π π' : near_litter_perm)
  (atoms : set atom) (litters : set litter) : Prop :=
(smul_eq_smul_atom : ∀ a ∈ atoms, π • a = π' • a)
(smul_eq_smul_litter : ∀ L ∈ litters, π • L = π' • L)
(left_exact : ∀ L ∈ litters, ∀ a, in_out π a L → π • a = π' • a)
(right_exact : ∀ L ∈ litters, ∀ a, in_out π' a L → π • a = π' • a)

@[simp] lemma _root_.xor_elim_left {a b : Prop} (h : a) : xor a b ↔ ¬b :=
by unfold xor; tauto

@[simp] lemma _root_.xor_elim_right {a b : Prop} (h : b) : xor a b ↔ ¬a :=
by unfold xor; tauto

@[simp] lemma _root_.xor_elim_not_left {a b : Prop} (h : ¬a) : xor a b ↔ b :=
by unfold xor; tauto

@[simp] lemma _root_.xor_elim_not_right {a b : Prop} (h : ¬b) : xor a b ↔ a :=
by unfold xor; tauto

lemma _root_.con_nf.near_litter_perm.biexact.atoms
  {π π' : near_litter_perm} (s : set atom) (hs : ∀ a ∈ s, π • a = π' • a) :
  near_litter_perm.biexact π π' s ∅ :=
⟨hs, λ L, false.elim, λ L, false.elim, λ L, false.elim⟩

lemma _root_.con_nf.near_litter_perm.biexact.litter
  {π π' : near_litter_perm} (L : litter)
  (hL : π • L = π' • L)
  (hL₁ : ∀ a, in_out π a L → π • a = π' • a)
  (hL₂ : ∀ a, in_out π' a L → π • a = π' • a) :
  near_litter_perm.biexact π π' ∅ {L} :=
⟨
  λ a ha, ha.elim,
  λ L' hL', by cases hL'; exact hL,
  λ L' hL', by cases hL'; exact hL₁,
  λ L' hL', by cases hL'; exact hL₂,
⟩

lemma _root_.con_nf.near_litter_perm.biexact.symm
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters) :
  near_litter_perm.biexact π' π atoms litters :=
⟨
  λ a ha, (h.smul_eq_smul_atom a ha).symm,
  λ L hL, (h.smul_eq_smul_litter L hL).symm,
  λ L hL a ha, (h.right_exact L hL a ha).symm,
  λ L hL a ha, (h.left_exact L hL a ha).symm,
⟩

lemma _root_.con_nf.near_litter_perm.biexact.union
  {π π' : near_litter_perm} {s₁ s₂ : set atom} {t₁ t₂ : set litter}
  (h₁ : near_litter_perm.biexact π π' s₁ t₁)
  (h₂ : near_litter_perm.biexact π π' s₂ t₂) :
  near_litter_perm.biexact π π' (s₁ ∪ s₂) (t₁ ∪ t₂) :=
⟨
  λ a ha, ha.elim (h₁.smul_eq_smul_atom a) (h₂.smul_eq_smul_atom a),
  λ L hL, hL.elim (h₁.smul_eq_smul_litter L) (h₂.smul_eq_smul_litter L),
  λ L hL, hL.elim (h₁.left_exact L) (h₂.left_exact L),
  λ L hL, hL.elim (h₁.right_exact L) (h₂.right_exact L),
⟩

lemma _root_.con_nf.near_litter_perm.biexact.smul_litter_subset
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters)
  (L : litter) (hL : L ∈ litters) :
  (π • L.to_near_litter : set atom) ⊆ π' • L.to_near_litter :=
begin
  rintros _ ⟨a, ha, rfl⟩,
  simp only [litter.coe_to_near_litter, mem_litter_set] at ha,
  by_cases h' : (π • a).1 = π • L,
  by_cases h'' : (π'⁻¹ • π • a).1 = L,
  { refine ⟨_, h'', _⟩,
    rw smul_inv_smul, },
  { have := h.right_exact L hL _ (or.inr ⟨_, h''⟩),
    { rw [smul_inv_smul, smul_left_cancel_iff, inv_smul_eq_iff] at this,
      rw this,
      exact ⟨a, ha, rfl⟩, },
    { rw [smul_inv_smul, h', h.smul_eq_smul_litter L hL], }, },
  { rw h.left_exact L hL a (or.inl ⟨ha, h'⟩),
    simp only [litter.coe_to_near_litter, smul_mem_smul_set_iff, mem_litter_set],
    exact ha, },
end

lemma _root_.con_nf.near_litter_perm.biexact.smul_litter
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters)
  (L : litter) (hL : L ∈ litters) :
  π • L.to_near_litter = π' • L.to_near_litter :=
begin
  refine set_like.coe_injective _,
  refine subset_antisymm _ _,
  exact h.smul_litter_subset L hL,
  exact h.symm.smul_litter_subset L hL,
end

lemma _root_.con_nf.near_litter_perm.biexact.smul_near_litter
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters)
  (N : near_litter) (hN : N.1 ∈ litters) (hN' : litter_set N.1 ∆ N ⊆ atoms) :
  π • N = π' • N :=
begin
  refine set_like.coe_injective _,
  change _ • _ = _ • _,
  conv_lhs { rw near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul, },
  conv_rhs { rw near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul, },
  refine congr_arg2 _
    (congr_arg set_like.coe (h.smul_litter N.1 hN)) _,
  ext a : 1,
  split,
  { rintro ⟨b, hb, rfl⟩,
    rw h.smul_eq_smul_atom b (hN' hb),
    exact ⟨b, hb, rfl⟩, },
  { rintro ⟨b, hb, rfl⟩,
    rw ← h.smul_eq_smul_atom b (hN' hb),
    exact ⟨b, hb, rfl⟩, },
end

/- `in_out` is just another way to quantify exceptions, focusing on a slightly different litter.
Basically `in_out` looks only at images not preimages. -/
lemma is_exception_of_in_out {π : near_litter_perm} {a : atom} {L : litter} :
  in_out π a L → π.is_exception a ∨ π.is_exception (π • a) :=
begin
  rintro (⟨rfl, ha⟩ | ha),
  { refine or.inr (or.inr _),
    intro h,
    rw [mem_litter_set, eq_inv_smul_iff] at h,
    rw [← h, inv_smul_smul] at ha,
    exact ha rfl, },
  { refine or.inl (or.inl _),
    rw [mem_litter_set, ha.1, smul_left_cancel_iff],
    exact ne.symm ha.2, },
end

structure biexact {β : Iio α} (π π' : struct_perm β) (c : support_condition β) : Prop :=
(smul_eq_smul_atom : ∀ A : extended_index β, ∀ a : atom,
  (inl a, A) ≤[α] c →
  struct_perm.derivative A π • a = struct_perm.derivative A π' • a)
(smul_eq_smul_litter : ∀ A : extended_index β, ∀ L : litter,
  (inr L.to_near_litter, A) ≤[α] c → flexible α L A →
  struct_perm.derivative A π • L = struct_perm.derivative A π' • L)
(exact : ∀ A : extended_index β, ∀ L : litter,
  (inr L.to_near_litter, A) ≤[α] c →
  struct_perm.derivative A π • L = struct_perm.derivative A π' • L →
  struct_perm.derivative A π • L.to_near_litter = struct_perm.derivative A π' • L.to_near_litter)

lemma biexact.atoms {β : Iio α} {π π' : struct_perm β} {c : support_condition β}
  (h : biexact π π' c) (A : extended_index β) :
  near_litter_perm.biexact
    (struct_perm.of_bot $ struct_perm.derivative A π)
    (struct_perm.of_bot $ struct_perm.derivative A π')
    {a | (inl a, A) ≤[α] c}
    ∅ :=
near_litter_perm.biexact.atoms _ (h.smul_eq_smul_atom A)

lemma biexact.constrains {β : Iio α} {π π' : struct_perm β} {c d : support_condition β}
  (h : biexact π π' c) (h' : d ≤[α] c) : biexact π π' d :=
⟨
  λ A a ha, h.smul_eq_smul_atom A a (ha.trans h'),
  λ A L hL, h.smul_eq_smul_litter A L (hL.trans h'),
  λ A L hL, h.exact A L (hL.trans h'),
⟩

lemma biexact.smul_eq_smul {β : Iio α} {π π' : allowable β} {c : support_condition β}
  (h : biexact π.to_struct_perm π'.to_struct_perm c) : π • c = π' • c :=
begin
  revert h,
  refine well_founded.induction (constrains_wf α β) c _,
  clear c,
  intros c ih h,
  obtain ⟨a | N, A⟩ := c;
  refine prod.ext _ rfl,
  { change inl _ = inl _,
    simp only,
    exact h.smul_eq_smul_atom A a relation.refl_trans_gen.refl, },
  change inr _ = inr _,
  simp only,
  by_cases hL : N.is_litter,
  swap,
  { have := ih _ (constrains.near_litter N (near_litter.not_is_litter hL) A)
      (h.constrains (refl_trans_gen_near_litter relation.refl_trans_gen.refl)),
    change (inr _, _) = (inr _, _) at this,
    simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
    refine set_like.coe_injective _,
    refine (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _,
    refine eq.trans _ (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).symm,
    refine congr_arg2 _ (congr_arg set_like.coe this) _,
    ext a : 1,
    split,
    { rintro ⟨b, hb, rfl⟩,
      have : (inl _, _) = (inl _, _) := ih _ (constrains.symm_diff N b hb A)
        (h.constrains (relation.refl_trans_gen.single $ constrains.symm_diff N b hb A)),
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
      exact ⟨b, hb, this.symm⟩, },
    { rintro ⟨b, hb, rfl⟩,
      have : (inl _, _) = (inl _, _) := ih _ (constrains.symm_diff N b hb A)
        (h.constrains (relation.refl_trans_gen.single $ constrains.symm_diff N b hb A)),
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
      exact ⟨b, hb, this⟩, }, },
  obtain ⟨L, rfl⟩ := hL.exists_litter_eq,
  suffices : struct_perm.derivative A π.to_struct_perm • L =
    struct_perm.derivative A π'.to_struct_perm • L,
  { exact h.exact _ _ relation.refl_trans_gen.refl this, },
  obtain (hL | hL) := flexible_cases α L A,
  swap,
  { exact h.smul_eq_smul_litter A L relation.refl_trans_gen.refl hL, },
  induction hL with γ δ ε hδ hε hδε B t γ ε hε B a,
  { rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine (to_struct_perm_smul_f_map
      (γ : Iic_index α) δ ε (coe_lt hδ) (coe_lt hε) (Iio.coe_injective.ne hδε) _ _).trans _,
    rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine eq.trans _ (to_struct_perm_smul_f_map
      (γ : Iic_index α) δ ε (coe_lt hδ) (coe_lt hε) (Iio.coe_injective.ne hδε) _ _).symm,
    refine congr_arg _ _,
    rw [← inv_smul_eq_iff, smul_smul],
    refine (designated_support t).supports _ _,
    intros c hc,
    rw [mul_smul, inv_smul_eq_iff],
    rw [← allowable.to_struct_perm_smul, ← allowable.to_struct_perm_smul,
      ← allowable.derivative_cons_apply, ← allowable.derivative_cons_apply,
      ← allowable.derivative_to_struct_perm, ← allowable.derivative_to_struct_perm],
    have := ih (c.fst, (B.cons $ coe_lt hδ).comp c.snd) _ _,
    { refine prod.ext _ rfl,
      apply_fun prod.fst at this,
      change _ • _ = _ • _,
      rw [struct_perm.derivative_derivative, struct_perm.derivative_derivative],
      exact this, },
    { exact constrains.f_map _ _ _ _ _ _ hc, },
    { refine h.constrains (relation.refl_trans_gen.single _),
      exact constrains.f_map _ _ _ _ _ _ hc, }, },
  { rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine (to_struct_perm_smul_f_map
      (γ : Iic_index α) ⊥ ε (bot_lt_coe _) (coe_lt hε) Iio_index.bot_ne_coe _ _).trans _,
    rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine eq.trans _ (to_struct_perm_smul_f_map
      (γ : Iic_index α) ⊥ ε (bot_lt_coe _) (coe_lt hε) Iio_index.bot_ne_coe _ _).symm,
    refine congr_arg _ _,
    rw [← allowable.derivative_cons_apply, ← allowable.derivative_cons_apply],
    have := ih (inl a, B.cons $ bot_lt_coe _) _ _,
    { change (inl _, _) = (inl _, _) at this,
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
      rw allowable.derivative_to_struct_perm
        (show path (β : type_index) (⊥ : Iic_index α), from _) at this,
      rw allowable.derivative_to_struct_perm
        (show path (β : type_index) (⊥ : Iic_index α), from _) at this,
      rw allowable.to_struct_perm_smul at this,
      rw allowable.to_struct_perm_smul at this,
      dsimp only,
      convert this using 2;
      { rw to_struct_perm_to_near_litter_perm, refl, }, },
    { exact constrains.f_map_bot _ _ _, },
    { refine h.constrains (relation.refl_trans_gen.single _),
      exact constrains.f_map_bot _ _ _, }, },
end

lemma biexact.smul_eq_smul_near_litter {β : Iio α}
  {π π' : allowable β} {A : extended_index β} {N : near_litter}
  (h : biexact π.to_struct_perm π'.to_struct_perm (inr N, A)) :
  struct_perm.derivative A π.to_struct_perm • N = struct_perm.derivative A π'.to_struct_perm • N :=
begin
  have : (inr _, _) = (inr _, _) := h.smul_eq_smul,
  rw prod.mk.inj_iff at this,
  exact inr_injective this.1,
end

lemma mem_dom_of_exactly_approximates {β : Iio α} {π₀ : struct_approx β}
  {π : struct_perm β} (hπ : π₀.exactly_approximates π)
  {A : extended_index β} {a : atom} {L : litter}
  (h : in_out (struct_perm.of_bot $ struct_perm.derivative A π) a L) :
  a ∈ (π₀ A).atom_perm.domain :=
begin
  obtain (h | h) := is_exception_of_in_out h,
  { exact (hπ A).exception_mem _ h, },
  { have h₁ := (hπ A).exception_mem _ h,
    have := (hπ A).symm_map_atom _ h₁,
    rw inv_smul_smul at this,
    rw ← this,
    exact (π₀ A).atom_perm.symm.map_domain h₁, },
end

/--
We can prove that `map_flexible` holds at any `constrained_action` without any `lawful` hypothesis.
-/
lemma constrained_action_comp_map_flexible (hπf : π.free) {γ : Iio α}
  {s : set (support_condition β)} {hs : small s}
  (A : path (β : type_index) γ) :
  ((constrained_action π s hs).comp A).map_flexible :=
begin
  rintros L B ⟨c, hc, hL₁⟩ hL₂,
  simp only [struct_action.comp_apply, constrained_action_litter_map,
    foa_hypothesis_near_litter_image],
  rw complete_near_litter_map_fst_eq,
  obtain (hL₃ | (⟨⟨hL₃⟩⟩ | ⟨⟨hL₃⟩⟩)) := flexible_cases' _ L (A.comp B),
  { rw complete_litter_map_eq_of_flexible hL₃,
    refine near_litter_approx.flexible_completion_smul_flexible _ _ _ _ _ hL₂,
    intros L' hL',
    exact flexible_of_comp_flexible (hπf (A.comp B) L' hL'), },
  { rw complete_litter_map_eq_of_inflexible_bot hL₃,
    obtain ⟨δ, ε, hε, C, a, rfl, hC⟩ := hL₃,
    contrapose hL₂,
    rw not_flexible_iff at hL₂ ⊢,
    rw inflexible_iff at hL₂,
    obtain (⟨δ', ε', ζ', hε', hζ', hεζ', C', t', h', rfl⟩ | ⟨δ', ε', hε', C', a', h', rfl⟩) := hL₂,
    { have := congr_arg litter.β h',
      simpa only [f_map_β, bot_ne_coe] using this, },
    { rw [path.comp_cons, path.comp_cons] at hC,
      cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hC)),
      exact inflexible.mk_bot _ _ _, }, },
  { rw complete_litter_map_eq_of_inflexible_coe' hL₃,
    split_ifs,
    swap,
    { exact hL₂, },
    obtain ⟨δ, ε, ζ, hε, hζ, hεζ, C, t, rfl, hC⟩ := hL₃,
    contrapose hL₂,
    rw not_flexible_iff at hL₂ ⊢,
    rw inflexible_iff at hL₂,
    obtain (⟨δ', ε', ζ', hε', hζ', hεζ', C', t', h', rfl⟩ | ⟨δ', ε', hε', C', a', h', rfl⟩) := hL₂,
    { rw [path.comp_cons, path.comp_cons] at hC,
      cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hC)),
      have hC := (path.heq_of_cons_eq_cons hC).eq,
      cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hC)),
      refine inflexible.mk_coe hε _ _ _ _, },
    { have := congr_arg litter.β h',
      simpa only [f_map_β, bot_ne_coe] using this, }, },
end

lemma ih_action_comp_map_flexible (hπf : π.free) {γ : Iio α} (c : support_condition β)
  (A : path (β : type_index) γ) :
  ((ih_action (π.foa_hypothesis : hypothesis c)).comp A).map_flexible :=
begin
  rw ih_action_eq_constrained_action,
  exact constrained_action_comp_map_flexible hπf A,
end

lemma ihs_action_comp_map_flexible (hπf : π.free) {γ : Iio α} (c d : support_condition β)
  (A : path (β : type_index) γ) :
  ((ihs_action π c d).comp A).map_flexible :=
begin
  rw ihs_action_eq_constrained_action,
  exact constrained_action_comp_map_flexible hπf A,
end

lemma complete_litter_map_flexible (hπf : π.free) {A : extended_index β} {L : litter}
  (h : flexible α L A) :
  flexible α (π.complete_litter_map A L) A :=
begin
  rw complete_litter_map_eq_of_flexible h,
  exact near_litter_approx.flexible_completion_smul_flexible _ _ _ (hπf A) _ h,
end

noncomputable lemma complete_litter_map_inflexible_bot {A : extended_index β} {L : litter}
  (h : inflexible_bot L A) : inflexible_bot (π.complete_litter_map A L) A :=
begin
  rw complete_litter_map_eq_of_inflexible_bot h,
  obtain ⟨γ, ε, hγε, B, a, rfl, rfl⟩ := h,
  exact ⟨_, _, _, _, _, rfl, rfl⟩,
end

noncomputable lemma complete_litter_map_inflexible_coe (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful) {A : extended_index β} {L : litter} (h : inflexible_coe L A)
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  inflexible_coe (π.complete_litter_map A L) A :=
begin
  rw complete_litter_map_eq_of_inflexible_coe h,
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B, a, rfl, rfl⟩ := h,
  exact ⟨_, _, _, hδ, hε, hδε, _, _, rfl, rfl⟩,
  { refine (hcd.le _).comp _,
    cases hL,
    { exact (ih_action_le hL).trans (ih_action_le_ihs_action _ _ _), },
    { rw ihs_action_symm,
      exact (ih_action_le hL).trans (ih_action_le_ihs_action _ _ _), }, },
  { exact ih_action_comp_map_flexible hπf _ _, },
end

lemma complete_litter_map_flexible' (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful) {A : extended_index β} {L : litter}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : flexible α (π.complete_litter_map A L) A) : flexible α L A :=
begin
  obtain (h' | h' | h') := flexible_cases' β L A,
  { exact h', },
  { have := complete_litter_map_inflexible_bot h'.some,
    rw flexible_iff_not_inflexible_bot_coe at h,
    cases h.1.false this, },
  { have := complete_litter_map_inflexible_coe hπf hcd h'.some hL,
    rw flexible_iff_not_inflexible_bot_coe at h,
    cases h.2.false this, },
end

lemma complete_litter_map_flexible_iff (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful) {A : extended_index β} {L : litter}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  flexible α (π.complete_litter_map A L) A ↔ flexible α L A :=
⟨complete_litter_map_flexible' hπf hcd hL, complete_litter_map_flexible hπf⟩

noncomputable lemma complete_litter_map_inflexible_bot' (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful) {A : extended_index β} {L : litter}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : inflexible_bot (π.complete_litter_map A L) A) : inflexible_bot L A :=
begin
  refine nonempty.some _,
  obtain (h' | h' | h') := flexible_cases' β L A,
  { have := complete_litter_map_flexible hπf h',
    rw flexible_iff_not_inflexible_bot_coe at this,
    cases this.1.false h, },
  { exact h', },
  { have := complete_litter_map_inflexible_coe hπf hcd h'.some hL,
    cases inflexible_bot_inflexible_coe h this, },
end

lemma complete_litter_map_inflexible_bot_iff (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful) {A : extended_index β} {L : litter}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  nonempty (inflexible_bot (π.complete_litter_map A L) A) ↔ nonempty (inflexible_bot L A) :=
⟨
  λ ⟨h⟩, ⟨complete_litter_map_inflexible_bot' hπf hcd hL h⟩,
  λ ⟨h⟩, ⟨complete_litter_map_inflexible_bot h⟩,
⟩

noncomputable lemma complete_litter_map_inflexible_coe' (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful) {A : extended_index β} {L : litter}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : inflexible_coe (π.complete_litter_map A L) A) : inflexible_coe L A :=
begin
  refine nonempty.some _,
  obtain (h' | h' | h') := flexible_cases' β L A,
  { have := complete_litter_map_flexible hπf h',
    rw flexible_iff_not_inflexible_bot_coe at this,
    cases this.2.false h, },
  { have := complete_litter_map_inflexible_bot h'.some,
    cases inflexible_bot_inflexible_coe this h, },
  { exact h', },
end

lemma complete_litter_map_inflexible_coe_iff (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful) {A : extended_index β} {L : litter}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  nonempty (inflexible_coe (π.complete_litter_map A L) A) ↔ nonempty (inflexible_coe L A) :=
⟨
  λ ⟨h⟩, ⟨complete_litter_map_inflexible_coe' hπf hcd hL h⟩,
  λ ⟨h⟩, ⟨complete_litter_map_inflexible_coe hπf hcd h hL⟩,
⟩

lemma constrained_action_coherent_precise' (hπf : π.free) {γ : Iio α} (A : path (β : type_index) γ)
  (N : extended_index γ × near_litter)
  (s : set (support_condition β)) (hs : small s)
  (hc : ∃ c : support_condition β, c ∈ s ∧ (inr N.2, A.comp N.1) ≤[α] c)
  (hπ : ((constrained_action π s hs).comp A).lawful)
  (ρ : allowable γ)
  (h : (((constrained_action π s hs).comp A).rc hπ).exactly_approximates ρ.to_struct_perm) :
  complete_near_litter_map π (A.comp N.1) N.2 = struct_perm.derivative N.1 ρ.to_struct_perm • N.2 :=
begin
  revert hc,
  refine well_founded.induction
    (inv_image.wf _ (relation.trans_gen.is_well_founded (constrains α γ)).wf) N _,
  exact λ N : extended_index γ × near_litter, (inr N.2, N.1),
  clear N,
  rintros ⟨B, N⟩ ih ⟨c, hc₁, hc₂⟩,
  dsimp only at *,
  have hdom : ((((constrained_action π s hs).comp A B).refine (hπ B)).litter_map N.fst).dom :=
    ⟨c, hc₁, refl_trans_gen_near_litter hc₂⟩,
  suffices : complete_litter_map π (A.comp B) N.fst =
    struct_perm.derivative B ρ.to_struct_perm • N.fst,
  { refine set_like.coe_injective _,
    refine eq.trans _ (near_litter_action.smul_near_litter_eq_of_precise_at
      _ (h B) hdom (near_litter_action.refine_precise _) this.symm).symm,
    rw complete_near_litter_map_eq' (A.comp B) N,
    simp only [struct_action.refine_apply, struct_action.refine_litter_map,
      foa_hypothesis_near_litter_image, struct_perm.of_bot_smul],
    simp only [struct_action.comp_apply, constrained_action_litter_map, symm_diff_right_inj],
    ext a : 1,
    split,
    { rintro ⟨a, ha, rfl⟩,
      refine ⟨a, ha, _⟩,
      refine ((h B).map_atom a _).symm.trans _,
      { refine (or.inl (or.inl (or.inl (or.inl _)))),
        exact ⟨c, hc₁, relation.refl_trans_gen.head (constrains.symm_diff N a ha _) hc₂⟩, },
      { rw struct_action.rc_smul_atom_eq,
        refl,
        exact ⟨c, hc₁, relation.refl_trans_gen.head (constrains.symm_diff N a ha _) hc₂⟩, }, },
    { rintro ⟨a, ha, rfl⟩,
      refine ⟨a, ha, _⟩,
      refine eq.trans _ ((h B).map_atom a _),
      { rw struct_action.rc_smul_atom_eq,
        refl,
        exact ⟨c, hc₁, relation.refl_trans_gen.head (constrains.symm_diff N a ha _) hc₂⟩, },
      { refine (or.inl (or.inl (or.inl (or.inl _)))),
        exact ⟨c, hc₁, relation.refl_trans_gen.head (constrains.symm_diff N a ha _) hc₂⟩, }, }, },
  have hc₂' := refl_trans_gen_near_litter hc₂,
  generalize hNL : N.fst = L,
  rw hNL at hdom hc₂',
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' (γ : Iic α) L B,
  { refine eq.trans _ ((h B).map_litter L _),
    { rw struct_action.rc_smul_litter_eq,
      rw near_litter_action.flexible_litter_perm_apply_eq,
      swap, exact hdom,
      swap, exact hL,
      exact (near_litter_action.rough_litter_map_or_else_of_dom _ hdom).symm, },
    { refine or.inl (or.inl _),
      refine ⟨hdom, hL⟩, }, },
  { rw complete_litter_map_eq_of_inflexible_bot (hL.comp A),
    obtain ⟨δ, ε, hε, C, a, rfl, rfl⟩ := hL,
    rw struct_perm.derivative_cons,
    refine eq.trans _ (struct_perm.derivative_bot_smul _ _).symm,
    rw struct_perm.derivative_cons,
    rw allowable.derivative_to_struct_perm (show path (γ : type_index) (δ : Iic_index α), from C),
    refine eq.trans _ (to_struct_perm_smul_f_map (δ : Iic_index α) ⊥ ε (bot_lt_coe _) _ _
      (allowable.derivative (show path (γ : type_index) (δ : Iic_index α), from _) ρ) a).symm,
    { intro h, cases h, },
    refine congr_arg _ _,
    rw ← allowable.derivative_cons_apply,
    refine eq.trans _ (((h $ C.cons (bot_lt_coe _)).map_atom a
      (or.inl (or.inl (or.inl (or.inl
        ⟨c, hc₁, relation.refl_trans_gen.head (constrains.f_map_bot hε _ _) hc₂'⟩))))).trans _),
    { rw struct_action.rc_smul_atom_eq,
      refl,
      exact ⟨c, hc₁, relation.refl_trans_gen.head (constrains.f_map_bot hε _ _) hc₂'⟩, },
    { have := allowable.to_struct_perm_smul
        (allowable.derivative (show path (γ : type_index) (⊥ : Iic_index α),
          from C.cons (bot_lt_coe _)) ρ) a,
      rw ← allowable.derivative_to_struct_perm at this,
      refine this.trans _,
      congr,
      ext π a : 4,
      change π.to_struct_perm.to_near_litter_perm.atom_perm a = π.atom_perm a,
      rw to_struct_perm_to_near_litter_perm, }, },
  { rw complete_litter_map_eq_of_inflexible_coe (hL.comp A),
    swap,
    { rw [inflexible_coe.comp_B, ← path.comp_cons, ← struct_action.comp_comp],
      refine struct_action.lawful.comp _ _,
      refine hπ.le (struct_action.le_comp (ih_action_le_constrained_action _ _) _),
      exact ⟨c, hc₁, hc₂'⟩, },
    swap,
    { rw [inflexible_coe.comp_B, ← path.comp_cons],
      exact ih_action_comp_map_flexible hπf _ _, },
    obtain ⟨δ, ε, ζ, hε, hζ, hεζ, C, t, rfl, rfl⟩ := hL,
    rw struct_perm.derivative_cons,
    refine eq.trans _ (struct_perm.derivative_bot_smul _ _).symm,
    rw struct_perm.derivative_cons,
    rw allowable.derivative_to_struct_perm (show path (γ : type_index) (δ : Iic_index α), from C),
    refine eq.trans _ (to_struct_perm_smul_f_map (δ : Iic_index α) ε ζ (coe_lt hε) _ _
      (allowable.derivative (show path (γ : type_index) (δ : Iic_index α), from C) ρ) t).symm,
    { intro h,
      refine hεζ (subtype.ext _),
      have := congr_arg subtype.val h,
      exact coe_injective this, },
    refine congr_arg _ _,
    rw [← allowable.derivative_cons_apply, ← inv_smul_eq_iff, smul_smul],
    refine (designated_support t).supports _ _,
    intros c hct,
    rw [mul_smul, inv_smul_eq_iff],
    obtain ⟨a | M, D⟩ := c,
    { refine prod.ext _ rfl,
      change inl _ = inl _,
      simp only,
      rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative],
      refine eq.trans _ ((h _).map_atom a _),
      refine (((ih_action _ ).hypothesised_allowable_exactly_approximates
        ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ D).map_atom a _).symm.trans _,
      { refine or.inl (or.inl (or.inl (or.inl _))),
        exact relation.trans_gen.single (constrains.f_map _ _ _ _ _ _ hct), },
      { rw [struct_action.rc_smul_atom_eq, struct_action.rc_smul_atom_eq],
        { simp only [struct_action.comp_apply, ih_action_atom_map, foa_hypothesis_atom_image,
            constrained_action_atom_map],
          simp_rw ← path.comp_cons,
          rw path.comp_assoc, },
        { refine ⟨c, hc₁, relation.refl_trans_gen.head _ hc₂'⟩,
          exact constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A, },
        { simp only [struct_action.comp_apply, ih_action_atom_map],
          simp_rw ← path.comp_cons,
          rw path.comp_assoc,
          exact relation.trans_gen.single
            (constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A), }, },
      { refine or.inl (or.inl (or.inl (or.inl _))),
        refine ⟨c, hc₁, relation.refl_trans_gen.head _ hc₂'⟩,
        exact constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A, }, },
    { refine prod.ext _ rfl,
      change inr _ = inr _,
      simp only,
      refine biexact.smul_eq_smul_near_litter _,
      split,
      { intros E a ha,
        have haN : (inl a, (C.cons $ coe_lt hε).comp E) <[α]
          (inr N.fst.to_near_litter, (C.cons $ coe_lt hζ).cons (bot_lt_coe _)),
        { simp only [hNL],
          refine relation.trans_gen.tail' _ (constrains.f_map hε _ _ _ _ _ hct),
          exact refl_trans_gen_constrains_comp ha _, },
        refine ((struct_action.hypothesised_allowable_exactly_approximates
          _ ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _).map_atom _ _).symm.trans _,
        { refine or.inl (or.inl (or.inl (or.inl _))),
          change _ <[α] _,
          simp only [← hNL, path.comp_assoc, ← path.comp_cons],
          exact trans_gen_constrains_comp haN _, },
        have := (h _).map_atom a _,
        rw struct_action.rc_smul_atom_eq at this ⊢,
        swap,
        { change _ <[α] _,
          simp only [← hNL, path.comp_assoc, ← path.comp_cons],
          exact trans_gen_constrains_comp haN _, },
        swap,
        { refine ⟨c, hc₁, trans _ hc₂⟩,
          swap,
          refine relation.refl_trans_gen.trans (trans_gen_constrains_comp haN _).to_refl _,
          exact refl_trans_gen_near_litter relation.refl_trans_gen.refl, },
        { simp only [struct_action.comp_apply, ih_action_atom_map, foa_hypothesis_atom_image,
            constrained_action_atom_map, struct_perm.of_bot_smul] at this ⊢,
          rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative, ← this,
            ← path.comp_assoc, path.comp_cons], },
        { refine or.inl (or.inl (or.inl (or.inl _))),
          refine ⟨c, hc₁, trans _ hc₂⟩,
          simp only [← hNL, path.comp_assoc, ← path.comp_cons],
          exact refl_trans_gen_constrains_comp (trans_gen_near_litter haN).to_refl _, }, },
      { intros E L hL₁ hL₂,
        rw ← struct_perm.of_bot_smul,
        refine ((struct_action.hypothesised_allowable_exactly_approximates
          _ ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _).map_litter _ _).symm.trans _,
        { refine or.inl (or.inl ⟨_, hL₂⟩),
          refine relation.trans_gen.trans_right (refl_trans_gen_constrains_comp hL₁ _) _,
          exact relation.trans_gen.single (constrains.f_map _ _ _ _ _ _ hct), },
        have hLN : (inr L.to_near_litter, (C.cons $ coe_lt hε).comp E) <[α]
          (inr N.fst.to_near_litter, (C.cons $ coe_lt hζ).cons (bot_lt_coe _)),
        { simp only [hNL],
          refine relation.trans_gen.tail' _ (constrains.f_map hε _ _ _ _ _ hct),
          exact refl_trans_gen_constrains_comp hL₁ _, },
        rw [struct_action.rc_smul_litter_eq, near_litter_action.flexible_litter_perm_apply_eq,
          near_litter_action.rough_litter_map_or_else_of_dom],
        simp only [struct_action.comp_apply, struct_action.refine_apply,
          near_litter_action.refine_litter_map, ih_action_litter_map,
          foa_hypothesis_near_litter_image],
        specialize ih ((C.cons $ coe_lt hε).comp E, L.to_near_litter) (trans_gen_near_litter hLN)
          ⟨c, hc₁, trans (trans_gen_constrains_comp (trans_gen_near_litter hLN) _).to_refl hc₂⟩,
        { dsimp only at ih,
          rw [← path.comp_assoc, path.comp_cons] at ih,
          rw ih,
          simp only [struct_perm.derivative_fst, litter.to_near_litter_fst],
          rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative], },
        { refine trans_gen_near_litter _,
          simp only [← hNL, path.comp_assoc, ← path.comp_cons],
          exact trans_gen_constrains_comp hLN _, },
        { refine trans_gen_near_litter _,
          simp only [← hNL, path.comp_assoc, ← path.comp_cons],
          exact trans_gen_constrains_comp hLN _, },
        { exact hL₂, }, },
      { intros E L hL₁ hL₂,
        have hLN : (inr L.to_near_litter, (C.cons $ coe_lt hε).comp E) <[α]
          (inr N.fst.to_near_litter, (C.cons $ coe_lt hζ).cons (bot_lt_coe _)),
        { simp only [hNL],
          refine relation.trans_gen.tail' _ (constrains.f_map hε _ _ _ _ _ hct),
          exact refl_trans_gen_constrains_comp hL₁ _, },
        specialize ih (((C.cons $ coe_lt hε).comp E), L.to_near_litter)
          (trans_gen_near_litter hLN)
          ⟨c, hc₁, trans (trans_gen_constrains_comp (trans_gen_near_litter hLN) _).to_refl hc₂⟩,
        simp only at ih,
        rw [← path.comp_assoc, path.comp_cons] at ih,
        refine (near_litter_action.smul_to_near_litter_eq_of_precise_at _
          (struct_action.hypothesised_allowable_exactly_approximates
            (ih_action _) ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _)
          _ (near_litter_action.refine_precise _) _).trans _,
        { refine relation.trans_gen.tail' (refl_trans_gen_constrains_comp hL₁ _) _,
          exact constrains.f_map _ _ _ _ _ _ hct, },
        { refine hL₂.trans _,
          simp only [struct_action.comp_apply, struct_action.refine_apply,
            near_litter_action.refine_litter_map, ih_action_litter_map,
            foa_hypothesis_near_litter_image],
          rw [ih, ← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative],
          refl, },
        { simp only [struct_action.comp_apply, struct_action.refine_apply,
            near_litter_action.refine_litter_map, ih_action_litter_map,
            foa_hypothesis_near_litter_image],
          rw [ih, ← allowable.derivative_to_struct_perm,
            struct_perm.derivative_derivative], }, }, }, },
end

/--
**Coherence lemma**: The action of the complete litter map, below a given support condition `c`,
is equal to the action of any allowable permutation that exactly approximates it.
This condition can only be applied for `γ < α` as we're dealing with lower allowable permutations.
-/
lemma constrained_action_coherent_precise (hπf : π.free) {γ : Iio α} (A : path (β : type_index) γ)
  (B : extended_index γ) (N : near_litter)
  (s : set (support_condition β)) (hs : small s)
  (hc : ∃ c : support_condition β, c ∈ s ∧ (inr N, A.comp B) ≤[α] c)
  (hπ : ((constrained_action π s hs).comp A).lawful)
  (ρ : allowable γ)
  (h : (((constrained_action π s hs).comp A).rc hπ).exactly_approximates ρ.to_struct_perm) :
  complete_near_litter_map π (A.comp B) N = struct_perm.derivative B ρ.to_struct_perm • N :=
constrained_action_coherent_precise' hπf A (B, N) s hs hc hπ ρ h

/--
The coherence lemma for atoms, which is much easier to prove.
The statement is here for symmetry.
-/
lemma constrained_action_coherent_precise_atom (hπf : π.free) {γ : Iio α}
  (A : path (β : type_index) γ)
  (B : extended_index γ) (a : atom)
  (s : set (support_condition β)) (hs : small s)
  (hc : ∃ c : support_condition β, c ∈ s ∧ (inl a, A.comp B) ≤[α] c)
  (hπ : ((constrained_action π s hs).comp A).lawful)
  (ρ : allowable γ)
  (h : (((constrained_action π s hs).comp A).rc hπ).exactly_approximates ρ.to_struct_perm) :
  complete_atom_map π (A.comp B) a = struct_perm.derivative B ρ.to_struct_perm • a :=
begin
  refine eq.trans _ ((h B).map_atom a (or.inl (or.inl (or.inl (or.inl hc))))),
  rw struct_action.rc_smul_atom_eq,
  refl,
  exact hc,
end

lemma ihs_action_coherent_precise (hπf : π.free) {γ : Iio α} (A : path (β : type_index) γ)
  (B : extended_index γ) (N : near_litter)
  (c d : support_condition β) (hc : (inr N, A.comp B) ∈ trans_constrained c d)
  (hπ : ((ihs_action π c d).comp A).lawful)
  (ρ : allowable γ)
  (h : (((ihs_action π c d).comp A).rc hπ).exactly_approximates ρ.to_struct_perm) :
  complete_near_litter_map π (A.comp B) N = struct_perm.derivative B ρ.to_struct_perm • N :=
begin
  simp_rw ihs_action_eq_constrained_action at hπ h,
  refine constrained_action_coherent_precise hπf A B N _ _ _ hπ ρ h,
  cases hc,
  { simp only [relation.trans_gen.tail'_iff, mem_set_of_eq] at hc,
    obtain ⟨d, hd₁, hd₂⟩ := hc,
    exact ⟨d, or.inl hd₂, hd₁⟩, },
  { simp only [relation.trans_gen.tail'_iff, mem_set_of_eq] at hc,
    obtain ⟨d, hd₁, hd₂⟩ := hc,
    exact ⟨d, or.inr hd₂, hd₁⟩, },
end

lemma ihs_action_coherent_precise_atom (hπf : π.free) {γ : Iio α} (A : path (β : type_index) γ)
  (B : extended_index γ) (a : atom)
  (c d : support_condition β) (hc : (inl a, A.comp B) <[α] c)
  (hπ : ((ihs_action π c d).comp A).lawful)
  (ρ : allowable γ)
  (h : (((ihs_action π c d).comp A).rc hπ).exactly_approximates ρ.to_struct_perm) :
  complete_atom_map π (A.comp B) a = struct_perm.derivative B ρ.to_struct_perm • a :=
begin
  refine eq.trans _ ((h B).map_atom a (or.inl (or.inl (or.inl (or.inl (or.inl hc)))))),
  rw struct_action.rc_smul_atom_eq,
  refl,
  exact (or.inl hc),
end

lemma ih_action_coherent_precise (hπf : π.free) {γ : Iio α} (A : path (β : type_index) γ)
  (B : extended_index γ) (N : near_litter)
  (c : support_condition β) (hc : (inr N, A.comp B) <[α] c)
  (hπ : ((ih_action (π.foa_hypothesis : hypothesis c)).comp A).lawful)
  (ρ : allowable γ)
  (h : (((ih_action (π.foa_hypothesis : hypothesis c)).comp A).rc hπ).exactly_approximates
    ρ.to_struct_perm) :
  complete_near_litter_map π (A.comp B) N = struct_perm.derivative B ρ.to_struct_perm • N :=
begin
  refine ihs_action_coherent_precise hπf A B N c c (or.inl hc) _ ρ _,
  { rw ihs_action_self,
    exact hπ, },
  { simp_rw ihs_action_self,
    exact h, },
end

lemma ih_action_coherent_precise_atom (hπf : π.free) {γ : Iio α}
  (A : path (β : type_index) γ)
  (B : extended_index γ) (a : atom)
  (c : support_condition β) (hc : (inl a, A.comp B) <[α] c)
  (hπ : ((ih_action (π.foa_hypothesis : hypothesis c)).comp A).lawful)
  (ρ : allowable γ)
  (h : (((ih_action (π.foa_hypothesis : hypothesis c)).comp A).rc hπ).exactly_approximates
    ρ.to_struct_perm) :
  complete_atom_map π (A.comp B) a = struct_perm.derivative B ρ.to_struct_perm • a :=
begin
  refine ihs_action_coherent_precise_atom hπf A B a c c hc _ ρ _,
  { rw ihs_action_self,
    exact hπ, },
  { simp_rw ihs_action_self,
    exact h, },
end

lemma ih_action_smul_tangle' (hπf : π.free) (c d : support_condition β)
  (A : extended_index β) (L : litter)
  (hL₁ : (inr L.to_near_litter, A) ≤[α] c)
  (hL₂ : inflexible_coe L A)
  (hlaw₁ hlaw₂) :
  (ih_action (π.foa_hypothesis : hypothesis (inr L.to_near_litter, A))).hypothesised_allowable
    hL₂ hlaw₁ (ih_action_comp_map_flexible hπf _ _) • hL₂.t =
  (ihs_action π c d).hypothesised_allowable
    hL₂ hlaw₂ (ihs_action_comp_map_flexible hπf _ _ _) • hL₂.t :=
begin
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := hL₂,
  rw [← inv_smul_eq_iff, smul_smul],
  refine (designated_support t).supports _ _,
  intros e he,
  rw [mul_smul, inv_smul_eq_iff],
  obtain ⟨a | N, C⟩ := e,
  { refine prod.ext _ rfl,
    change inl _ = inl _,
    simp only,
    refine eq.trans _ (ihs_action_coherent_precise_atom hπf _ _ a c d _ hlaw₂ _
      ((ihs_action π c d).hypothesised_allowable_exactly_approximates _ _ _)),
    simp_rw ← ihs_action_self,
    refine (ihs_action_coherent_precise_atom hπf _ _ a _ _ _ _ _
      ((ihs_action π _ _).hypothesised_allowable_exactly_approximates
        ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ _ _)).symm,
    { exact relation.trans_gen.single (constrains.f_map _ _ _ _ _ _ he), },
    { exact relation.trans_gen.head' (constrains.f_map hδ _ _ _ _ _ he) hL₁, }, },
  { refine prod.ext _ rfl,
    change inr _ = inr _,
    simp only,
    refine eq.trans _ (ihs_action_coherent_precise hπf _ _ N c d _ hlaw₂ _
      ((ihs_action π c d).hypothesised_allowable_exactly_approximates _ _ _)),
    simp_rw ← ihs_action_self,
    refine (ihs_action_coherent_precise hπf _ _ N _ _ _ _ _
      ((ihs_action π _ _).hypothesised_allowable_exactly_approximates
        ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ _ _)).symm,
    { exact or.inl (relation.trans_gen.single (constrains.f_map _ _ _ _ _ _ he)), },
    { exact or.inl (relation.trans_gen.head' (constrains.f_map hδ _ _ _ _ _ he) hL₁), }, },
end

lemma ih_action_smul_tangle (hπf : π.free) (c d : support_condition β)
  (A : extended_index β) (L : litter)
  (hL₁ : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d)
  (hL₂ : inflexible_coe L A)
  (hlaw₁ hlaw₂) :
  (ih_action (π.foa_hypothesis : hypothesis (inr L.to_near_litter, A))).hypothesised_allowable
    hL₂ hlaw₁ (ih_action_comp_map_flexible hπf _ _) • hL₂.t =
  (ihs_action π c d).hypothesised_allowable
    hL₂ hlaw₂ (ihs_action_comp_map_flexible hπf _ _ _) • hL₂.t :=
begin
  cases hL₁,
  { exact ih_action_smul_tangle' hπf c d A L hL₁ hL₂ hlaw₁ hlaw₂, },
  { have := ih_action_smul_tangle' hπf d c A L hL₁ hL₂ hlaw₁ _,
    { simp_rw ihs_action_symm at this,
      exact this, },
    { rw ihs_action_symm,
      exact hlaw₂, }, },
end

lemma litter_injective_extends (hπf : π.free) {c d : support_condition β}
  (hcd : (ihs_action π c d).lawful)
  {A : extended_index β} {L₁ L₂ : litter}
  (h₁ : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h₂ : (inr L₂.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : complete_litter_map π A L₁ = complete_litter_map π A L₂) :
  L₁ = L₂ :=
begin
  obtain (h₁' | h₁' | h₁') := flexible_cases' β L₁ A,
  { have h₂' : flexible α L₂ A,
    { have := complete_litter_map_flexible hπf h₁',
      rw h at this,
      exact complete_litter_map_flexible' hπf hcd h₂ this, },
    rw [complete_litter_map_eq_of_flexible h₁',
      complete_litter_map_eq_of_flexible h₂'] at h,
    refine local_perm.inj_on _ _ _ h,
    all_goals {
      rw near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπf A),
      assumption, }, },
  { obtain ⟨h₁'⟩ := h₁',
    have h₂' : inflexible_bot L₂ A,
    { have := complete_litter_map_inflexible_bot h₁',
      rw h at this,
      exact complete_litter_map_inflexible_bot' hπf hcd h₂ this, },
    rw [complete_litter_map_eq_of_inflexible_bot h₁',
      complete_litter_map_eq_of_inflexible_bot h₂'] at h,
    obtain ⟨γ₁, ε₁, hγε₁, B₁, a₁, rfl, rfl⟩ := h₁',
    obtain ⟨γ₂, ε₂, hγε₂, B₂, a₂, rfl, hB⟩ := h₂',
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hB)),
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hB).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).eq).eq,
    refine congr_arg _ ((hcd _).atom_map_injective _ _ (f_map_injective bot_ne_coe h)),
    { have := constrains.f_map_bot hγε₁ B₁ a₁,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h₁
        (relation.trans_gen.single this), },
    { have := constrains.f_map_bot hγε₁ B₁ a₂,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h₂
        (relation.trans_gen.single this), }, },
  { obtain ⟨h₁'⟩ := h₁',
    have h₂' : inflexible_coe L₂ A,
    { have := complete_litter_map_inflexible_coe hπf hcd h₁' h₁,
      rw h at this,
      exact complete_litter_map_inflexible_coe' hπf hcd h₂ this, },
    rw complete_litter_map_eq_of_inflexible_coe h₁' at h,
    swap,
    { refine (hcd.le _).comp _,
      cases h₁,
      { exact (ih_action_le h₁).trans (ih_action_le_ihs_action _ _ _), },
      { rw ihs_action_symm,
        exact (ih_action_le h₁).trans (ih_action_le_ihs_action _ _ _), }, },
    swap,
    { exact ih_action_comp_map_flexible hπf _ _, },
    rw complete_litter_map_eq_of_inflexible_coe h₂' at h,
    swap,
    { refine (hcd.le _).comp _,
      cases h₂,
      { exact (ih_action_le h₂).trans (ih_action_le_ihs_action _ _ _), },
      { rw ihs_action_symm,
        exact (ih_action_le h₂).trans (ih_action_le_ihs_action _ _ _), }, },
    swap,
    { exact ih_action_comp_map_flexible hπf _ _, },
    obtain ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩ := h₁',
    obtain ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, rfl, hB⟩ := h₂',
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hB)),
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hB).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).eq).eq,
    have := congr_arg litter.β h,
    cases subtype.coe_injective (coe_injective this),
    clear this,
    refine congr_arg _ _,
    have h' := f_map_injective _ h,
    rw ih_action_smul_tangle hπf c d _ _ h₁ _ _ (hcd.comp _) at h',
    rw ih_action_smul_tangle hπf c d _ _ h₂ _ _ (hcd.comp _) at h',
    rw struct_action.hypothesised_allowable_eq t₁ t₂ rfl
      (hcd.comp _) (ihs_action_comp_map_flexible hπf _ _ _) at h',
    rw smul_left_cancel_iff at h',
    exact h', },
end

/--
**Split relation**
Let `<` denote a relation on `α`.
The split relation `<ₛ` defined on `α × α` is defined by:

* `a < b → (a, c) <ₛ (b, c)` (left `<`)
* `b < c → (a, b) <ₛ (a, c)` (right `<`)
* `a < c → b < c → (a, b) <ₛ (c, d)` (left split)
* `a < d → b < d → (a, b) <ₛ (c, d)` (right split)

This is more granular than the standard product of relations,
which would be given by just the first two constructors.
The splitting constructors allow one to "split" either `c` or `d` into two lower values `a` and `b`.

Splitting has applications with well-founded relations; in particular, `<ₛ` is well-founded whenever
`<` is, so this relation can simplify certain inductive steps.
-/
inductive split_lt {α : Type*} (r : α → α → Prop) :
  α × α → α × α → Prop
| left_lt ⦃a b c : α⦄ : r a b → split_lt (a, c) (b, c)
| right_lt ⦃a b c : α⦄ : r b c → split_lt (a, b) (a, c)
| left_split ⦃a b c d : α⦄ : r a c → r b c → split_lt (a, b) (c, d)
| right_split ⦃a b c d : α⦄ : r a d → r b d → split_lt (a, b) (c, d)

lemma le_well_order_extension_lt {α : Type*} {r : α → α → Prop} (hr : well_founded r) :
  r ≤ hr.well_order_extension.lt :=
λ a b h, prod.lex.left _ _ (hr.rank_lt_of_rel h)

lemma to_lex_lt_of_split_lt {α : Type*} {r : α → α → Prop} {hr : well_founded r} :
  split_lt r ≤ inv_image (prod.lex hr.well_order_extension.lt hr.well_order_extension.lt)
    (λ a, if hr.well_order_extension.lt a.1 a.2 then (a.2, a.1) else (a.1, a.2)) :=
begin
  intros a b h,
  induction h with a b c h a b c h a b c d ha hb a b c d ha hb,
  { change prod.lex _ _ _ _,
    simp only,
    split_ifs with h₁ h₂ h₂,
    { exact prod.lex.right _ (le_well_order_extension_lt hr _ _ h), },
    { by_cases hcb : c = b,
      { cases hcb,
        exact prod.lex.right _ h₁, },
      { refine prod.lex.left _ _ _,
        have := (@not_lt _ hr.well_order_extension _ _).mp h₂,
        exact @lt_of_le_of_ne _ (@linear_order.to_partial_order _ hr.well_order_extension)
          _ _ this hcb, }, },
    { cases h₁ ((le_well_order_extension_lt hr _ _ h).trans h₂), },
    { exact prod.lex.left _ _ (le_well_order_extension_lt hr _ _ h), }, },
  { change prod.lex _ _ _ _,
    simp only,
    split_ifs with h₁ h₂ h₂,
    { exact prod.lex.left _ _ (le_well_order_extension_lt hr _ _ h), },
    { cases h₂ (h₁.trans (le_well_order_extension_lt hr _ _ h)), },
    { exact prod.lex.left _ _ h₂, },
    { exact prod.lex.right _ (le_well_order_extension_lt hr _ _ h), }, },
  { change prod.lex _ _ _ _,
    simp only,
    split_ifs with h₁ h₂ h₂,
    { exact prod.lex.left _ _ ((le_well_order_extension_lt hr _ _ hb).trans h₂), },
    { exact prod.lex.left _ _ (le_well_order_extension_lt hr _ _ hb), },
    { exact prod.lex.left _ _ ((le_well_order_extension_lt hr _ _ ha).trans h₂), },
    { exact prod.lex.left _ _ (le_well_order_extension_lt hr _ _ ha), }, },
  { change prod.lex _ _ _ _,
    simp only,
    split_ifs with h₁ h₂ h₂,
    { exact prod.lex.left _ _ (le_well_order_extension_lt hr _ _ hb), },
    { by_cases hcb : c = b,
      { cases hcb,
        exact prod.lex.right _ (le_well_order_extension_lt hr _ _ ha), },
      { refine prod.lex.left _ _ _,
        have := (@not_lt _ hr.well_order_extension _ _).mp h₂,
        exact @lt_of_lt_of_le _
          (@partial_order.to_preorder _ (@linear_order.to_partial_order _ hr.well_order_extension))
          _ _ _ (le_well_order_extension_lt hr _ _ hb) this, }, },
    { exact prod.lex.left _ _ (le_well_order_extension_lt hr _ _ ha), },
    { have := (@not_lt _ hr.well_order_extension _ _).mp h₂,
      have := @lt_of_lt_of_le _
        (@partial_order.to_preorder _ (@linear_order.to_partial_order _ hr.well_order_extension))
        _ _ _ (le_well_order_extension_lt hr _ _ ha) this,
      exact prod.lex.left _ _ this, }, },
end

lemma split_lt_well_founded {α : Type*} {r : α → α → Prop} (hr : well_founded r) :
  well_founded (split_lt r) :=
begin
  refine subrelation.wf to_lex_lt_of_split_lt _,
  { exact hr, },
  { refine inv_image.wf _ (inv_image.wf _ _),
    refine prod.lex_wf _ _;
    exact inv_image.wf _ (prod.lex_wf
      ordinal.well_founded_lt.wf well_ordering_rel.is_well_order.wf), },
end

-- TODO: Clean this up. Proof comes from an old lemma.
lemma complete_atom_map_mem_complete_near_litter_map_to_near_litter' (hπf : π.free)
  {c d : support_condition β} (hcd : (ihs_action π c d).lawful)
  {A : extended_index β} {a : atom} {L : litter} (ha : a.1 = L)
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  π.complete_atom_map A a ∈ π.complete_near_litter_map A L.to_near_litter :=
begin
  subst ha,
  rw complete_near_litter_map_eq,
  by_cases ha : a ∈ (π A).atom_perm.domain,
  { rw complete_atom_map_eq_of_mem_domain ha,
    refine or.inl ⟨or.inr ⟨a, ⟨rfl, ha⟩, rfl⟩, _⟩,
    rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩,
    simp only [foa_hypothesis_atom_image, mem_singleton_iff] at hab,
    rw complete_atom_map_eq_of_not_mem_domain hb.2 at hab,
    have := sublitter.order_iso_apply_mem _,
    rw ← hab at this,
    exact this.2 ((π A).atom_perm.map_domain ha), },
  rw complete_atom_map_eq_of_not_mem_domain ha,
  refine or.inl ⟨or.inl _, _⟩,
  { rw set_like.mem_coe,
    convert sublitter.order_iso_apply_mem _ using 1,
    rw [near_litter_hypothesis_eq, complete_litter_map_eq],
    refl, },
  { rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩,
    simp only [foa_hypothesis_atom_image, mem_singleton_iff] at hab,
    rw complete_atom_map_eq_of_not_mem_domain hb.2 at hab,
    have := litter_injective_extends hπf hcd hL
      (fst_mem_refl_trans_constrained_of_mem_symm_diff hb.1 hL) _,
    { rw [sublitter.order_iso_congr_left (congr_arg _ this) _,
        sublitter.order_iso_congr_right (congr_arg _ (congr_arg2 _ rfl this)) _,
        subtype.coe_inj, equiv_like.apply_eq_iff_eq] at hab,
      simp only [set_like.coe_mk] at hab,
      cases hab,
      exact hb.1.elim (λ h', h'.2 rfl) (λ h', h'.2 rfl), },
    exact order_iso_apply_eq hab, },
end

lemma ihs_action_lawful_extends (hπf : π.free) (c d : support_condition β)
  (hπ : ∀ e f, split_lt (λ c d, c <[α] d) (e, f) (c, d) → (ihs_action π e f).lawful) :
  (ihs_action π c d).lawful :=
begin
  intro A,
  have litter_map_injective : ∀ ⦃L₁ L₂ : litter⦄
    (hL₁ : (inr L₁.to_near_litter, A) ∈ trans_constrained c d)
    (hL₁ : (inr L₂.to_near_litter, A) ∈ trans_constrained c d),
      ((π.complete_near_litter_map A L₁.to_near_litter : set atom) ∩
        (π.complete_near_litter_map A L₂.to_near_litter : set atom)).nonempty →
      L₁ = L₂,
  { intros L₁ L₂ h₁ h₂ h₁₂,
    have := eq_of_complete_litter_map_inter_nonempty h₁₂,
    cases h₁; cases h₂,
    { specialize hπ (inr L₁.to_near_litter, A) (inr L₂.to_near_litter, A)
        (split_lt.left_split h₁ h₂),
      exact litter_injective_extends hπf hπ
        (or.inl relation.refl_trans_gen.refl) (or.inr relation.refl_trans_gen.refl) this, },
    { specialize hπ (inr L₁.to_near_litter, A) d (split_lt.left_lt h₁),
      exact litter_injective_extends hπf hπ
        (or.inl relation.refl_trans_gen.refl) (or.inr h₂.to_refl) this, },
    { specialize hπ c (inr L₁.to_near_litter, A) (split_lt.right_lt h₁),
      exact litter_injective_extends hπf hπ
        (or.inr relation.refl_trans_gen.refl) (or.inl h₂.to_refl) this, },
    { specialize hπ (inr L₁.to_near_litter, A) (inr L₂.to_near_litter, A)
        (split_lt.right_split h₁ h₂),
      exact litter_injective_extends hπf hπ
        (or.inl relation.refl_trans_gen.refl) (or.inr relation.refl_trans_gen.refl) this, }, },
  constructor,
  { intros a b ha hb hab,
    simp only [ihs_action_atom_map] at ha hb hab,
    cases ha; cases hb,
    { specialize hπ (inl a, A) (inl b, A) (split_lt.left_split ha hb),
      exact atom_injective_extends hπ
        (or.inl relation.refl_trans_gen.refl) (or.inr relation.refl_trans_gen.refl) hab, },
    { specialize hπ (inl a, A) d (split_lt.left_lt ha),
      exact atom_injective_extends hπ
        (or.inl relation.refl_trans_gen.refl) (or.inr hb.to_refl) hab, },
    { specialize hπ c (inl a, A) (split_lt.right_lt ha),
      exact atom_injective_extends hπ
        (or.inr relation.refl_trans_gen.refl) (or.inl hb.to_refl) hab, },
    { specialize hπ (inl a, A) (inl b, A) (split_lt.right_split ha hb),
      exact atom_injective_extends hπ
        (or.inl relation.refl_trans_gen.refl) (or.inr relation.refl_trans_gen.refl) hab, }, },
  { exact litter_map_injective, },
  { intros a ha L hL,
    simp only [ihs_action_atom_map, ihs_action_litter_map],
    have : π.complete_atom_map A a ∈ π.complete_near_litter_map A a.fst.to_near_litter,
    { cases ha; cases hL,
      { specialize hπ (inl a, A) (inr L.to_near_litter, A)
          (split_lt.left_split ha hL),
        exact complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
          (fst_mem_refl_trans_constrained' (or.inl relation.refl_trans_gen.refl)), },
      { specialize hπ (inl a, A) d (split_lt.left_lt ha),
        exact complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
          (fst_mem_refl_trans_constrained' (or.inl relation.refl_trans_gen.refl)), },
      { specialize hπ c (inl a, A) (split_lt.right_lt ha),
        exact complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
          (fst_mem_refl_trans_constrained' (or.inr relation.refl_trans_gen.refl)), },
      { specialize hπ (inl a, A) (inr L.to_near_litter, A)
          (split_lt.right_split ha hL),
        exact complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
          (fst_mem_refl_trans_constrained' (or.inl relation.refl_trans_gen.refl)), }, },
    split,
    { rintro rfl,
      exact this, },
    { intro h,
      exact litter_map_injective (fst_mem_trans_constrained' ha) hL ⟨_, this, h⟩, }, },
end

/-- Every `ihs_action` is lawful. This is a consequence of all of the previous lemmas. -/
lemma ihs_action_lawful (hπf : π.free) (c d : support_condition β) : (ihs_action π c d).lawful :=
begin
  suffices : ∀ c : support_condition β × support_condition β, (ihs_action π c.1 c.2).lawful,
  { exact this (c, d), },
  intro c,
  -- Satisfy the elaborator by splitting this line into two.
  have := well_founded.induction (split_lt_well_founded (trans_constrains_wf α β)) c _,
  exact this,
  rintros ⟨c, d⟩ ih,
  exact ihs_action_lawful_extends hπf c d (λ e f hef, ih (e, f) hef),
end

lemma ih_action_lawful (hπf : π.free) (c : support_condition β) :
  (ih_action (π.foa_hypothesis : hypothesis c)).lawful :=
by rw [← ihs_action_self]; exact ihs_action_lawful hπf c c

/-!
We now establish a number of key consequences of `ihs_action_lawful`, such as injectivity.
-/

/-- The complete atom map is injective. -/
lemma complete_atom_map_injective (hπf : π.free) (A : extended_index β) :
  injective (π.complete_atom_map A) :=
λ a b, atom_injective_extends (ihs_action_lawful hπf (inl a, A) (inl b, A))
  (or.inl relation.refl_trans_gen.refl) (or.inr relation.refl_trans_gen.refl)

/-- The complete litter map is injective. -/
lemma complete_litter_map_injective (hπf : π.free) (A : extended_index β) :
  injective (π.complete_litter_map A) :=
λ L₁ L₂, litter_injective_extends hπf
  (ihs_action_lawful hπf (inr L₁.to_near_litter, A) (inr L₂.to_near_litter, A))
  (or.inl relation.refl_trans_gen.refl) (or.inr relation.refl_trans_gen.refl)

/-- Atoms inside litters are mapped inside the corresponding image near-litter. -/
lemma complete_atom_map_mem_complete_near_litter_map_to_near_litter (hπf : π.free)
  {A : extended_index β} {a : atom} {L : litter} :
  π.complete_atom_map A a ∈ π.complete_near_litter_map A L.to_near_litter ↔ a.1 = L :=
begin
  have := complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf
    (ihs_action_lawful hπf (inl a, A) (inl a, A)) rfl
    (fst_mem_refl_trans_constrained' (or.inl relation.refl_trans_gen.refl)),
  split,
  { intro h,
    exact complete_litter_map_injective hπf _
      (eq_of_complete_litter_map_inter_nonempty ⟨_, this, h⟩), },
  { rintro rfl,
    exact this, },
end

lemma mem_image_iff {α β : Type*} {f : α → β} (hf : injective f)
  (x : α) (s : set α) :
  f x ∈ f '' s ↔ x ∈ s :=
set.inj_on.mem_image_iff (hf.inj_on set.univ) (subset_univ _) (mem_univ _)

/-- Atoms inside near litters are mapped inside the corresponding image near-litter. -/
lemma complete_atom_map_mem_complete_near_litter_map (hπf : π.free)
  {A : extended_index β} {a : atom} {N : near_litter} :
  π.complete_atom_map A a ∈ π.complete_near_litter_map A N ↔ a ∈ N :=
begin
  rw [← set_like.mem_coe, complete_near_litter_map_eq', set.symm_diff_def],
  simp only [mem_union, mem_diff, set_like.mem_coe, not_exists, not_and,
    symm_diff_symm_diff_cancel_left],
  rw complete_atom_map_mem_complete_near_litter_map_to_near_litter hπf,
  rw mem_image_iff (complete_atom_map_injective hπf A),
  simp only [← mem_litter_set, ← mem_diff, ← mem_union],
  rw [← set.symm_diff_def, symm_diff_symm_diff_cancel_left],
  rw set_like.mem_coe,
end

/-- The complete near-litter map is injective. -/
lemma complete_near_litter_map_injective (hπf : π.free) (A : extended_index β) :
  injective (π.complete_near_litter_map A) :=
begin
  intros N₁ N₂ h,
  rw [← set_like.coe_set_eq, set.ext_iff] at h ⊢,
  intros a,
  specialize h (π.complete_atom_map A a),
  simp only [set_like.mem_coe, complete_atom_map_mem_complete_near_litter_map hπf] at h ⊢,
  exact h,
end

lemma complete_near_litter_map_subset_range (hπf : π.free) (A : extended_index β) (L : litter) :
  (π.complete_near_litter_map A L.to_near_litter : set atom) ⊆ range (π.complete_atom_map A) :=
begin
  rw complete_near_litter_map_to_near_litter_eq,
  rintros a (⟨ha₁, ha₂⟩ | ⟨a, ⟨ha₁, ha₂⟩, rfl⟩),
  { refine ⟨(((π A).largest_sublitter L).order_iso
      ((π A).largest_sublitter a.1)).symm
      ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a ha₂⟩, _⟩,
    rw complete_atom_map_eq_of_not_mem_domain,
    swap,
    { exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
        (sublitter.order_iso_symm_apply_mem ⟨a, _⟩), },
    { rw mem_litter_set at ha₁,
      have : (((((π A).largest_sublitter L).order_iso
          ((π A).largest_sublitter a.fst)).symm) ⟨a, _⟩ : atom).fst = L :=
        sublitter.order_iso_symm_apply_fst_eq ⟨a, _⟩,
      rw [sublitter.order_iso_congr_left (congr_arg _ this),
        sublitter.order_iso_congr_right (congr_arg _ (congr_arg _ this)),
        sublitter.order_iso_congr_right (congr_arg _ ha₁.symm)],
      simp only [set_like.coe_mk, set_like.eta, order_iso.apply_symm_apply], }, },
  { refine ⟨a, _⟩,
    rw complete_atom_map_eq_of_mem_domain ha₂, },
end

lemma complete_atom_map_surjective_extends (hπf : π.free) (A : extended_index β) (a : atom)
  (h : a.1 ∈ range (π.complete_litter_map A)) :
  a ∈ range (π.complete_atom_map A) :=
begin
  obtain ⟨L, hL⟩ := h,
  by_cases ha : a ∈ (π A).atom_perm.domain,
  { refine ⟨(π A).atom_perm.symm a, _⟩,
    rw complete_atom_map_eq_of_mem_domain ((π A).atom_perm.symm.map_domain ha),
    exact (π A).atom_perm.right_inv ha, },
  { have := complete_near_litter_map_to_near_litter_eq A L,
    rw hL at this,
    have := eq.subset this.symm (or.inl ⟨rfl, ha⟩),
    exact complete_near_litter_map_subset_range hπf A L this, },
end

noncomputable def complete_support_condition_map (π : struct_approx β) :
  support_condition β → support_condition β
| (inl a, B) := (inl (π.complete_atom_map B a), B)
| (inr N, B) := (inr (π.complete_near_litter_map B N), B)

@[simp] lemma complete_support_condition_map_atom_eq {π : struct_approx β}
  {a : atom} {B : extended_index β} :
  π.complete_support_condition_map (inl a, B) = (inl (π.complete_atom_map B a), B) := rfl

@[simp] lemma complete_support_condition_map_near_litter_eq {π : struct_approx β}
  {N : near_litter} {B : extended_index β} :
  π.complete_support_condition_map (inr N, B) = (inr (π.complete_near_litter_map B N), B) := rfl

lemma complete_support_condition_map_injective (hπf : π.free) :
  injective π.complete_support_condition_map :=
begin
  rintros ⟨a₁ | N₁, B₁⟩ ⟨a₂ | N₂, B₂⟩ h;
  simp only [complete_support_condition_map_atom_eq,
    complete_support_condition_map_near_litter_eq,
    prod.mk.inj_iff] at h,
  { cases h.2,
    cases complete_atom_map_injective hπf B₁ h.1,
    refl, },
  { cases h.1, },
  { cases h.1, },
  { cases h.2,
    cases complete_near_litter_map_injective hπf B₁ h.1,
    refl, },
end

def preimage_constrained (π : struct_approx β) (c : support_condition β) :
  set (support_condition β) :=
π.complete_support_condition_map ⁻¹' {d | d ≺[α] c}

lemma preimage_constrained_small (hπf : π.free) (c : support_condition β) :
  small (preimage_constrained π c) :=
small.preimage (complete_support_condition_map_injective hπf) (small_constrains c)

noncomputable def preimage_action (hπf : π.free) (c : support_condition β) : struct_action β :=
constrained_action π (preimage_constrained π c) (preimage_constrained_small hπf c)

lemma preimage_action_eq_constrained_action (hπf : π.free) (c : support_condition β) :
  preimage_action hπf c =
  constrained_action π (preimage_constrained π c) (preimage_constrained_small hπf c) := rfl

-- In fact, any `constrained_action` is lawful.
lemma preimage_action_lawful {hπf : π.free} {c : support_condition β} :
  (preimage_action hπf c).lawful :=
begin
  intro A,
  constructor,
  { intros a b ha hb hab,
    exact complete_atom_map_injective hπf A hab, },
  { intros L₁ L₂ hL₁ hL₂ hL,
    exact complete_litter_map_injective hπf A (eq_of_complete_litter_map_inter_nonempty hL), },
  { intros a ha L hL,
    exact (complete_atom_map_mem_complete_near_litter_map_to_near_litter hπf).symm, },
end

lemma preimage_action_comp_map_flexible {hπf : π.free} {γ : Iio α} {c : support_condition β}
  (A : path (β : type_index) γ) :
  ((preimage_action hπf c).comp A).map_flexible :=
constrained_action_comp_map_flexible hπf A

lemma _root_.relation.refl_trans_gen_of_eq {α : Type*} {r : α → α → Prop} {x y : α}
  (h : x = y) : relation.refl_trans_gen r x y := by cases h; refl

lemma preimage_action_coherent_precise (hπf : π.free) {γ : Iio α} (A : path (β : type_index) γ)
  (B : extended_index γ) (N : near_litter)
  (c : support_condition β) (hc : (inr (π.complete_near_litter_map (A.comp B) N), A.comp B) ≺[α] c)
  (ρ : allowable γ)
  (h : (((preimage_action hπf c).comp A).rc (preimage_action_lawful.comp _)).exactly_approximates
    ρ.to_struct_perm) :
  complete_near_litter_map π (A.comp B) N = struct_perm.derivative B ρ.to_struct_perm • N :=
begin
  refine constrained_action_coherent_precise hπf A B N _ _ _ (preimage_action_lawful.comp _) ρ h,
  refine ⟨_, _, relation.refl_trans_gen.refl⟩,
  exact hc,
end

lemma preimage_action_coherent_precise_atom (hπf : π.free) {γ : Iio α} (A : path (β : type_index) γ)
  (B : extended_index γ) (a : atom)
  (c : support_condition β) (hc : (inl (π.complete_atom_map (A.comp B) a), A.comp B) ≺[α] c)
  (ρ : allowable γ)
  (h : (((preimage_action hπf c).comp A).rc (preimage_action_lawful.comp _)).exactly_approximates
    ρ.to_struct_perm) :
  complete_atom_map π (A.comp B) a = struct_perm.derivative B ρ.to_struct_perm • a :=
begin
  refine constrained_action_coherent_precise_atom hπf A B a _ _ _ _ ρ h,
  refine ⟨_, _, relation.refl_trans_gen.refl⟩,
  exact hc,
end

lemma complete_litter_map_surjective_extends (hπf : π.free) (A : extended_index β) (L : litter)
  (ha : ∀ (B : extended_index β) (a : atom), (inl a, B) ≺[α] (inr L.to_near_litter, A) →
    a ∈ range (π.complete_atom_map B))
  (hN : ∀ (B : extended_index β) (N : near_litter), (inr N, B) ≺[α] (inr L.to_near_litter, A) →
    N ∈ range (π.complete_near_litter_map B)) :
  L ∈ range (π.complete_litter_map A) :=
begin
  obtain (h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩) := flexible_cases' β L A,
  { refine ⟨(near_litter_approx.flexible_completion α (π A) A).symm • L, _⟩,
    rw [complete_litter_map_eq_of_flexible, near_litter_approx.right_inv_litter],
    { rw near_litter_approx.flexible_completion_litter_perm_domain_free α (π A) A (hπf A),
      exact h, },
    { exact near_litter_approx.flexible_completion_symm_smul_flexible α (π A) A (hπf A) L h, }, },
  { obtain ⟨γ, ε, hε, C, a, rfl, rfl⟩ := h,
    obtain ⟨b, rfl⟩ := ha _ a (constrains.f_map_bot hε _ a),
    refine ⟨f_map (show ⊥ ≠ (ε : type_index), from bot_ne_coe) b, _⟩,
    rw complete_litter_map_eq_of_inflexible_bot ⟨γ, ε, hε, C, b, rfl, rfl⟩, },
  { obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h,
    refine ⟨f_map (coe_ne_coe.mpr $ coe_ne' hδε)
      (((preimage_action hπf (inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
        (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesised_allowable
          ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩
          (preimage_action_lawful.comp _) (preimage_action_comp_map_flexible _))⁻¹ • t), _⟩,
    rw complete_litter_map_eq_of_inflexible_coe
      ⟨γ, δ, ε, hδ, hε, hδε, B, _, rfl, rfl⟩
      ((ih_action_lawful hπf _).comp _) (ih_action_comp_map_flexible hπf _ _),
    refine congr_arg _ _,
    rw smul_smul,
    refine (designated_support t).supports _ _,
    intros c hc,
    rw [mul_smul, smul_eq_iff_eq_inv_smul],
    obtain ⟨a | N, A⟩ := c,
    { refine prod.ext _ rfl,
      change inl _ = inl _,
      simp only,
      have hac := constrains.f_map hδ _ _ _ _ _ hc,
      specialize ha _ a hac,
      obtain ⟨b, ha⟩ := ha,
      have : (struct_perm.derivative A
        ((preimage_action hπf (inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
          (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesised_allowable
            ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩
            (preimage_action_lawful.comp _) (preimage_action_comp_map_flexible _)).to_struct_perm)⁻¹
        • a = b,
      { rw [inv_smul_eq_iff, ← ha],
        rw struct_action.hypothesised_allowable,
        refine preimage_action_coherent_precise_atom hπf (B.cons $ coe_lt hδ) A b _ _ _
          (struct_action.allowable_exactly_approximates _ _ _ _),
        rw ha,
        exact hac, },
      transitivity b,
      { rw [map_inv, map_inv, this], },
      { rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← ha],
        rw struct_action.hypothesised_allowable,
        refine (ih_action_coherent_precise_atom hπf (B.cons $ coe_lt hδ) A b _ _
          ((ih_action_lawful hπf _).comp _) _
          (struct_action.allowable_exactly_approximates _ _ _ _)).symm,
        refine relation.trans_gen.tail' _
          (constrains.f_map hδ _ _ _ _ _ (smul_mem_designated_support hc _)),
        refine relation.refl_trans_gen_of_eq _,
        refine prod.ext _ rfl,
        change inl _ = inl _,
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul], }, },
    { refine prod.ext _ rfl,
      change inr _ = inr _,
      simp only,
      have hNc := constrains.f_map hδ _ _ _ _ _ hc,
      specialize hN _ N hNc,
      obtain ⟨N', hN⟩ := hN,
      have : (struct_perm.derivative A
        ((preimage_action hπf (inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
          (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesised_allowable
            ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩
            (preimage_action_lawful.comp _) (preimage_action_comp_map_flexible _)).to_struct_perm)⁻¹
        • N = N',
      { rw [inv_smul_eq_iff, ← hN],
        rw struct_action.hypothesised_allowable,
        refine preimage_action_coherent_precise hπf (B.cons $ coe_lt hδ) A N' _ _ _
          (struct_action.allowable_exactly_approximates _ _ _ _),
        rw hN,
        exact hNc, },
      transitivity N',
      { rw [map_inv, map_inv, this], },
      { rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← hN],
        rw struct_action.hypothesised_allowable,
        refine (ih_action_coherent_precise hπf (B.cons $ coe_lt hδ) A N' _ _
          ((ih_action_lawful hπf _).comp _) _
          (struct_action.allowable_exactly_approximates _ _ _ _)).symm,
        refine relation.trans_gen.tail' _
          (constrains.f_map hδ _ _ _ _ _ (smul_mem_designated_support hc _)),
        refine relation.refl_trans_gen_of_eq _,
        refine prod.ext _ rfl,
        change inr _ = inr _,
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul], }, }, },
end

lemma atom_mem_range_of_mem_complete_near_litter_map (hπf : π.free) (A : extended_index β)
  (a : atom) {N : near_litter} (h : a ∈ π.complete_near_litter_map A N) :
  a ∈ range (π.complete_atom_map A) :=
begin
  rw ← set_like.mem_coe at h,
  rw complete_near_litter_map_eq' at h,
  obtain (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) := h,
  { rw complete_near_litter_map_to_near_litter_eq at h₁,
    cases h₁,
    { exact complete_atom_map_surjective_extends hπf A a ⟨_, h₁.1.symm⟩, },
    { obtain ⟨b, h₁, rfl⟩ := h₁,
      refine ⟨b, _⟩,
      exact complete_atom_map_eq_of_mem_domain h₁.2, }, },
  { obtain ⟨b, h₁, rfl⟩ := h₁,
    exact ⟨b, rfl⟩, },
end

lemma complete_near_litter_map_coe (hπf : π.free) (A : extended_index β) (N : near_litter) :
  (π.complete_near_litter_map A N : set atom) = π.complete_atom_map A '' N :=
begin
  ext a : 1,
  split,
  { intro h,
    obtain ⟨b, rfl⟩ := atom_mem_range_of_mem_complete_near_litter_map hπf A a h,
    rw [set_like.mem_coe, complete_atom_map_mem_complete_near_litter_map hπf] at h,
    exact ⟨b, h, rfl⟩, },
  { rintro ⟨b, h, rfl⟩,
    rw [set_like.mem_coe, complete_atom_map_mem_complete_near_litter_map hπf],
    exact h, },
end

@[simp] lemma preimage_symm_diff {α β : Type*} {s t : set β} {f : α → β} :
  f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) := rfl

lemma complete_near_litter_map_surjective_extends (hπf : π.free) (A : extended_index β)
  (N : near_litter) (hN : N.1 ∈ range (π.complete_litter_map A))
  (ha : litter_set N.1 ∆ N ⊆ range (π.complete_atom_map A)) :
  N ∈ range (π.complete_near_litter_map A) :=
begin
  obtain ⟨L, hN⟩ := hN,
  refine ⟨⟨L, π.complete_atom_map A ⁻¹' N, _⟩, _⟩,
  { suffices : small ((π.complete_atom_map A '' L.to_near_litter) ∆ N),
    { have := small.preimage (complete_atom_map_injective hπf A) this,
      rw [preimage_symm_diff, preimage_image_eq _ (complete_atom_map_injective hπf A)] at this,
      exact this, },
    rw ← complete_near_litter_map_coe hπf,
    refine is_near_litter.near _ N.2.2,
    simp only [near_litter.is_near_litter, complete_near_litter_map_fst_eq],
    exact hN, },
  { refine set_like.coe_injective _,
    rw complete_near_litter_map_coe hπf,
    simp only [near_litter.coe_mk, subtype.coe_mk, litter.coe_to_near_litter],
    rw image_preimage_eq_of_subset _,
    intros a ha',
    by_cases a.1 = N.1,
    { rw ← hN at h,
      exact complete_atom_map_surjective_extends hπf A a ⟨_, h.symm⟩, },
    { exact ha (or.inr ⟨ha', h⟩), }, },
end

variable (π)

def complete_map_surjective_at : support_condition β → Prop
| (inl a, A) := a ∈ range (π.complete_atom_map A)
| (inr N, A) := N ∈ range (π.complete_near_litter_map A)

variable {π}

lemma complete_map_surjective_extends (hπf : π.free) (c : support_condition β)
  (hc : ∀ d : support_condition β, d <[α] c → π.complete_map_surjective_at d) :
  π.complete_map_surjective_at c :=
begin
  obtain ⟨a | N, A⟩ := c,
  { refine complete_atom_map_surjective_extends hπf A a _,
    obtain ⟨N, hN⟩ := hc (inr a.1.to_near_litter, A)
      (relation.trans_gen.single $ constrains.atom a A),
    refine ⟨N.1, _⟩,
    apply_fun sigma.fst at hN,
    simp only [litter.to_near_litter_fst, complete_near_litter_map_fst_eq'] at hN,
    exact hN, },
  { refine complete_near_litter_map_surjective_extends hπf A N _ _,
    { refine complete_litter_map_surjective_extends hπf A N.1 _ _,
      { intros B a h,
        exact hc (inl a, B) (trans_gen_near_litter $ relation.trans_gen.single h), },
      { intros B N h,
        exact hc (inr N, B) (trans_gen_near_litter $ relation.trans_gen.single h), }, },
    { intros a h,
      exact hc (inl a, A) (relation.trans_gen.single $ constrains.symm_diff N a h A), }, },
end

lemma complete_map_surjective_at_all (hπf : π.free) (c : support_condition β) :
  π.complete_map_surjective_at c :=
well_founded.induction (trans_constrains_wf α β) c (complete_map_surjective_extends hπf)

lemma complete_atom_map_surjective (hπf : π.free) (A : extended_index β) :
  surjective (π.complete_atom_map A) :=
λ a, complete_map_surjective_at_all hπf (inl a, A)

lemma complete_near_litter_map_surjective (hπf : π.free) (A : extended_index β) :
  surjective (π.complete_near_litter_map A) :=
λ N, complete_map_surjective_at_all hπf (inr N, A)

lemma complete_litter_map_surjective (hπf : π.free) (A : extended_index β) :
  surjective (π.complete_litter_map A) :=
begin
  intro L,
  obtain ⟨N, hN⟩ := complete_near_litter_map_surjective hπf A L.to_near_litter,
  refine ⟨N.1, _⟩,
  apply_fun sigma.fst at hN,
  simp only [complete_near_litter_map_fst_eq', litter.to_near_litter_fst] at hN,
  exact hN,
end

lemma complete_atom_map_bijective (hπf : π.free) (A : extended_index β) :
  bijective (π.complete_atom_map A) :=
⟨complete_atom_map_injective hπf A, complete_atom_map_surjective hπf A⟩

lemma complete_litter_map_bijective (hπf : π.free) (A : extended_index β) :
  bijective (π.complete_litter_map A) :=
⟨complete_litter_map_injective hπf A, complete_litter_map_surjective hπf A⟩

lemma complete_near_litter_map_bijective (hπf : π.free) (A : extended_index β) :
  bijective (π.complete_near_litter_map A) :=
⟨complete_near_litter_map_injective hπf A, complete_near_litter_map_surjective hπf A⟩

noncomputable def complete_atom_perm (hπf : π.free) (A : extended_index β) : perm atom :=
equiv.of_bijective _ (complete_atom_map_bijective hπf A)

noncomputable def complete_litter_perm (hπf : π.free) (A : extended_index β) : perm litter :=
equiv.of_bijective _ (complete_litter_map_bijective hπf A)

lemma complete_atom_perm_apply (hπf : π.free) (A : extended_index β) (a : atom) :
  complete_atom_perm hπf A a = π.complete_atom_map A a := rfl

lemma complete_litter_perm_apply (hπf : π.free) (A : extended_index β) (L : litter) :
  complete_litter_perm hπf A L = π.complete_litter_map A L := rfl

noncomputable def complete_near_litter_perm (hπf : π.free) (A : extended_index β) :
  near_litter_perm := {
  atom_perm := complete_atom_perm hπf A,
  litter_perm := complete_litter_perm hπf A,
  near := begin
    intros L s hs,
    have : ⇑(complete_atom_perm hπf A)⁻¹ ⁻¹' s =
      (π.complete_near_litter_map A ⟨L, s, hs⟩ : set atom),
    { rw [complete_near_litter_map_coe hπf, perm.preimage_inv],
      refl, },
    rw this,
    simp only [near_litter.is_near_litter, complete_near_litter_map_fst_eq'],
    refl,
  end,
}

lemma complete_near_litter_perm_smul_atom (hπf : π.free) (A : extended_index β)
  (a : atom) :
  complete_near_litter_perm hπf A • a = π.complete_atom_map A a := rfl

lemma complete_near_litter_perm_smul_litter (hπf : π.free) (A : extended_index β)
  (L : litter) :
  complete_near_litter_perm hπf A • L = π.complete_litter_map A L := rfl

lemma complete_near_litter_perm_smul_near_litter (hπf : π.free) (A : extended_index β)
  (N : near_litter) :
  complete_near_litter_perm hπf A • N = π.complete_near_litter_map A N :=
begin
  refine set_like.coe_injective _,
  rw complete_near_litter_map_coe hπf,
  refl,
end

def allowable_below (hπf : π.free) (γ : Iic_index α) (A : path (β : type_index) γ) : Prop :=
  ∃ ρ : allowable γ, ∀ B : extended_index γ,
  struct_perm.of_bot (struct_perm.derivative B ρ.to_struct_perm) =
  complete_near_litter_perm hπf (A.comp B)

@[simp] lemma of_bot_to_struct_perm (π : allowable ⊥) :
  struct_perm.of_bot π.to_struct_perm = π :=
begin
  ext a : 2,
  rw [to_struct_perm_bot],
  simp only [mul_equiv.coe_to_monoid_hom, struct_perm.coe_to_bot_iso, struct_perm.of_bot_to_bot],
end

lemma allowable_below_bot (hπf : π.free) (A : extended_index β) : allowable_below hπf ⊥ A :=
begin
  refine ⟨complete_near_litter_perm hπf A, _⟩,
  intro B,
  obtain (B | ⟨B, h⟩) := B,
  { simp only [struct_perm.derivative_nil, path.comp_nil, of_bot_to_struct_perm], },
  { -- TODO: Make this a lemma.
    cases le_bot_iff.mp (le_of_path B),
    cases bot_le.not_lt h, },
end

lemma exists_nil_cons_of_path' {β γ : type_index} (A : path (β : type_index) γ)
  (hA : A.length ≠ 0) :
  ∃ δ : type_index, ∃ h : (δ : type_index) < β, ∃ B : path δ γ,
  A = ((path.nil : path (β : type_index) β).cons h).comp B :=
begin
  set n := A.length with hn,
  clear_value n,
  induction n with n ih generalizing γ,
  { cases hA rfl, },
  cases A with δ _ A hδ,
  { cases hn, },
  simp only [path.length_cons, nat.succ_eq_add_one, add_left_inj] at hn,
  cases n,
  { cases path.eq_of_length_zero A hn.symm,
    cases path_eq_nil A,
    exact ⟨γ, hδ, path.nil, rfl⟩, },
  { obtain ⟨ε, hε, B, rfl⟩ := ih (n.succ_ne_zero) A hn,
    exact ⟨ε, hε, B.cons hδ, rfl⟩, },
end

lemma exists_nil_cons_of_path {β : Iic α} (A : extended_index β) :
  ∃ γ : Iio_index α, ∃ h : (γ : type_index) < β, ∃ B : extended_index γ,
  A = ((path.nil : path (β : type_index) β).cons h).comp B :=
begin
  obtain ⟨γ, h, B, rfl⟩:= exists_nil_cons_of_path' A _,
  { refine ⟨⟨γ, _⟩, h, B, rfl⟩,
    exact lt_of_lt_of_le h (coe_le_coe.mpr β.prop), },
  { intro h,
    cases path.eq_of_length_zero A h, },
end

lemma Iio_index_cases (δ : Iio_index α) : δ = ⊥ ∨ ∃ ε : Iio α, δ = ε :=
begin
  obtain ⟨(_ | δ), hδ⟩ := δ,
  { exact or.inl rfl, },
  { exact or.inr ⟨⟨δ, coe_lt_coe.mp hδ⟩, rfl⟩, },
end

lemma allowable_below_extends (hπf : π.free) (γ : Iic α) (A : path (β : type_index) γ)
  (h : ∀ (δ : Iio_index α) (h : (δ : type_index) < γ), allowable_below hπf δ (A.cons h)) :
  allowable_below hπf γ A :=
begin
  choose ρs hρ using h,
  refine ⟨allowable_of_smul_f_map γ ρs _, _⟩,
  { intros δ ε hδ hε hδε t,
    change struct_perm.to_near_litter_perm _ • _ = _,
    have := hρ ε hε (path.nil.cons (bot_lt_coe _)),
    simp only [path.comp_cons, path.comp_nil] at this,
    change struct_perm.to_near_litter_perm (ρs ε hε).to_struct_perm = _ at this,
    rw this,
    rw complete_near_litter_perm_smul_litter,
    obtain (rfl | ⟨δ, rfl⟩) := Iio_index_cases δ,
    { refine (complete_litter_map_eq_of_inflexible_bot
        ⟨γ, ε, coe_lt_coe.mp hε, A, t, rfl, rfl⟩).trans _,
      refine congr_arg _ _,
      specialize hρ ⊥ hδ path.nil,
      simp only [struct_perm.derivative_nil, of_bot_to_struct_perm, path.comp_nil] at hρ,
      rw hρ,
      refl, },
    { refine (complete_litter_map_eq_of_inflexible_coe
        ⟨γ, δ, ε, coe_lt_coe.mp hδ, coe_lt_coe.mp hε, _, A, t, rfl, rfl⟩
        ((ih_action_lawful hπf _).comp _)
        (ih_action_comp_map_flexible hπf _ _)).trans _,
      { rintro rfl,
        cases hδε rfl, },
      refine congr_arg _ _,
      rw [← inv_smul_eq_iff, smul_smul],
      refine (designated_support t).supports _ _,
      intros c hc,
      rw [mul_smul, inv_smul_eq_iff],
      obtain ⟨a | N, B⟩ := c,
      { refine prod.ext _ rfl,
        change inl _ = inl _,
        simp only,
        rw ← ih_action_coherent_precise_atom hπf _ B a _
          (relation.trans_gen.single $ constrains.f_map _ _ _ _ _ _ hc) _ _
          (struct_action.hypothesised_allowable_exactly_approximates _
            ⟨γ, δ, ε, _, _, _, _, t, rfl, rfl⟩ _ _),
        exact (congr_arg (λ π, π • a) (hρ δ hδ B)).symm, },
      { refine prod.ext _ rfl,
        change inr _ = inr _,
        simp only,
        rw ← ih_action_coherent_precise hπf _ B N _
          (relation.trans_gen.single $ constrains.f_map _ _ _ _ _ _ hc) _ _
          (struct_action.hypothesised_allowable_exactly_approximates _
            ⟨γ, δ, ε, _, _, _, _, t, rfl, rfl⟩ _ _),
        rw ← complete_near_litter_perm_smul_near_litter hπf,
        exact (congr_arg (λ π, π • N) (hρ δ hδ B)).symm, }, }, },
  { intro B,
    obtain ⟨δ, hδ, B, rfl⟩ := exists_nil_cons_of_path B,
    specialize hρ δ hδ B,
    rw [← struct_perm.derivative_derivative],
    have := allowable_of_smul_f_map_derivative_eq δ hδ,
    apply_fun allowable.to_struct_perm at this,
    rw ← allowable_derivative_eq at this,
    rw ← this at hρ,
    rw [← path.comp_assoc, path.comp_cons, path.comp_nil],
    exact hρ, },
end

lemma allowable_below_all (hπf : π.free) (γ : Iic α) (A : path (β : type_index) γ) :
  allowable_below hπf γ A :=
begin
  obtain ⟨γ, hγ⟩ := γ,
  revert hγ,
  refine well_founded.induction Λwf.wf γ _,
  intros γ ih hγ A,
  refine allowable_below_extends hπf ⟨γ, hγ⟩ A _,
  intros δ hδ,
  obtain (rfl | ⟨δ, rfl⟩) := Iio_index_cases δ,
  { exact allowable_below_bot hπf _, },
  { exact ih δ (coe_lt_coe.mp hδ) (le_of_lt δ.prop) _, },
end

noncomputable def complete_allowable (hπf : π.free) : allowable β :=
(allowable_below_all hπf β path.nil).some

lemma complete_allowable_derivative (hπf : π.free) (A : extended_index β) :
  struct_perm.of_bot (struct_perm.derivative A (complete_allowable hπf).to_struct_perm) =
  complete_near_litter_perm hπf A :=
begin
  have := (allowable_below_all hπf β path.nil).some_spec A,
  rw path.nil_comp at this,
  exact this,
end

lemma complete_exception_mem (hπf : π.free) (A : extended_index β) (a : atom)
  (ha : (complete_near_litter_perm hπf A).is_exception a) :
  a ∈ (π A).atom_perm.domain :=
begin
  unfold near_litter_perm.is_exception at ha,
  simp only [mem_litter_set, complete_near_litter_perm_smul_atom,
    complete_near_litter_perm_smul_litter] at ha,
  cases ha,
  { have := complete_near_litter_map_to_near_litter_eq A a.1,
    rw [complete_near_litter_map_coe hπf, set.ext_iff] at this,
    have := (this (π.complete_atom_map A a)).mp ⟨_, rfl, rfl⟩,
    obtain (ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩) := this,
    { cases ha ha'.1, },
    rw ← complete_atom_map_eq_of_mem_domain hb₂ at hb₃,
    cases complete_atom_map_injective hπf A hb₃,
    exact hb₂, },
  { obtain ⟨a, rfl⟩ := complete_atom_map_surjective hπf A a,
    rw [eq_inv_smul_iff, ← complete_near_litter_perm_smul_atom hπf, inv_smul_smul] at ha,
    have := complete_near_litter_map_to_near_litter_eq A a.1,
    rw [complete_near_litter_map_coe hπf, set.ext_iff] at this,
    have := (this (π.complete_atom_map A a)).mp ⟨_, rfl, rfl⟩,
    obtain (ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩) := this,
    { cases ha ha'.1.symm, },
    { rw ← complete_atom_map_eq_of_mem_domain hb₂ at hb₃,
      cases complete_atom_map_injective hπf A hb₃,
      rw complete_atom_map_eq_of_mem_domain hb₂,
      exact (π A).atom_perm.map_domain hb₂, }, },
end

lemma complete_allowable_exactly_approximates (hπf : π.free) :
  π.exactly_approximates (complete_allowable hπf).to_struct_perm :=
begin
  intro A,
  refine ⟨⟨_, _⟩, _⟩,
  { intros a ha,
    rw [complete_allowable_derivative, complete_near_litter_perm_smul_atom,
      complete_atom_map_eq_of_mem_domain ha], },
  { intros L hL,
    rw [complete_allowable_derivative, complete_near_litter_perm_smul_litter,
      complete_litter_map_eq_of_flexible (hπf A L hL),
      near_litter_approx.flexible_completion_smul_of_mem_domain _ _ A L hL],
    refl, },
  { intros a ha,
    rw complete_allowable_derivative at ha,
    exact complete_exception_mem hπf A a ha, },
end

def foa_extends : foa_ih β :=
λ π hπf, ⟨complete_allowable hπf, complete_allowable_exactly_approximates hπf⟩

theorem freedom_of_action (β : Iic α) (π₀ : struct_approx β) (h : π₀.free) :
  ∃ (π : allowable β), π₀.exactly_approximates π.to_struct_perm :=
begin
  obtain ⟨β, hβ⟩ := β,
  revert hβ,
  refine well_founded.induction Λwf.wf β _,
  intros β ih hβ π₀ h,
  haveI : freedom_of_action_hypothesis ⟨β, hβ⟩,
  { constructor,
    intros γ hγ,
    exact ih γ hγ γ.prop, },
  exact foa_extends π₀ h,
end

end struct_approx

end con_nf
