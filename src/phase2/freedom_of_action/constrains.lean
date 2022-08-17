import phase2.freedom_of_action.allowable

/-!
# Constraints

Support conditions can be said to *constrain* each other in a number of ways.
This is detailed below. The `constrains` relation is well-founded.
-/

open quiver sum with_bot

universe u

namespace con_nf
variables [params.{u}]

open struct_perm

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] (B : le_index α)

/--
Support conditions can be said to *constrain* each other in a number of ways. This is discussed
in the "freedom of action discussion".

1. `⟨L, A⟩ ≺ ⟨a, A⟩` when `a ∈ L` and `L` is a litter. We can say that an atom is constrained by the
    litter it belongs to.
2. `⟨N°, A⟩ ≺ ⟨N, A⟩` when `N` is a near-litter not equal to its corresponding litter `N°`.
3. `⟨a, A⟩ ≺ ⟨N, A⟩` for all `a ∈ N ∆ N°`.
4. `⟨y, B : (γ < β) : A⟩ ≺ ⟨L, A⟩` for all paths `A : α ⟶ β` and `γ, δ < β` with `γ ≠ δ`,
    and `L = f_{γ,δ}^A(x)` for some `x ∈ τ_{γ:A}`, where `⟨y, B⟩` lies in the designated support
    `S_x` of `x`.
-/
@[mk_iff] inductive constrains : support_condition B → support_condition B → Prop
| mem_litter (L : litter) (a ∈ litter_set L) (A : extended_index B) :
    constrains ⟨inr L.to_near_litter, A⟩ ⟨inl a, A⟩
| near_litter (N : near_litter) (hN : litter_set N.fst ≠ N.snd) (A : extended_index B) :
    constrains ⟨inr N.fst.to_near_litter, A⟩ ⟨inr N, A⟩
| symm_diff (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd) (A : extended_index B) :
    constrains ⟨inl a, A⟩ ⟨inr N, A⟩
| f_map ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (B : type_index) β)
    (t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α))
    (c ∈ (designated_support_path t).carrier) :
    constrains
      ⟨c.fst, path.comp (A.cons hγ) c.snd⟩
      ⟨inr (f_map_path hγ hδ t).to_near_litter,
        (A.cons (coe_lt_coe.mpr hδ)).cons (bot_lt_coe _)⟩

/-! We declare new notation for the "constrains" relation on support conditions. -/
infix ` ≺ `:50 := constrains _

/-- A litter and extended index is flexible only if it is not constrained by anything. -/
lemma unconstrained_of_flex (L : litter) (A : extended_index B) (h : flex L A) :
∀ c, ¬ c ≺ ⟨inr L.to_near_litter, A⟩ :=
begin
  intros c hc,
  rw constrains_iff at hc,
  obtain ⟨L, a, ha, A', hc, hA'⟩ | ⟨N, hN, A', hc, hA'⟩ |
    ⟨N, a, ha, A', hc, hA'⟩ | ⟨β, δ, γ, hγ, hδ, hγδ, A', t, ht, c', hc, h'⟩ := hc,
  { cases hA' },
  { obtain ⟨hLN, hAA'⟩ := prod.mk.inj_iff.1 hA',
    simp only at hLN,
    rw ← hLN at hN,
    apply hN, refl },
  { obtain ⟨hLN, hAA'⟩ := prod.mk.inj_iff.1 hA',
    suffices : litter_set N.1 = N.2,
    { have that := symm_diff_self (litter_set N.1),
      nth_rewrite 1 this at that,
      rw that at ha, exact ha },
    simp only at hLN,
    rw ← hLN, refl },
    unfold extended_index at A,
  refine h hγ hδ hγδ _ _ t _,
  cases h', refl,
  simp only [prod.mk.inj_iff, litter.to_near_litter_injective.eq_iff] at h',
  exact h'.1,
end

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `⟨x, A⟩ ≺ ⟨y, B⟩`,
then `x < y` in `µ`, under the `typed_near_litter_path` or `typed_singleton_path` maps. -/
lemma constrains_wf : well_founded (constrains B) := sorry

instance : has_well_founded (support_condition B) := ⟨constrains B, constrains_wf B⟩

end con_nf
