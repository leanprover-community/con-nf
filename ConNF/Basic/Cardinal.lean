import Mathlib.SetTheory.Cardinal.Cofinality
import ConNF.Basic.Rel

universe u v

namespace Function

open Cardinal

/-- An alternate spelling of `Function.graph`, useful in proving inequalities of cardinals. -/
def graph' {α β : Type _} (f : α → β) : Set (α × β) :=
  {(x, y) | y = f x}

theorem graph'_injective {α β : Type _} : Injective (graph' : (α → β) → Set (α × β)) := by
  intro f g h
  ext x
  have : (x, f x) ∈ graph' f := rfl
  rwa [h] at this

theorem card_graph'_eq {α β : Type _} (f : α → β) : #(f.graph') = #α := by
  rw [Cardinal.eq]
  refine ⟨⟨λ x ↦ x.val.1, λ x ↦ ⟨⟨x, f x⟩, rfl⟩, ?_, ?_⟩⟩
  · rintro ⟨⟨x, _⟩, rfl⟩
    rfl
  · intro x
    rfl

end Function

namespace Cardinal

theorem mul_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a * b ≤ c := by
  apply (mul_le_max a b).trans
  rw [max_le_iff, max_le_iff]
  exact ⟨⟨h1, h2⟩, hc⟩

theorem mk_biUnion_le_of_le_lift {α : Type u} {β : Type v} {s : Set α} {f : ∀ x ∈ s, Set β}
    (c : Cardinal.{v}) (h : ∀ (x : α) (h : x ∈ s), #(f x h) ≤ c) :
    lift.{u} #(⋃ (x : α) (h : x ∈ s), f x h) ≤ lift.{v} #s * lift.{u} c := by
  rw [Set.biUnion_eq_iUnion]
  apply (mk_iUnion_le_lift.{v} (λ (x : s) ↦ f x x.prop)).trans
  refine mul_le_mul le_rfl ?_ (zero_le _) (zero_le _)
  obtain hs | hs := isEmpty_or_nonempty s
  · simp only [ciSup_of_empty, bot_eq_zero', zero_le, lift_zero]
  · apply ciSup_le
    intro x
    have := h x x.prop
    rwa [← lift_le.{u}] at this

theorem mk_biUnion_le_of_le {α β : Type _} {s : Set α} {f : ∀ x ∈ s, Set β}
    (c : Cardinal) (h : ∀ (x : α) (h : x ∈ s), #(f x h) ≤ c) :
    #(⋃ (x : α) (h : x ∈ s), f x h) ≤ #s * c := by
  rw [Set.biUnion_eq_iUnion]
  apply (mk_iUnion_le _).trans
  refine mul_le_mul le_rfl ?_ (zero_le _) (zero_le _)
  obtain hs | hs := isEmpty_or_nonempty s
  · simp only [ciSup_of_empty, bot_eq_zero', zero_le]
  · apply ciSup_le
    intro x
    exact h x x.prop

theorem mk_iUnion_le_of_le_lift {α : Type u} {β : Type v} {f : α → Set β}
    (c : Cardinal.{v}) (h : ∀ (x : α), #(f x) ≤ c) :
    lift.{u} #(⋃ (x : α), f x) ≤ lift.{v} #α * lift.{u} c := by
  have := mk_biUnion_le_of_le_lift (s := Set.univ) (f := λ x _ ↦ f x) c (λ x _ ↦ h x)
  simp only [Set.mem_univ, Set.iUnion_true, mk_univ] at this
  exact this

theorem mk_iUnion_le_of_le {α β : Type _} {f : α → Set β}
    (c : Cardinal) (h : ∀ (x : α), #(f x) ≤ c) :
    #(⋃ (x : α), f x) ≤ #α * c := by
  have := mk_biUnion_le_of_le (s := Set.univ) (f := λ x _ ↦ f x) c (λ x _ ↦ h x)
  simp only [Set.mem_univ, Set.iUnion_true, mk_univ] at this
  exact this

theorem lift_isRegular (c : Cardinal.{u}) (h : IsRegular c) : IsRegular (lift.{v} c) := by
  constructor
  · rw [← lift_aleph0.{v, u}, lift_le]
    exact h.1
  · rw [← lift_ord, ← Ordinal.lift_cof, lift_le]
    exact h.2

theorem le_of_le_add {c d e : Cardinal.{u}} (h : c ≤ d + e) (hc : ℵ₀ ≤ c) (he : e < c) : c ≤ d := by
  by_contra! h'
  exact (add_lt_of_lt hc h' he).not_le h

theorem mk_ne_zero_iff_nonempty {α : Type _} (s : Set α) :
    #s ≠ 0 ↔ s.Nonempty := by
  rw [mk_ne_zero_iff]
  exact Set.nonempty_coe_sort

theorem compl_nonempty_of_mk_lt {α : Type _} {s : Set α} (h : #s < #α) : sᶜ.Nonempty := by
  rw [← mk_ne_zero_iff_nonempty]
  intro h'
  have := mk_sum_compl s
  rw [h', add_zero] at this
  exact h.ne this

theorem mk_pow_le_of_mk_lt_ord_cof {α β : Type _}
    (hα : (#α).IsStrongLimit) (hβ : #β < (#α).ord.cof) :
    #α ^ #β ≤ #α := by
  by_cases hβ' : #β = 0
  · rw [hβ', power_zero]
    exact one_le_iff_ne_zero.mpr hα.1
  have hαβ : #(β × α) = #α := by
    rw [mk_prod, lift_id, lift_id]
    apply mul_eq_right
    · exact aleph0_le_of_isSuccLimit hα.isSuccLimit
    · exact hβ.le.trans (Ordinal.cof_ord_le (#α))
    · exact hβ'
  have := mk_subset_mk_lt_cof (α := β × α) (hαβ ▸ hα.2)
  refine le_trans ?_ (this.trans hαβ).le
  rw [power_def]
  refine mk_le_of_injective (f := λ f ↦ ⟨f.graph', ?_⟩) ?_
  · rwa [hαβ, Function.card_graph'_eq]
  · intro f g h
    exact Function.graph'_injective (congr_arg Subtype.val h)

/-- If `c` is a strong limit and `d` is not "too large", then `c ^ d = c`.
By "too large" here, we mean large enough to be a counterexample by König's theorem on cardinals:
`c < c ^ c.ord.cof`. -/
theorem pow_le_of_lt_ord_cof {c d : Cardinal} (hc : c.IsStrongLimit) (hd : d < c.ord.cof) :
    c ^ d ≤ c := by
  induction c using inductionOn
  induction d using inductionOn
  exact mk_pow_le_of_mk_lt_ord_cof hc hd

theorem mk_fun_le (α β : Type _) :
    #(α → β) ≤ #(Set (α × β)) :=
  mk_le_of_injective (f := Function.graph') Function.graph'_injective

theorem mk_power_le_two_power (α β : Type _) :
    #α ^ #β ≤ max ℵ₀ (max (2 ^ #α) (2 ^ #β)) := by
  -- Brutal case analysis - there's got to be a cleaner proof.
  by_cases hα : #α < ℵ₀
  · by_cases hβ : #β < ℵ₀
    · exact (power_lt_aleph0 hα hβ).le.trans (le_max_left _ _)
    · rw [not_lt] at hβ
      rw [lt_aleph0] at hα
      obtain ⟨n, hα'⟩ := hα
      rw [hα']
      by_cases hα'' : n < 2
      · cases n with
        | zero =>
          norm_cast
          rw [zero_power]
          exact Cardinal.zero_le _
          exact ne_zero_of_lt (aleph0_pos.trans_le hβ)
        | succ n => cases n with
          | zero => simp only [zero_add, Nat.cast_one, one_power, power_one, le_max_iff,
              Nat.one_le_ofNat, true_or, or_true]
          | succ n => linarith
      · rw [not_lt] at hα''
        rw [nat_power_eq hβ hα'']
        apply le_max_of_le_right
        exact le_max_right _ _
  · rw [not_lt] at hα
    have := mk_fun_le β α
    rw [mk_pi, prod_const, lift_id, lift_id, mk_set, mk_prod, lift_id, lift_id] at this
    apply this.trans
    clear this
    by_cases hβ : #β < ℵ₀
    · by_cases hβ' : #β = 0
      · rw [hβ', zero_mul, power_zero]
        apply le_max_of_le_right
        exact le_max_right _ _
      · rw [mul_eq_right hα (hβ.le.trans hα) hβ']
        apply le_max_of_le_right
        exact le_max_left _ _
    · rw [not_lt] at hβ
      wlog h : #α ≤ #β
      · have := this β α hβ hα (le_of_not_le h)
        rwa [mul_comm, max_comm (2 ^ #α)]
      · rw [mul_eq_left hβ h (ne_zero_of_lt (aleph0_pos.trans_le hα))]
        apply le_max_of_le_right
        exact le_max_right _ _

theorem power_le_two_power (c d : Cardinal) :
    c ^ d ≤ max ℵ₀ (max (2 ^ c) (2 ^ d)) := by
  induction c using inductionOn
  induction d using inductionOn
  exact mk_power_le_two_power _ _

/-- Strong limit cardinals are closed under exponentials. -/
theorem pow_lt_of_lt {c d e : Cardinal} (hc : c.IsStrongLimit) (hd : d < c) (he : e < c) :
    d ^ e < c := by
  by_cases hc' : ℵ₀ < c
  · apply (power_le_two_power d e).trans_lt
    rw [max_lt_iff, max_lt_iff]
    exact ⟨hc', hc.2 d hd, hc.2 e he⟩
  · cases eq_of_le_of_not_lt (aleph0_le_of_isSuccLimit hc.isSuccLimit) hc'
    exact power_lt_aleph0 hd he

theorem card_codom_le_of_functional {α β : Type _} {r : Rel α β} (hr : r.Functional) :
    #r.codom ≤ #r.dom := by
  refine le_trans ?_ (mk_image_le (f := r.toFunction hr) (s := r.dom))
  apply mk_le_mk_of_subset
  rintro b ⟨a, h⟩
  refine ⟨a, ⟨b, h⟩, ?_⟩
  rwa [Rel.toFunction_eq_iff]

theorem card_codom_le_of_coinjective {α β : Type _} {r : Rel α β} (hr : r.Coinjective) :
    #r.codom ≤ #r.dom := by
  have := card_codom_le_of_functional (r := λ (a : r.dom) b ↦ r a b) ?_
  · refine le_trans ?_ (this.trans ?_)
    · apply mk_le_mk_of_subset
      rintro b ⟨a, h⟩
      exact ⟨⟨a, b, h⟩, h⟩
    · exact mk_subtype_le _
  · constructor
    · constructor
      intro b₁ b₂ a h₁ h₂
      exact hr.coinjective h₁ h₂
    · constructor
      intro a
      exact a.prop

end Cardinal
