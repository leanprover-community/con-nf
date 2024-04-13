import Mathlib.Data.Prod.Lex
import ConNF.Fuzz
import ConNF.FOA.Basic.Hypotheses

/-!
# The constrains relation

Addresses can be said to *constrain* each other in a number of ways.
This is detailed below. The `Constrains` relation is well-founded.

## Main declarations
* `ConNF.Constrains`: The constrains relation.
* `ConNF.constrains_wf`: The constrains relation is well-founded.
* `ConNF.small_constrains`: Only a small amount of things are constrained by a particular address.
-/

open Quiver Set Sum WithBot

open scoped Cardinal Classical symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : Λ}

/--
Addresses can be said to *constrain* each other in a number of ways.

1. `(L, A) ≺ (a, A)` when `a ∈ L` and `L` is a litter. We can say that an atom is constrained by the
    litter it belongs to.
2. `(N°, A) ≺ (N, A)` when `N` is a near-litter not equal to its corresponding litter `N°`.
3. `(a, A) ≺ (N, A)` for all `a ∈ N ∆ N°`.
4. `(x, A ⬝ (γ ⟶ δ) ⬝ B) ≺ (f_{γ,δ}(t), A ⬝ (γ ⟶ ε) ⬝ (ε ⟶ ⊥))` for all paths `A : β ⟶ γ` and
    `δ, ε < γ` with `δ ≠ ε`, `t` a `γ`-tangle, where `(x, B)` lies in the `δ`-support in `t`.

This choice of relation makes some parts of the freedom of action theorem easier to prove.
-/
@[mk_iff]
inductive Constrains : Address β → Address β → Prop
  | atom (A : ExtendedIndex β) (a : Atom) : Constrains ⟨A, inr a.1.toNearLitter⟩ ⟨A, inl a⟩
  | nearLitter (A : ExtendedIndex β) (N : NearLitter) (hN : ¬N.IsLitter) :
    Constrains ⟨A, inr N.fst.toNearLitter⟩ ⟨A, inr N⟩
  | symmDiff (A : ExtendedIndex β) (N : NearLitter) (a : Atom) :
    a ∈ litterSet N.fst ∆ N → Constrains ⟨A, inl a⟩ ⟨A, inr N⟩
  | fuzz ⦃γ : Λ⦄ [LeLevel γ] ⦃δ : Λ⦄ [LtLevel δ] ⦃ε : Λ⦄ [LtLevel ε]
    (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε)
    (A : Path (β : TypeIndex) γ) (t : Tangle δ) (c : Address δ) :
    c ∈ t.support →
    Constrains ⟨(A.cons hδ).comp c.path, c.value⟩
      ⟨(A.cons hε).cons (bot_lt_coe _), inr (fuzz hδε t).toNearLitter⟩
  | fuzzBot ⦃γ : Λ⦄ [LeLevel γ] ⦃ε : Λ⦄ [LtLevel ε]
    (hε : (ε : TypeIndex) < γ) (A : Path (β : TypeIndex) γ) (a : Atom) :
    Constrains ⟨A.cons (bot_lt_coe _), inl a⟩
      ⟨(A.cons hε).cons (bot_lt_coe _), inr (fuzz (bot_ne_coe (a := ε)) a).toNearLitter⟩

/-! We declare new notation for the "constrains" relation on addresses. -/

@[inherit_doc] infix:50 " ≺ " => Constrains

def Address.pos (c : Address β) : μ :=
  c.2.elim Position.pos Position.pos

@[simp]
theorem Address.pos_atom (A : ExtendedIndex β) (a : Atom) :
    Address.pos ⟨A, inl a⟩ = Position.pos a :=
  rfl

@[simp]
theorem Address.pos_nearLitter (A : ExtendedIndex β) (N : NearLitter) :
    Address.pos ⟨A, inr N⟩ = Position.pos N :=
  rfl

/-- If `c` constrains `d`, then the position of `c` is less than the position of `d`. -/
theorem Constrains.hasPosition_lt {c d : Address β} (h : c ≺ d) :
    c.pos < d.pos := by
  cases h
  case atom A a => exact BasePositions.lt_pos_atom a
  case nearLitter A N hN => exact BasePositions.lt_pos_litter N hN
  case symmDiff A N a ha => exact BasePositions.lt_pos_symmDiff a N ha
  case fuzz γ _ δ _ ε _ hδ hε hδε A t c hc' =>
    have := pos_lt_pos_fuzz_nearLitter hδε t (ConNF.fuzz hδε t).toNearLitter rfl
    obtain ⟨B, a | N⟩ := c
    · simp only [Address.pos_atom, Address.pos_nearLitter]
      exact (pos_lt_pos_atom _ hc').trans this
    · simp only [Address.pos_nearLitter]
      by_cases h : t.set = typedNearLitter N
      · exact (pos_typedNearLitter N t h).trans_lt this
      · exact (pos_lt_pos_nearLitter _ hc' h).trans this
  case fuzzBot γ _ ε _ hε A a =>
    simp only [Address.pos_atom, Address.pos_nearLitter]
    exact pos_lt_pos_fuzz_nearLitter (bot_ne_coe (a := ε)) a
      (ConNF.fuzz (bot_ne_coe (a := ε)) a).toNearLitter rfl

theorem constrains_subrelation (β : Λ) :
    Subrelation ((· ≺ ·) : Address β → _ → Prop) (InvImage (· < ·) Address.pos) :=
  Constrains.hasPosition_lt

/-- The `≺` relation is well-founded. -/
theorem constrains_wf (β : Λ) : WellFounded ((· ≺ ·) : Address β → _ → Prop) :=
  Subrelation.wf (constrains_subrelation β) (InvImage.wf _ Params.μ_isWellOrder.wf)

/-! We establish some useful lemmas that show what addresses can possibly constrain what other
addresses. -/

@[simp]
theorem constrains_atom {c : Address β} {A : ExtendedIndex β} {a : Atom} :
    c ≺ ⟨A, inl a⟩ ↔ c = ⟨A, inr a.1.toNearLitter⟩ := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact Constrains.atom A a

theorem constrains_nearLitter {c : Address β} {A : ExtendedIndex β}
    {N : NearLitter} (hN : ¬N.IsLitter) :
    c ≺ ⟨A, inr N⟩ ↔ c = ⟨A, inr N.1.toNearLitter⟩ ∨
      ∃ a ∈ litterSet N.fst ∆ N.snd, c = ⟨A, inl a⟩ := by
  constructor
  · intro h
    rw [constrains_iff] at h
    obtain ⟨A, a, rfl, hc⟩ | ⟨A, N, hN, rfl, hc⟩ | ⟨A, N, a, ha, rfl, hc⟩ |
        ⟨γ, _, δ, _, ε, _, hδ, hε, hδε, A, t, c, _, rfl, hc'⟩ |
        ⟨γ, _, ε, _, hγ, A, a, rfl, hc⟩ := h
    · cases hc
    · cases hc
      exact Or.inl rfl
    · cases hc
      exact Or.inr ⟨a, ha, rfl⟩
    · cases hc'
      cases hN (NearLitter.IsLitter.mk _)
    · cases hc
      cases hN (NearLitter.IsLitter.mk _)
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact Constrains.nearLitter A N hN
    · exact Constrains.symmDiff A N a ha

/-- The constrains relation is stable under composition of paths. The converse is false. -/
theorem constrains_comp {β γ : Λ} {c d : Address γ} (h : c ≺ d)
    (B : Path (β : TypeIndex) γ) : ⟨B.comp c.path, c.value⟩ ≺ ⟨B.comp d.path, d.value⟩ := by
  obtain ⟨A, a⟩ | ⟨A, N, hN⟩ | ⟨A, N, a, ha⟩ | ⟨hδ, hε, hδε, A, t, c, hc⟩ | ⟨hδ, A, a⟩ := h
  · exact Constrains.atom _ _
  · exact Constrains.nearLitter _ _ hN
  · exact Constrains.symmDiff _ _ _ ha
  · rw [Path.comp_cons, ← Path.comp_assoc, Path.comp_cons]
    exact Constrains.fuzz hδ hε hδε (B.comp A) t c hc
  · rw [Path.comp_cons]
    exact Constrains.fuzzBot hδ (B.comp A) a

/-!
We establish a strict partial order `<` on addresses given by the transitive closure of the
constrains relation. This is well-founded.
-/

instance : PartialOrder (Address β) where
  le := Relation.ReflTransGen (· ≺ ·)
  lt := Relation.TransGen (· ≺ ·)
  le_refl := fun _ => Relation.ReflTransGen.refl
  le_trans := fun _ _ _ => Relation.ReflTransGen.trans
  lt_iff_le_not_le := by
    intro c d
    constructor
    · intro h
      exact ⟨h.to_reflTransGen,
        fun h' => (constrains_wf β).transGen.isIrrefl.irrefl d (h.trans_right h')⟩
    · intro h
      obtain (rfl | h') := Relation.reflTransGen_iff_eq_or_transGen.mp h.1
      · cases h.2 Relation.ReflTransGen.refl
      · exact h'
  le_antisymm := by
    intro c d h₁ h₂
    obtain (h₁ | h₁) := Relation.reflTransGen_iff_eq_or_transGen.mp h₁
    · exact h₁.symm
    obtain (h₂ | h₂) := Relation.reflTransGen_iff_eq_or_transGen.mp h₂
    · exact h₂
    cases (constrains_wf β).transGen.isIrrefl.irrefl c (h₁.trans h₂)

instance : WellFoundedLT (Address β) where
  wf := (constrains_wf β).transGen

instance : WellFoundedRelation (Address β) :=
  ⟨(· < ·), (constrains_wf β).transGen⟩

theorem Address.le_iff {c d : Address β} :
    c ≤ d ↔ Relation.ReflTransGen (· ≺ ·) c d :=
  Iff.rfl

theorem Address.lt_iff {c d : Address β} :
    c < d ↔ Relation.TransGen (· ≺ ·) c d :=
  Iff.rfl

theorem le_comp {β γ : Λ} {c d : Address γ} (h : c ≤ d)
    (B : Path (β : TypeIndex) γ) :
    (⟨B.comp c.path, c.value⟩ : Address β) ≤ ⟨B.comp d.path, d.value⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.tail ih (constrains_comp h B)

theorem lt_comp {β γ : Λ} {c d : Address γ} (h : c < d)
    (B : Path (β : TypeIndex) γ) :
    (⟨B.comp c.path, c.value⟩ : Address β) < ⟨B.comp d.path, d.value⟩ := by
  induction h with
  | single h => exact Relation.TransGen.single (constrains_comp h B)
  | tail _ h ih => exact Relation.TransGen.tail ih (constrains_comp h B)

theorem le_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : Address β} (h : ⟨B, inr N⟩ ≤ c) : ⟨B, inr N.1.toNearLitter⟩ ≤ c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.ReflTransGen.head (Constrains.nearLitter B N h') h

theorem lt_nearLitter {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : Address β} (h : c < ⟨B, inr N.1.toNearLitter⟩) : c < ⟨B, inr N⟩ := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.tail h (Constrains.nearLitter B N h')

theorem lt_nearLitter' {β : Λ} {N : NearLitter} {B : ExtendedIndex β}
    {c : Address β} (h : ⟨B, inr N⟩ < c) : ⟨B, inr N.1.toNearLitter⟩ < c := by
  by_cases h' : N.IsLitter
  · obtain ⟨L, rfl⟩ := h'.exists_litter_eq
    exact h
  · exact Relation.TransGen.head (Constrains.nearLitter B N h') h

/-- There is a small amount of addresses that constrain a given address. -/
theorem small_constrains {β : Λ} (c : Address β) : Small {d | d ≺ c} := by
  obtain ⟨A, a | N⟩ := c
  · simp only [constrains_atom, setOf_eq_eq_singleton, small_singleton]
  simp_rw [constrains_iff]
  refine Small.union ?_ (Small.union ?_ (Small.union ?_ (Small.union ?_ ?_))) <;>
    rw [small_setOf]
  · change Small {c | ∃ b B, _ ∧ _ = _}
    simp only [Address.mk.injEq, false_and, and_false, exists_false,
      setOf_false, small_empty]
  · change Small {c | ∃ B N', _}
    refine Set.Subsingleton.small ?_
    rintro c ⟨_, _, _, ⟨rfl, rfl⟩, h₁⟩ d ⟨_, _, _, ⟨rfl, rfl⟩, h₂⟩
    cases h₁
    cases h₂
    rfl
  · change Small {c | ∃ B N' a, _}
    convert (show Small (litterSet N.fst ∆ N) from N.2.prop).image
      (f := fun a : Atom => (⟨A, inl a⟩ : Address β)) using 1
    ext c : 1
    simp only [mem_setOf_eq, mem_image]
    constructor
    · rintro ⟨B, N', a, h₁, h₂, h₃⟩
      cases h₃
      exact ⟨a, h₁, h₂.symm⟩
    · rintro ⟨a, h₁, h₂⟩
      exact ⟨A, N, a, h₁, h₂.symm, rfl⟩
  · by_cases h :
      ∃ (γ : Λ) (_ : LeLevel γ) (δ : Λ) (_ : LtLevel δ) (ε : Λ) (_ : LtLevel ε)
        (_ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ) (hδε : (δ : TypeIndex) ≠ ε)
        (B : Path (β : TypeIndex) γ) (t : Tangle δ),
        N = (fuzz hδε t).toNearLitter ∧ A = (B.cons hε).cons (bot_lt_coe _)
    · obtain ⟨γ, _, δ, _, ε, _, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
      refine lt_of_le_of_lt ?_ t.support.small
      suffices
        #{a : Address β | ∃ c : (t.support : Set (Address δ)),
            a = ⟨(B.cons hδ).comp c.val.path, c.val.value⟩} ≤
          #(t.support : Set (Address δ)) by
        refine le_trans (Cardinal.mk_subtype_le_of_subset ?_) this
        rintro x ⟨_, _, _, _, _, _, _, _, _, _, _, c, hc, rfl, h⟩
        rw [Address.mk.injEq] at h
        simp only [inr.injEq, Litter.toNearLitter_injective.eq_iff] at h
        cases WithBot.coe_injective (fuzz_congr_β h.2)
        cases fuzz_congr_γ h.2
        cases fuzz_injective _ h.2
        cases coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.1).eq)
        cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons h.1).eq).eq
        exact ⟨⟨c, hc⟩, rfl⟩
      refine ⟨⟨fun a => a.prop.choose, ?_⟩⟩
      intro a b h
      refine Subtype.coe_inj.mp ?_
      rw [a.prop.choose_spec, b.prop.choose_spec]
      simp only [h]
    · refine small_of_forall_not_mem ?_
      rintro x ⟨γ, _, δ, _, ε, _, hδ, hε, hδε, B, t, c, _, rfl, hA⟩
      rw [Address.mk.injEq] at hA
      simp only [inr.injEq] at hA
      exact h ⟨γ, inferInstance, δ, inferInstance, ε, inferInstance, hδ, hε, hδε, B, t, hA.2, hA.1⟩
  · refine Set.Subsingleton.small ?_
    rintro ⟨c, C⟩ ⟨γ, _, ε, _, hε, C', a, hc₁, hc₂⟩ ⟨d, D⟩ ⟨γ, _, ε, _, hε, D', b, hd₁, hd₂⟩
    rw [Address.mk.injEq] at hc₁ hc₂ hd₁ hd₂
    simp only [inr.injEq] at hc₂ hd₂
    rw [hc₁.1, hc₁.2, hd₁.1, hd₁.2]
    rw [hc₂.1, hc₂.2, Litter.toNearLitter_injective.eq_iff] at hd₂
    cases coe_inj.mp (Path.obj_eq_of_cons_eq_cons hd₂.1)
    cases coe_inj.mp (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.1).eq)
    cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hd₂.1).eq).eq
    rw [(fuzz_injective bot_ne_coe).eq_iff] at hd₂
    cases hd₂.2
    rfl

/-- The reflexive transitive closure of a set of addresses. -/
def reflTransClosure (S : Set (Address β)) : Set (Address β) :=
  {c | ∃ d ∈ S, c ≤ d}

/-- The transitive closure of a set of addresses. -/
def transClosure (S : Set (Address β)) : Set (Address β) :=
  {c | ∃ d ∈ S, c < d}

/-- Gadget that helps us prove that the `reflTransClosure` of a small set is small. -/
def nthClosure (S : Set (Address β)) : ℕ → Set (Address β)
  | 0 => S
  | n + 1 => {c | ∃ d, d ∈ nthClosure S n ∧ c ≺ d}

/-- The `nthClosure` of a small set is small. -/
theorem small_nthClosure {S : Set (Address β)} {n : ℕ} (h : Small S) :
    Small (nthClosure S n) := by
  induction' n with n hn
  exact h
  rw [nthClosure]
  simp_rw [← exists_prop, Subtype.exists', setOf_exists]
  refine' small_iUnion hn _
  rintro ⟨c, _⟩
  exact small_constrains c

theorem mem_nthClosure_iff {S : Set (Address β)} {n : ℕ} {c : Address β} :
    c ∈ nthClosure S n ↔
      ∃ l, List.Chain (· ≺ ·) c l ∧
        l.length = n ∧ (c::l).getLast (List.cons_ne_nil _ _) ∈ S := by
  induction' n with n hn generalizing c
  · rw [nthClosure]
    constructor
    · intro h
      exact ⟨[], List.Chain.nil, rfl, h⟩
    · rintro ⟨l, h₁, h₂, h₃⟩
      rw [List.length_eq_zero] at h₂
      cases h₂
      exact h₃
  · simp only [nthClosure, mem_setOf_eq]
    constructor
    · rintro ⟨d, hd₁, hd₂⟩
      obtain ⟨l, hl₁, hl₂, hl₃⟩ := hn.mp hd₁
      refine' ⟨d::l, List.Chain.cons hd₂ hl₁, _, _⟩
      · rw [List.length_cons, hl₂]
      · rw [List.getLast_cons]
        exact hl₃
    · rintro ⟨_ | ⟨d, l⟩, hl₁, hl₂, hl₃⟩
      · cases hl₂
      obtain _ | ⟨hcd, hl₁⟩ := hl₁
      rw [List.getLast_cons] at hl₃
      have := hn.mpr ⟨l, hl₁, Nat.succ.inj hl₂, hl₃⟩
      exact ⟨d, this, hcd⟩

/-- The `reflTransClosure` of a set is the `ℕ`-indexed union of the `n`th closures. -/
theorem reflTransClosure_eq_iUnion_nthClosure {S : Set (Address β)} :
    reflTransClosure S = ⋃ n, nthClosure S n := by
  refine' subset_antisymm _ _
  · rintro c ⟨d, hdS, hd⟩
    obtain ⟨l, hl, rfl⟩ := List.exists_chain_of_relationReflTransGen hd
    rw [mem_iUnion]
    refine' ⟨l.length, _⟩
    rw [mem_nthClosure_iff]
    refine' ⟨l, hl, rfl, hdS⟩
  · intro c hc
    rw [mem_iUnion] at hc
    obtain ⟨i, hc⟩ := hc
    rw [mem_nthClosure_iff] at hc
    obtain ⟨l, hl₁, _hl₂, hl₃⟩ := hc
    exact
      ⟨(c::l).getLast (List.cons_ne_nil _ _), hl₃,
        List.relationReflTransGen_of_exists_chain l hl₁ rfl⟩

/-- The `reflTransClosure` of a small set is small. -/
theorem reflTransClosure_small {S : Set (Address β)} (h : Small S) :
    Small (reflTransClosure S) := by
  rw [reflTransClosure_eq_iUnion_nthClosure]
  have : Small (⋃ n : ULift ℕ, nthClosure S n.down)
  · refine' small_iUnion _ fun _ => small_nthClosure h
    rw [Cardinal.mk_denumerable]
    exact aleph0_le_mk_Λ.trans_lt Params.Λ_lt_κ
  convert this using 1
  ext x : 1
  simp only [mem_iUnion, ULift.exists]

/-- The `transClosure` of a small set is small. -/
theorem transClosure_small {S : Set (Address β)} (h : Small S) :
    Small (transClosure S) := by
  refine' lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset _) (reflTransClosure_small h)
  rintro c ⟨d, hd₁, hd₂⟩
  exact ⟨d, hd₁, hd₂.to_reflTransGen⟩

end ConNF
