import A_map

/-!
# Equivalence of codes

Several codes will be identified to make one TTT object. A TTT object has extensions for all type
indices (except possibly `⊥`), so our equivalence classes must too.

One way to do this is to make an equivalence class out of a code and its image under each A-map.
Thus we want to partition the big tree given by `A_map_rel` into trees of height `1` that each
contains all descendents of its root (this is a slight lie for empty codes as the one equivalence
class they form won't be a tree but rather a complete graph).

This is where code parity kicks in. We recursively pick out the small trees by noticing that codes
whose preimages under A-maps are all in a small tree already (in particular, those that have no
preimage under an A-map) must be the root of their own small tree, and that codes that are a
image of some root of a small tree must belong to that same tree. This motivates the following
definitions:
* A code is even if all its preimages under A-maps are odd.
* A code is odd if one of its preimages under A-maps are even.

If we replace "even" and "odd" by "winning" and "losing", we precisely get the rules for determining
whether a game position is winning or losing.

Note that for nonempty codes there is at most one preimage under A-maps.

## Main declarations

* `con_nf.is_even`, `con_nf.is_odd`: Code parity.
* `con_nf.code.equiv`: Equivalence of codes.
-/

open set with_bot

universe u

namespace con_nf
open params
variables [params.{u}] {α β δ : Λ} {γ : type_index} [phase_1a.{u} α] {hβ : β ≤ α} {hγ: γ < β}
  {hδ : δ < β}

namespace code
variables {c d : code α β hβ}

/-! ### Parity of a code -/

/-- Parity of codes. We define them mutually inductively (`even_odd ff` is evenness, `even_odd
tt` is oddity). If we consider codes as states of a game and `A_map_rel` as the "leads to"
relation, then even codes are precisely losing codes and odd codes are precisely winning codes.
Parity of a nonempty code corresponds to the parity of its number of iterated preimages under
A-maps. The only even empty code is `⊥` one, all others are odd. -/
@[mk_iff] inductive even_odd : bool → code α β hβ → Prop
| intro_even : ∀ c, (∀ d, d ↝ c → even_odd tt d) → even_odd ff c
| intro_odd : ∀ c d, d ↝ c → even_odd ff d → even_odd tt c

/-- A code is even iff it only leads to odd codes. -/
def is_even : code α β hβ → Prop := even_odd false

/-- A code is odd iff it leads to some even code. -/
def is_odd : code α β hβ → Prop := even_odd true

lemma is_even_iff : c.is_even ↔ ∀ d, d ↝ c → d.is_odd := (even_odd_iff _ _).trans $ by simp [is_odd]
lemma is_odd_iff : c.is_odd ↔ ∃ d, d ↝ c ∧ d.is_even := (even_odd_iff _ _).trans $ by simp [is_even]

lemma is_even_of_forall_not (h : ∀ d, ¬ d ↝ c) : is_even c := is_even_iff.2 $ λ d hd, (h _ hd).elim

@[simp] lemma not_is_odd : ¬ c.is_odd ↔ c.is_even := sorry -- use `A_map_rel'_well_founded`
@[simp] lemma not_is_even : ¬ c.is_even ↔ c.is_odd := not_is_odd.symm.not_left

alias not_is_odd ↔ _ is_even.not_is_odd
alias not_is_even ↔ _ is_odd.not_is_even

lemma is_even_or_is_odd (c : code α β hβ) : c.is_even ∨ c.is_odd :=
by { rw ←not_is_even, exact em _ }

@[simp] lemma is_even_of_eq_bot (c : code α β hβ) (hc : c.extension = ⊥) : c.is_even :=
is_even_of_forall_not $ by { rintro d ⟨γ, hγ, -⟩, exact coe_ne_bot hc }

lemma is_even_bot (s : set atom) : is_even (⟨⊥, bot_lt_coe _, s⟩ : code α β hβ) :=
is_even_of_eq_bot _ rfl

@[simp] lemma is_even_empty_iff : is_even (⟨γ, hγ, ∅⟩ : code α β hβ) ↔ γ = ⊥ :=
begin
  refine ⟨λ h, _, is_even_of_eq_bot ⟨γ, hγ, ∅⟩⟩,
  cases γ,
  { refl },
  cases (is_even_bot _).not_is_odd (is_even_iff.1 h ⟨⊥, _, ∅⟩ _),
  convert A_map_rel.intro _ (coe_lt_coe.1 hγ) _,
  exacts [(A_map_empty _).symm, bot_ne_coe],
end

protected lemma _root_.con_nf.A_map_rel.is_odd (hc : c.is_even) (h : c ↝ d) : d.is_odd :=
is_odd_iff.2 ⟨_, h, hc⟩

protected lemma is_even.A_map_code (hc : c.is_even) (hcδ : c.extension ≠ δ) :
  (A_map_code hδ c).is_odd :=
(A_map_rel.intro _ _ hcδ).is_odd hc

protected lemma is_odd.A_map_code (hc : c.is_odd) (hc' : c.elts.nonempty) (hcδ : c.extension ≠ δ) :
  (A_map_code hδ c).is_even :=
is_even_iff.2 $ λ d hd, by rwa (A_map_rel_A_map_code hc' hcδ).1 hd

protected lemma is_even.A_map_code_ne (hc : c.is_even) (hd : d.is_even) (hcδ : c.extension ≠ δ) :
  A_map_code hδ c ≠ d :=
by { rintro rfl, exact hd.not_is_odd (hc.A_map_code hcδ) }

lemma A_map_code_ne_singleton {t} : A_map_code hδ c ≠ ⟨γ, hγ, {t}⟩ :=
begin
  simp only [A_map_code, ne.def, eq_self_iff_true, heq_iff_eq, true_and],
  rintro ⟨rfl, h⟩,
  refine (cardinal.one_lt_aleph_0.trans_le $ κ_regular.aleph_0_le.trans κ_le_μ).not_le _,
  rw [←cardinal.mk_singleton t, ←h.eq],
  exact μ_le_mk_A_map _ (A_map_nonempty.1
    (h.eq.symm ▸ singleton_nonempty _ : (A_map (hδ.trans_le hβ) c.elts).nonempty)),
end

@[simp] lemma is_even_singleton (t) : (⟨γ, hγ, {t}⟩ : code α β hβ).is_even :=
begin
  refine is_even_of_forall_not (λ c hc, _),
  obtain ⟨δ, hδ, hc, h⟩ := (A_map_rel_iff _ _).1 hc,
  exact A_map_code_ne_singleton h.symm,
end

/-! ### Equivalence of codes -/

/-- Equivalence of codes. -/
@[mk_iff] inductive equiv : code α β hβ → code α β hβ → Prop
| refl (c) : equiv c c
| A_map_left (c : code α β hβ) (hc : c.is_even) (γ) (hγ : γ < β) (hcγ : c.extension ≠ γ) :
  equiv (A_map_code hγ c) c
| A_map_right (c : code α β hβ) (hc : c.is_even) (γ) (hγ : γ < β) (hcγ : c.extension ≠ γ) :
  equiv c (A_map_code hγ c)
| A_map_A_map (c : code α β hβ) (hc : c.is_even) (γ) (hγ : γ < β) (hcγ : c.extension ≠ γ)
  (δ) (hδ : δ < β) (hcδ : c.extension ≠ δ) :
    equiv (A_map_code hγ c) (A_map_code hδ c)

/-! We declare new notation for code equivalence. -/
infix ` ≡ `:50 := equiv

attribute [refl] equiv.refl

lemma equiv.rfl : c ≡ c := equiv.refl _

lemma equiv.of_eq : c = d → c ≡ d := by { rintro rfl, refl }

lemma equiv.symm : symmetric ((≡) : code α β hβ → code α β hβ → Prop)
| _ _ (equiv.refl _) := equiv.refl _
| _ _ (equiv.A_map_left c γ hγ hc hcγ) := equiv.A_map_right c γ hγ hc hcγ
| _ _ (equiv.A_map_right c γ hγ hc hcγ) := equiv.A_map_left c γ hγ hc hcγ
| _ _ (equiv.A_map_A_map c hc γ hγ hcγ δ hδ hcδ) := equiv.A_map_A_map c hc δ hδ hcδ γ hγ hcγ

lemma equiv_comm : c ≡ d ↔ d ≡ c := equiv.symm.iff _ _

lemma equiv.trans : ∀ {c d e : code α β hβ}, c ≡ d → d ≡ e → c ≡ e := sorry
-- | _ _ _ (equiv.refl _) _ := ‹_›
-- | _ _ _ _ (equiv.refl _) := ‹_›
-- | _ _ _ (equiv.A_map_left γ hγ _ hcγ _) (equiv.A_map_right δ hδ c hcδ h) := sorry
-- | _ _ _ (equiv.A_map_right c hc γ hγ h) (equiv.A_map_left _ _ _ _ _) := equiv.refl _

lemma equiv_equivalence : equivalence ((≡) : code α β hβ → code α β hβ → Prop) :=
⟨equiv.refl, equiv.symm, λ _ _ _, equiv.trans⟩

lemma equiv.nonempty_iff_nonempty :
  ∀ {c d : code α β hβ}, c ≡ d → (c.elts.nonempty ↔ d.elts.nonempty)
| _ _ (equiv.refl _) := iff.rfl
| _ _ (equiv.A_map_left c hc γ hγ h) := A_map_nonempty
| _ _ (equiv.A_map_right c hc γ hγ h) := A_map_nonempty.symm
| _ _ (equiv.A_map_A_map c hc γ hγ hcγ δ hδ hcδ) := A_map_nonempty.trans A_map_nonempty.symm

lemma equiv.ext : ∀ {c d : code α β hβ}, c ≡ d → c.extension = d.extension → c = d
| _ _ (equiv.refl _) _ := rfl
| _ _ (equiv.A_map_left c hc γ hγ h) H := (h H.symm).elim
| _ _ (equiv.A_map_right c hc γ hγ h) H := (h H).elim
| _ _ (equiv.A_map_A_map c hc γ hγ hcγ δ hδ hcδ) H :=
  by { have : γ = δ := coe_injective H, subst this }

lemma equiv.empty_empty {δ : type_index} (hγ : γ < β) (hδ : δ < β) :
  (⟨γ, hγ, ∅⟩ : code α β hβ) ≡ ⟨δ, hδ, ∅⟩ :=
begin
  cases γ; cases δ,
  { refl },
  { convert equiv.A_map_right _ (is_even_bot _) _ (coe_lt_coe.1 hδ) bot_ne_coe,
    exact (A_map_empty _).symm },
  { convert equiv.A_map_left _ (is_even_bot _) _ (coe_lt_coe.1 hγ) bot_ne_coe,
    exact (A_map_empty _).symm },
  { convert equiv.A_map_A_map _ (is_even_bot ∅) _ (coe_lt_coe.1 hγ) bot_ne_coe
      _ (coe_lt_coe.1 hδ) bot_ne_coe;
        exact (A_map_empty _).symm }
end

lemma singleton_equiv (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (g : tangle α γ _) :
  (⟨γ, hγ, {g}⟩ : code α β hβ) ≡
    ⟨δ, coe_lt_coe.2 hδ, to_tangle δ _ '' local_cardinal (f_map γ δ _ (hδ.trans_le hβ) g)⟩ :=
begin
  convert code.equiv.A_map_right ⟨γ, hγ, {g}⟩ (is_even_singleton _) _ hδ hγδ,
  simp only [mem_singleton_iff, Union_Union_eq_left],
end

lemma equiv_singleton_iff {g} :
  c ≡ ⟨γ, hγ, {g}⟩ ↔
    c = ⟨γ, hγ, {g}⟩ ∨
      ∃ δ (hc : c.extension = some δ) (hδ : δ < β) (hγδ : γ ≠ δ), c = A_map_code hδ ⟨γ, hγ, {g}⟩ :=
begin
  classical,
  refine ⟨λ h, _, _⟩,
  {
    rw equiv_iff at h,
    simp only [A_map_code_ne_singleton.symm, is_even_singleton, true_and, and_false, exists_false,
      or_false] at h,
    obtain rfl | ⟨δ, hδ, hγδ, rfl⟩ := h,
    { exact or.inl rfl },
    { exact or.inr ⟨_, rfl, hδ, hγδ, rfl⟩ } },
  { rintro (rfl | ⟨δ, hc, hδ, hγδ, rfl⟩),
    { refl },
    { convert (singleton_equiv hγ hδ hγδ g).symm,
      simp only [A_map_code, A_map_singleton, eq_self_iff_true, heq_iff_eq, and_self] } }
end

lemma extension_eq_of_singleton_equiv_singleton {δ : type_index} (hγ : γ < β) (hδ : δ < β)
  {a b : tangle α _ _} (h : (⟨γ, hγ, {a}⟩ : code α β hβ) ≡ ⟨δ, hδ, {b}⟩) :
  γ = δ :=
begin
  obtain h | ⟨ε, hc, hε, hγε, hA⟩ := equiv_singleton_iff.1 h,
  { exact ((code.ext_iff _ _).1 h).1 },
  { cases A_map_code_ne_singleton hA.symm }
end

lemma is_even.unique : ∀ {c d : code α β hβ}, c.is_even → d.is_even → c ≡ d → c = d
| c _ _ _ (equiv.refl _) := rfl
| c _ hc hd (equiv.A_map_left d _ γ hγ hdγ) := by cases (hd.A_map_code hdγ).not_is_even hc
| c _ hc hd (equiv.A_map_right d _ γ hγ hcγ) := by cases (hc.A_map_code hcγ).not_is_even hd
| c _ hc hd (equiv.A_map_A_map e he γ hγ hcγ δ hδ _) := by cases (he.A_map_code hcγ).not_is_even hc

lemma exists_even_equiv : ∀ c : code α β hβ, ∃ d ≡ c, d.is_even :=
begin
  rintro ⟨γ, hγ, s⟩,
   obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact ⟨_, equiv.empty_empty _ _, is_even_bot _⟩ },
  obtain heven | hodd := is_even_or_is_odd ⟨γ, hγ, s⟩,
  { exact ⟨_, equiv.rfl, heven⟩ },
  simp_rw [is_odd_iff, A_map_rel_iff] at hodd,
  obtain ⟨d, ⟨δ, hδ, hdδ, hc⟩, hd⟩ := id hodd,
  exact ⟨d, (equiv.A_map_right _ hd _ _ hdδ).trans (equiv.of_eq hc.symm), hd⟩,
end

protected lemma is_even.exists_equiv_extension_eq (hδ : δ < β) (heven : c.is_even) :
  ∃ d ≡ c, d.extension = δ :=
begin
  by_cases c.extension = δ,
  { exact ⟨c, equiv.rfl, h⟩ },
  { exact ⟨A_map_code hδ c, equiv.A_map_left _ heven _ _ h, rfl⟩ }
end

lemma exists_equiv_extension_eq (hδ : δ < β) : ∀ c : code α β hβ, ∃ d ≡ c, d.extension = δ :=
begin
  rintro ⟨γ, hγ, s⟩,
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact ⟨_, equiv.empty_empty (coe_lt_coe.2 hδ) _, rfl⟩ },
  obtain heven | hodd := is_even_or_is_odd ⟨γ, hγ, s⟩,
  { exact heven.exists_equiv_extension_eq hδ },
  simp_rw [is_odd_iff, A_map_rel_iff] at hodd,
  obtain ⟨d, ⟨ε, hε, hdε, hc⟩, hd⟩ := hodd,
  obtain ⟨e, he, heδ⟩ := hd.exists_equiv_extension_eq hδ,
  exact ⟨e, he.trans $ (equiv.A_map_right _ hd _ hε hdε).trans $ equiv.of_eq hc.symm, heδ⟩,
end

lemma equiv.unique : ∀ {c d : code α β hβ}, c ≡ d → c.extension = d.extension → c = d
| c _ (equiv.refl _) _ := rfl
| c _ (equiv.A_map_left d _ γ hγ hdγ) h := by cases hdγ h.symm
| c _ (equiv.A_map_right d _ γ hγ hcγ) h := by cases hcγ h
| c _ (equiv.A_map_A_map e he γ hγ _ δ hδ _) h := by { have : γ = δ := coe_injective h, subst this }

lemma equiv_bot_subsingleton : ∀ d ≡ c, ∀ e ≡ c, d.extension = ⊥ → e.extension = ⊥ → d = e :=
λ d hdc e hec hd he, (hdc.trans hec.symm).unique (hd.trans he.symm)

end code
end con_nf
