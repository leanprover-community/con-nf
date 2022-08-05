import phase1.A_map

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
variables [params.{u}] {α : Λ} {β : Iio (α : type_index)} {γ : Iio α} [core_tangle_cumul α]
  [almost_tangle_cumul α] [positioned_tangle_cumul α]

namespace code
variables {c d : code α}

/-! ### Parity of a code -/

/-- Parity of codes. We define them mutually inductively (`even_odd ff` is evenness, `even_odd tt`
is oddity). If we consider codes as states of a game and `A_map_rel` as the "leads to"
relation, then even codes are precisely losing codes and odd codes are precisely winning codes.
Parity of a nonempty code corresponds to the parity of its number of iterated preimages under
A-maps. The only even empty code is `⊥` one, all others are odd. -/
@[mk_iff] inductive even_odd : bool → code α → Prop
| intro_even : ∀ c, (∀ d, d ↝ c → even_odd tt d) → even_odd ff c
| intro_odd : ∀ c d, d ↝ c → even_odd ff d → even_odd tt c

/-- A code is even iff it only leads to odd codes. -/
def is_even : code α → Prop := even_odd false

/-- A code is odd iff it leads to some even code. -/
def is_odd : code α → Prop := even_odd true

lemma is_even_iff : c.is_even ↔ ∀ d, d ↝ c → d.is_odd := (even_odd_iff _ _).trans $ by simp [is_odd]
lemma is_odd_iff : c.is_odd ↔ ∃ d, d ↝ c ∧ d.is_even := (even_odd_iff _ _).trans $ by simp [is_even]

lemma is_even_of_forall_not (h : ∀ d, ¬ d ↝ c) : is_even c := is_even_iff.2 $ λ d hd, (h _ hd).elim

@[simp] lemma is_even_of_eq_bot (c : code α) (hc : c.1.1 = ⊥) : c.is_even :=
is_even_of_forall_not $ by { rintro d ⟨β, -⟩, exact coe_ne_bot hc }

@[simp] lemma is_even_bot (s : set atom) : is_even (mk ⊥ s : code α) := is_even_of_eq_bot _ rfl

lemma not_is_odd_bot (s : set atom) : ¬ is_odd (mk ⊥ s : code α) :=
begin
  simp_rw [is_odd_iff, A_map_rel_iff],
  rintro ⟨d, ⟨γ, hdγ, h⟩, hd⟩,
  exact bot_ne_mk_coe (congr_arg sigma.fst h),
end

@[simp] lemma is_empty.is_even_iff (hc : c.is_empty) : is_even c ↔ (c.1 : type_index) = ⊥ :=
begin
  refine ⟨λ h, _, is_even_of_eq_bot _⟩,
  obtain ⟨⟨_ | β, hβ⟩, s⟩ := c,
  { refl },
  cases not_is_odd_bot _ (is_even_iff.1 h ⟨⟨⊥, _⟩, ∅⟩ _),
  convert A_map_rel.intro ⟨β, coe_lt_coe.1 hβ⟩ _; simp,
  assumption,
end

@[simp] lemma is_empty.is_odd_iff (hc : c.is_empty) : is_odd c ↔ (c.1 : type_index) ≠ ⊥ :=
begin
  obtain ⟨⟨β, hβ⟩, s⟩ := c,
  refine ⟨_, λ h, is_odd_iff.2 ⟨mk ⊥ ∅, _, is_even_bot _⟩⟩,
  { rintro h (rfl : β = _),
    exact not_is_odd_bot _ h },
  { lift β to Λ using h,
    rw (show s = _, from hc.eq),
    exact (A_map_rel_iff _ _).2 ⟨⟨β, coe_lt_coe.1 hβ⟩, bot_ne_mk_coe, by simpa using hc.eq⟩ }
end

@[simp] lemma is_even_empty_iff : is_even (mk β ∅) ↔ (β : type_index) = ⊥ :=
is_empty.is_even_iff rfl

@[simp] lemma is_odd_empty_iff : is_odd (mk β ∅) ↔ (β : type_index) ≠ ⊥ := is_empty.is_odd_iff rfl

private lemma not_is_odd_nonempty : ∀ c : nonempty_code α, ¬ c.1.is_odd ↔ c.1.is_even
| c := begin
  rw [is_odd_iff, is_even_iff],
  push_neg,
  apply forall_congr (λ d, _),
  apply imp_congr_right (λ h, _),
  rw [iff.comm, ←not_iff_not, not_not],
  obtain hd | hd := d.2.eq_empty_or_nonempty,
  { rw [is_empty.is_odd_iff hd, is_empty.is_even_iff hd, not_not] },
  { let : A_map_rel' ⟨d, hd⟩ c := A_map_rel_coe_coe.1 h,
    exact @not_is_odd_nonempty ⟨d, hd⟩ }
end
using_well_founded { dec_tac := `[assumption] }

@[simp] lemma not_is_odd : ¬ c.is_odd ↔ c.is_even :=
begin
  obtain hc | hc := c.2.eq_empty_or_nonempty,
  { rw [is_empty.is_odd_iff hc, is_empty.is_even_iff hc, not_not] },
  { exact not_is_odd_nonempty ⟨c, hc⟩ }
end

@[simp] lemma not_is_even : ¬ c.is_even ↔ c.is_odd := not_is_odd.symm.not_left

alias not_is_odd ↔ _ is_even.not_is_odd
alias not_is_even ↔ _ is_odd.not_is_even

lemma is_even_or_is_odd (c : code α) : c.is_even ∨ c.is_odd := by { rw ←not_is_even, exact em _ }

protected lemma _root_.con_nf.A_map_rel.is_odd (hc : c.is_even) (h : c ↝ d) : d.is_odd :=
is_odd_iff.2 ⟨_, h, hc⟩

protected lemma is_even.A_map_code (hc : c.is_even) (hcγ : c.1 ≠ γ) : (A_map_code γ c).is_odd :=
(A_map_rel.intro _ hcγ).is_odd hc

protected lemma is_odd.A_map_code (hc : c.is_odd) (hc' : c.2.nonempty) (hcγ : c.1 ≠ γ) :
  (A_map_code γ c).is_even :=
is_even_iff.2 $ λ d hd, by rwa (A_map_rel_A_map_code _ hc' hcγ).1 hd

protected lemma is_even.A_map_code_ne (hc : c.is_even) (hd : d.is_even) (hcγ : c.1 ≠ γ) :
  A_map_code γ c ≠ d :=
by { rintro rfl, exact hd.not_is_odd (hc.A_map_code hcγ) }

lemma A_map_code_ne_bot {s} : A_map_code γ c ≠ mk ⊥ s :=
ne_of_apply_ne (subtype.val ∘ sigma.fst) coe_ne_bot

lemma A_map_code_ne_singleton {t} : A_map_code γ c ≠ mk β {t} :=
begin
  simp only [A_map_code, ne.def, eq_self_iff_true, heq_iff_eq, true_and, sigma.ext_iff, fst_mk,
    snd_mk],
  rintro ⟨rfl, h⟩,
  refine (cardinal.one_lt_aleph_0.trans_le $ κ_regular.aleph_0_le.trans κ_le_μ).not_le _,
  rw [←cardinal.mk_singleton t, ←h.eq],
  exact μ_le_mk_A_map (A_map_nonempty.1
    (h.eq.symm ▸ singleton_nonempty _ : (A_map γ c.2).nonempty)),
end

@[simp] lemma is_even_singleton (t) : (mk β {t}).is_even :=
begin
  refine is_even_of_forall_not (λ c hc, _),
  obtain ⟨γ, hc, h⟩ := (A_map_rel_iff _ _).1 hc,
  exact A_map_code_ne_singleton h.symm,
end

/-! ### Equivalence of codes -/

/-- Equivalence of codes. -/
@[mk_iff] inductive equiv : code α → code α → Prop
| refl (c) : equiv c c
| A_map_left (c : code α) (hc : c.is_even) (β : Iio α) (hcβ : c.1 ≠ β) :
  equiv (A_map_code β c) c
| A_map_right (c : code α) (hc : c.is_even) (β : Iio α) (hcβ : c.1 ≠ β) :
  equiv c (A_map_code β c)
| A_map_A_map (c : code α) (hc : c.is_even) (β : Iio α) (hcβ : c.1 ≠ β) (γ : Iio α)
  (hcγ : c.1 ≠ γ) :
    equiv (A_map_code β c) (A_map_code γ c)

/-! We declare new notation for code equivalence. -/
infix ` ≡ `:50 := equiv

namespace equiv

attribute [refl] refl

protected lemma rfl : c ≡ c := refl _

lemma of_eq : c = d → c ≡ d := by { rintro rfl, refl }

lemma symm : symmetric ((≡) : code α → code α → Prop)
| _ _ (refl _) := refl _
| _ _ (A_map_left c β hc hcβ) := A_map_right c β hc hcβ
| _ _ (A_map_right c β hc hcβ) := A_map_left c β hc hcβ
| _ _ (A_map_A_map c hc β hcβ γ hcγ) := A_map_A_map c hc γ hcγ β hcβ

lemma comm : c ≡ d ↔ d ≡ c := symm.iff _ _

lemma empty_empty : ∀ (β γ), (⟨β, ∅⟩ : code α) ≡ ⟨γ, ∅⟩
| ⟨⊥, _⟩ ⟨⊥, _⟩ := equiv.rfl
| ⟨⊥, _⟩ ⟨(γ : Λ), hγ⟩ := by { convert A_map_right _ (is_even_bot _) ⟨_, coe_lt_coe.1 hγ⟩
      bot_ne_mk_coe,
    simp only [A_map_empty, snd_mk] }
| ⟨(β : Λ), hβ⟩  ⟨⊥, _⟩ := by { convert A_map_left _ (is_even_bot _) ⟨_, coe_lt_coe.1 hβ⟩
      bot_ne_mk_coe,
    simp only [A_map_empty, snd_mk] }
| ⟨(β : Λ), hβ⟩ ⟨(γ : Λ), hγ⟩ := by
  { convert A_map_A_map _ (is_even_bot ∅) ⟨_, coe_lt_coe.1 hβ⟩ bot_ne_mk_coe ⟨_, coe_lt_coe.1 hγ⟩
      bot_ne_mk_coe;
    simp only [A_map_empty, snd_mk] }

protected lemma _root_.con_nf.code.is_empty.equiv (hc : c.is_empty) (hd : d.is_empty) : c ≡ d :=
by { cases c, cases d, change c_snd = ∅ at hc, change d_snd = ∅ at hd, subst hc, subst hd,
  exact equiv.empty_empty _ _ }

lemma trans {c d e : code α} : c ≡ d → d ≡ e → c ≡ e :=
begin
  rw [equiv_iff, equiv_iff],
  rintro (rfl | ⟨hc, β, hcβ, rfl⟩ | ⟨hc, β, hcβ, rfl⟩ | ⟨d, hd, γ, hdγ, ε, hdε, rfl, rfl⟩),
  { exact (equiv_iff _ _).2 },
  { rintro (rfl | ⟨hc', γ, hcγ, rfl⟩ | ⟨-, γ, hcγ, rfl⟩ | ⟨_, hc', γ, hcγ, ε, hcε, rfl, rfl⟩),
    { exact A_map_left _ hc β hcβ },
    { cases (hc'.A_map_code hcγ).not_is_even hc },
    { exact A_map_A_map _ hc _ hcβ _ hcγ },
    { cases (hc'.A_map_code hcγ).not_is_even hc } },
  { rintro (rfl | ⟨hc', γ, hcγ, hce⟩ | ⟨hc', γ, hcγ, rfl⟩ |
      ⟨e, he, γ, hcγ, ε, heε, hce, rfl⟩),
    { exact A_map_right _ hc β hcβ },
    { obtain h | h := c.2.eq_empty_or_nonempty,
      { refine is_empty.equiv h _,
        rwa [←A_map_code_is_empty, ←hce, A_map_code_is_empty, code.is_empty] },
      { exact of_eq (eq_of_A_map_code h hcβ hcγ hce) } },
    { cases (hc.A_map_code hcβ).not_is_even hc' },
    { obtain h | h := c.2.eq_empty_or_nonempty,
      { refine is_empty.equiv h _,
        rwa [A_map_code_is_empty, ←A_map_code_is_empty, ←hce, A_map_code_is_empty, code.is_empty] },
      { rw eq_of_A_map_code h hcβ hcγ hce,
        exact A_map_right _ he _ heε } } },
  { rintro (rfl | ⟨he, γ, heγ, hde⟩ | ⟨hd', γ, -, rfl⟩ | ⟨e, he, ι, heι, κ, heκ, hde, rfl⟩),
    { exact A_map_A_map _ hd _ hdγ _ hdε },
    { obtain h | h := e.2.eq_empty_or_nonempty,
      { refine is_empty.equiv _ h,
        rwa [A_map_code_is_empty, ←A_map_code_is_empty, hde, A_map_code_is_empty, code.is_empty] },
      { rw eq_of_A_map_code h heγ hdε hde.symm,
        exact A_map_left _ hd _ hdγ } },
    { cases (hd.A_map_code hdε).not_is_even hd' },
    { obtain h | h := d.2.eq_empty_or_nonempty,
      { refine (is_empty.A_map_code h).equiv _,
        rwa [A_map_code_is_empty, ←A_map_code_is_empty, ←hde, A_map_code_is_empty, code.is_empty] },
      { have := eq_of_A_map_code h hdε heι hde,
        subst this,
        exact A_map_A_map _ hd _ hdγ _ heκ } } }
end

lemma equiv_equivalence : equivalence ((≡) : code α → code α → Prop) :=
⟨refl, symm, λ _ _ _, trans⟩

lemma nonempty_iff : ∀ {c d : code α}, c ≡ d → (c.2.nonempty ↔ d.2.nonempty)
| _ _ (refl _) := iff.rfl
| _ _ (A_map_left c hc β h) := A_map_nonempty
| _ _ (A_map_right c hc β h) := A_map_nonempty.symm
| _ _ (A_map_A_map c hc β hcβ γ hcγ) := A_map_nonempty.trans A_map_nonempty.symm

lemma ext : ∀ {c d : code α}, c ≡ d → c.1 = d.1 → c = d
| _ _ (refl _) _ := rfl
| _ _ (A_map_left c hc β h) H := (h H.symm).elim
| _ _ (A_map_right c hc β h) H := (h H).elim
| _ _ (A_map_A_map c hc β hcβ γ hcγ) H :=
  by { simp only [fst_A_map_code, Iio.coe_inj] at H, subst H }

@[simp] lemma bot_left_iff {s} : mk ⊥ s ≡ c ↔ mk ⊥ s = c ∨ ∃ β : Iio α, c = mk β (A_map β s) :=
by simp [equiv_iff, A_map_code_ne_bot.symm, eq_comm]

@[simp] lemma bot_right_iff {s} : c ≡ mk ⊥ s ↔ c = mk ⊥ s ∨ ∃ β : Iio α, c = mk β (A_map β s) :=
by simp [equiv_iff, A_map_code_ne_bot.symm, eq_comm]

@[simp] lemma bot_bot_iff {s t} : (mk ⊥ s : code α) ≡ mk ⊥ t ↔ s = t :=
by simp [equiv_iff, A_map_code_ne_bot.symm, eq_comm, sigma.ext_iff]

lemma singleton (hβγ : β ≠ γ) (g : tangle β) :
  mk β {g} ≡ mk γ (to_tangle '' local_cardinal (f_map γ g)) :=
begin
  convert equiv.A_map_right (mk β {g}) (is_even_singleton _) _ hβγ,
  simp only [snd_mk, mem_singleton_iff, Union_Union_eq_left],
end

lemma singleton_iff {g} :
  c ≡ mk β {g} ↔ c = mk β {g} ∨ ∃ γ : Iio α, (c.1 : type_index) = some γ ∧ β ≠ γ ∧
    c = A_map_code γ (mk β {g}) :=
begin
  classical,
  refine ⟨λ h, _, _⟩,
  { rw equiv_iff at h,
    simp only [A_map_code_ne_singleton.symm, is_even_singleton, true_and, and_false, exists_false,
      or_false] at h,
    obtain rfl | ⟨γ, hβγ, rfl⟩ := h,
    { exact or.inl rfl },
    { exact or.inr ⟨_, rfl, hβγ, rfl⟩ } },
  { rintro (rfl | ⟨γ, hc, hβγ, rfl⟩),
    { refl },
    { convert (singleton hβγ g).symm,
      simp only [snd_mk, A_map_code, A_map_singleton, eq_self_iff_true, heq_iff_eq, and_self] } }
end

end equiv

lemma extension_eq_of_singleton_equiv_singleton {γ : Iio ↑α} {a b}
  (h : (⟨β, {a}⟩ : code α) ≡ ⟨γ, {b}⟩) : β = γ :=
begin
  obtain h | ⟨ε, hc, hβε, hA⟩ := equiv.singleton_iff.1 h,
  { exact (sigma.ext_iff.1 h).1 },
  { cases A_map_code_ne_singleton hA.symm }
end

lemma is_even.unique : ∀ {c d : code α}, c.is_even → d.is_even → c ≡ d → c = d
| c _ _ _ (equiv.refl _) := rfl
| c _ hc hd (equiv.A_map_left d _ β hdβ) := by cases (hd.A_map_code hdβ).not_is_even hc
| c _ hc hd (equiv.A_map_right d _ β hcβ) := by cases (hc.A_map_code hcβ).not_is_even hd
| c _ hc hd (equiv.A_map_A_map e he β hcβ γ _) := by cases (he.A_map_code hcβ).not_is_even hc

lemma exists_even_equiv : ∀ c : code α, ∃ d ≡ c, d.is_even :=
begin
  rintro ⟨β, s⟩,
   obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact ⟨_, equiv.empty_empty _ _, is_even_bot _⟩ },
  obtain heven | hodd := is_even_or_is_odd ⟨β, s⟩,
  { exact ⟨_, equiv.rfl, heven⟩ },
  simp_rw [is_odd_iff, A_map_rel_iff] at hodd,
  obtain ⟨d, ⟨γ, hdγ, hc⟩, hd⟩ := id hodd,
  exact ⟨d, (equiv.A_map_right _ hd _ hdγ).trans (equiv.of_eq hc.symm), hd⟩,
end

protected lemma is_even.exists_equiv_extension_eq (heven : c.is_even) : ∃ d ≡ c, d.1 = γ :=
begin
  by_cases c.1 = γ,
  { exact ⟨c, equiv.rfl, h⟩ },
  { exact ⟨A_map_code γ c, equiv.A_map_left _ heven _ h, rfl⟩ }
end

lemma exists_equiv_extension_eq : ∀ c : code α, ∃ d ≡ c, d.1 = γ :=
begin
  rintro ⟨β, s⟩,
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact ⟨_, equiv.empty_empty _ _, rfl⟩ },
  obtain heven | hodd := is_even_or_is_odd ⟨β, s⟩,
  { exact heven.exists_equiv_extension_eq },
  simp_rw [is_odd_iff, A_map_rel_iff] at hodd,
  obtain ⟨d, ⟨ε, hdε, hc⟩, hd⟩ := hodd,
  obtain ⟨e, he, heγ⟩ := hd.exists_equiv_extension_eq,
  exact ⟨e, he.trans $ (equiv.A_map_right _ hd _ hdε).trans $ equiv.of_eq hc.symm, heγ⟩,
end

lemma equiv.unique : ∀ {c d : code α}, c ≡ d → c.1 = d.1 → c = d
| c _ (equiv.refl _) _ := rfl
| c _ (equiv.A_map_left d _ β hdβ) h := by cases hdβ h.symm
| c _ (equiv.A_map_right d _ β hcβ) h := by cases hcβ h
| c _ (equiv.A_map_A_map e he β _ γ _) h := by { have : β = γ := Iio.coe_injective h, subst this }

lemma equiv_bot_subsingleton : ∀ d ≡ c, ∀ e ≡ c, d.1 = ⊥ → e.1 = ⊥ → d = e :=
λ d hdc e hec hd he, (hdc.trans hec.symm).unique (hd.trans he.symm)

end code
end con_nf
