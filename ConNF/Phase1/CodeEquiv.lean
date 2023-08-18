import ConNF.Phase1.AMap

#align_import phase1.code_equiv

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


open Set WithBot

universe u

namespace ConNF

variable [Params.{u}] [PositionData] {α : Λ} {β : IioBot α} {γ : Iio α} [CoreTangleCumul α]
  [AlmostTangleCumul α] [PositionedTangleCumul α]

open IioIndex

namespace Code

variable {c d : Code α}

/-! ### Parity of a code -/


/-- Parity of codes. We define them mutually inductively (`even_odd ff` is evenness, `even_odd tt`
is oddity). If we consider codes as states of a game and `A_map_rel` as the "leads to"
relation, then even codes are precisely losing codes and odd codes are precisely winning codes.
Parity of a nonempty code corresponds to the parity of its number of iterated preimages under
A-maps. The only even empty code is `⊥` one, all others are odd. -/
@[mk_iff]
inductive EvenOdd : Bool → Code α → Prop
  | intro_even : ∀ c, (∀ d, d ↝ c → even_odd true d) → even_odd false c
  | intro_odd : ∀ c d, d ↝ c → even_odd false d → even_odd true c

/-- A code is even iff it only leads to odd codes. -/
def IsEven : Code α → Prop :=
  EvenOdd False

/-- A code is odd iff it leads to some even code. -/
def IsOdd : Code α → Prop :=
  EvenOdd True

theorem isEven_iff : c.IsEven ↔ ∀ d, d ↝ c → d.IsOdd :=
  (evenOdd_iff _ _).trans <| by simp [is_odd]

theorem isOdd_iff : c.IsOdd ↔ ∃ d, d ↝ c ∧ d.IsEven :=
  (evenOdd_iff _ _).trans <| by simp [is_even]

theorem isEvenOfForallNot (h : ∀ d, ¬d ↝ c) : IsEven c :=
  isEven_iff.2 fun d hd => (h _ hd).elim

@[simp]
theorem isEvenOfEqBot (c : Code α) (hc : c.1.1 = ⊥) : c.IsEven :=
  isEvenOfForallNot <| by rintro d ⟨β, -⟩; exact coe_ne_bot hc

@[simp]
theorem isEvenBot (s : Set Atom) : IsEven (mk ⊥ s : Code α) :=
  isEvenOfEqBot _ rfl

theorem not_isOdd_bot (s : Set Atom) : ¬IsOdd (mk ⊥ s : Code α) :=
  by
  simp_rw [is_odd_iff, A_map_rel_iff]
  rintro ⟨d, ⟨γ, hdγ, h⟩, hd⟩
  exact bot_ne_mk_coe (congr_arg Sigma.fst h)

@[simp]
theorem IsEmpty.isEven_iff (hc : c.isEmpty) : IsEven c ↔ (c.1 : TypeIndex) = ⊥ :=
  by
  refine' ⟨fun h => _, is_even_of_eq_bot _⟩
  obtain ⟨⟨_ | β, hβ⟩, s⟩ := c
  · rfl
  cases not_is_odd_bot _ (is_even_iff.1 h ⟨⟨⊥, _⟩, ∅⟩ _)
  convert A_map_rel.intro ⟨β, coe_lt_coe.1 hβ⟩ _ <;> simp
  assumption

@[simp]
theorem IsEmpty.isOdd_iff (hc : c.isEmpty) : IsOdd c ↔ (c.1 : TypeIndex) ≠ ⊥ :=
  by
  obtain ⟨⟨β, hβ⟩, s⟩ := c
  refine' ⟨_, fun h => is_odd_iff.2 ⟨mk ⊥ ∅, _, is_even_bot _⟩⟩
  · rintro h (rfl : β = _)
    exact not_is_odd_bot _ h
  · lift β to Λ using h
    rw [show s = _ from hc.eq]
    exact (A_map_rel_iff _ _).2 ⟨⟨β, coe_lt_coe.1 hβ⟩, bot_ne_mk_coe, by simpa using hc.eq⟩

@[simp]
theorem isEven_empty_iff : IsEven (mk β ∅) ↔ (β : TypeIndex) = ⊥ :=
  IsEmpty.isEven_iff rfl

@[simp]
theorem isOdd_empty_iff : IsOdd (mk β ∅) ↔ (β : TypeIndex) ≠ ⊥ :=
  IsEmpty.isOdd_iff rfl

private theorem not_is_odd_nonempty : ∀ c : NonemptyCode α, ¬c.1.IsOdd ↔ c.1.IsEven
  | c => by
    rw [is_odd_iff, is_even_iff]
    push_neg
    apply forall_congr' fun d => _
    apply imp_congr_right fun h => _
    rw [Iff.comm, ← not_iff_not, Classical.not_not]
    obtain hd | hd := d.2.eq_empty_or_nonempty
    · rw [is_empty.is_odd_iff hd, is_empty.is_even_iff hd, Classical.not_not]
    · let this.1 : A_map_rel' ⟨d, hd⟩ c := A_map_rel_coe_coe.1 h
      exact @not_is_odd_nonempty ⟨d, hd⟩

@[simp]
theorem not_isOdd : ¬c.IsOdd ↔ c.IsEven :=
  by
  obtain hc | hc := c.2.eq_empty_or_nonempty
  · rw [is_empty.is_odd_iff hc, is_empty.is_even_iff hc, Classical.not_not]
  · exact not_is_odd_nonempty ⟨c, hc⟩

@[simp]
theorem not_isEven : ¬c.IsEven ↔ c.IsOdd :=
  not_isOdd.symm.not_left

alias not_is_odd ↔ _ is_even.not_is_odd

alias not_is_even ↔ _ is_odd.not_is_even

theorem isEven_or_isOdd (c : Code α) : c.IsEven ∨ c.IsOdd := by rw [← not_is_even]; exact em _

protected theorem ConNF.AMapRel.isOdd (hc : c.IsEven) (h : c ↝ d) : d.IsOdd :=
  isOdd_iff.2 ⟨_, h, hc⟩

protected theorem IsEven.aMapCode (hc : c.IsEven) (hcγ : c.1 ≠ γ) : (aMapCode γ c).IsOdd :=
  (AMapRel.intro _ hcγ).IsOdd hc

protected theorem IsOdd.aMapCode (hc : c.IsOdd) (hc' : c.2.Nonempty) (hcγ : c.1 ≠ γ) :
    (aMapCode γ c).IsEven :=
  isEven_iff.2 fun d hd => by rwa [(A_map_rel_A_map_code _ hc' hcγ).1 hd]

protected theorem IsEven.aMapCode_ne (hc : c.IsEven) (hd : d.IsEven) (hcγ : c.1 ≠ γ) :
    aMapCode γ c ≠ d := by rintro rfl; exact hd.not_is_odd (hc.A_map_code hcγ)

theorem aMapCode_ne_bot {s} : aMapCode γ c ≠ mk ⊥ s :=
  ne_of_apply_ne (Subtype.val ∘ Sigma.fst) coe_ne_bot

theorem aMapCode_ne_singleton {t} (hcβ : c.1 ≠ β) : aMapCode γ c ≠ mk β {t} :=
  by
  simp only [A_map_code, Ne.def, eq_self_iff_true, heq_iff_eq, true_and_iff, Sigma.ext_iff, fst_mk,
    snd_mk]
  rintro ⟨rfl, h⟩
  refine' (cardinal.one_lt_aleph_0.trans_le <| κ_regular.aleph_0_le.trans κ_le_μ).not_le _
  rw [← Cardinal.mk_singleton t, ← h.eq]
  refine' μ_le_mk_A_map_code c hcβ (A_map_code_nonempty.1 _)
  exact γ
  rw [A_map_code, eq_of_hEq h]
  simp only [snd_mk, singleton_nonempty]

@[simp]
theorem isEvenSingleton (t) : (mk β {t}).IsEven :=
  by
  refine' is_even_of_forall_not fun c hc => _
  obtain ⟨γ, hc', h⟩ := (A_map_rel_iff _ _).1 hc
  have := congr_arg Sigma.fst h
  cases this
  exact A_map_code_ne_singleton hc' h.symm

/-! ### Equivalence of codes -/


/-- Equivalence of codes. -/
@[mk_iff]
inductive Equiv : Code α → Code α → Prop
  | refl (c) : Equiv c c
  | A_map_left (c : Code α) (hc : c.IsEven) (β : Iio α) (hcβ : c.1 ≠ β) : Equiv (aMapCode β c) c
  | A_map_right (c : Code α) (hc : c.IsEven) (β : Iio α) (hcβ : c.1 ≠ β) : Equiv c (aMapCode β c)
  |
  A_map_A_map (c : Code α) (hc : c.IsEven) (β : Iio α) (hcβ : c.1 ≠ β) (γ : Iio α) (hcγ : c.1 ≠ γ) :
    Equiv (aMapCode β c) (aMapCode γ c)

/-! We declare new notation for code equivalence. -/


infixl:50 " ≡ " => Equiv

namespace Equiv

attribute [refl] refl

protected theorem rfl : c ≡ c :=
  refl _

theorem ofEq : c = d → c ≡ d := by rintro rfl; rfl

theorem symm : Symmetric ((· ≡ ·) : Code α → Code α → Prop)
  | _, _, refl _ => refl _
  | _, _, A_map_left c β hc hcβ => A_map_right c β hc hcβ
  | _, _, A_map_right c β hc hcβ => A_map_left c β hc hcβ
  | _, _, A_map_A_map c hc β hcβ γ hcγ => A_map_A_map c hc γ hcγ β hcβ

theorem comm : c ≡ d ↔ d ≡ c :=
  symm.Iff _ _

theorem emptyEmpty : ∀ β γ, (⟨β, ∅⟩ : Code α) ≡ ⟨γ, ∅⟩
  | ⟨⊥, _⟩, ⟨⊥, _⟩ => Equiv.rfl
  | ⟨⊥, _⟩, ⟨(γ : Λ), hγ⟩ =>
    by
    convert A_map_right _ (is_even_bot _) ⟨_, coe_lt_coe.1 hγ⟩ bot_ne_mk_coe
    rw [extension_ne _ _ bot_ne_coe, snd_mk, A_map_empty]
  | ⟨(β : Λ), hβ⟩, ⟨⊥, _⟩ =>
    by
    convert A_map_left _ (is_even_bot _) ⟨_, coe_lt_coe.1 hβ⟩ bot_ne_mk_coe
    rw [extension_ne _ _ bot_ne_coe, snd_mk, A_map_empty]
  | ⟨(β : Λ), hβ⟩, ⟨(γ : Λ), hγ⟩ => by
    convert
        A_map_A_map _ (is_even_bot ∅) ⟨_, coe_lt_coe.1 hβ⟩ bot_ne_mk_coe ⟨_, coe_lt_coe.1 hγ⟩
          bot_ne_mk_coe <;>
      rw [extension_ne _ _ bot_ne_coe, snd_mk, A_map_empty]

protected theorem ConNF.Code.IsEmpty.equiv (hc : c.isEmpty) (hd : d.isEmpty) : c ≡ d :=
  by
  cases c; cases d; change c_snd = ∅ at hc ; change d_snd = ∅ at hd ; subst hc; subst hd
  exact equiv.empty_empty _ _

theorem trans {c d e : Code α} : c ≡ d → d ≡ e → c ≡ e :=
  by
  rw [equiv_iff, equiv_iff]
  rintro (rfl | ⟨hc, β, hcβ, rfl⟩ | ⟨hc, β, hcβ, rfl⟩ | ⟨d, hd, γ, hdγ, ε, hdε, rfl, rfl⟩)
  · exact (equiv_iff _ _).2
  · rintro (rfl | ⟨hc', γ, hcγ, rfl⟩ | ⟨-, γ, hcγ, rfl⟩ | ⟨_, hc', γ, hcγ, ε, hcε, rfl, rfl⟩)
    · exact A_map_left _ hc β hcβ
    · cases (hc'.A_map_code hcγ).not_isEven hc
    · exact A_map_A_map _ hc _ hcβ _ hcγ
    · cases (hc'.A_map_code hcγ).not_isEven hc
  · rintro (rfl | ⟨hc', γ, hcγ, hce⟩ | ⟨hc', γ, hcγ, rfl⟩ | ⟨e, he, γ, hcγ, ε, heε, hce, rfl⟩)
    · exact A_map_right _ hc β hcβ
    · obtain h | h := c.2.eq_empty_or_nonempty
      · refine' is_empty.equiv h _
        rwa [← A_map_code_is_empty, ← hce, A_map_code_is_empty, code.is_empty]
      · exact of_eq (eq_of_A_map_code h hcβ hcγ hce)
    · cases (hc.A_map_code hcβ).not_isEven hc'
    · obtain h | h := c.2.eq_empty_or_nonempty
      · refine' is_empty.equiv h _
        rwa [A_map_code_is_empty, ← A_map_code_is_empty, ← hce, A_map_code_is_empty, code.is_empty]
      · rw [eq_of_A_map_code h hcβ hcγ hce]
        exact A_map_right _ he _ heε
  · rintro (rfl | ⟨he, γ, heγ, hde⟩ | ⟨hd', γ, -, rfl⟩ | ⟨e, he, ι, heι, κ, heκ, hde, rfl⟩)
    · exact A_map_A_map _ hd _ hdγ _ hdε
    · obtain h | h := e.2.eq_empty_or_nonempty
      · refine' is_empty.equiv _ h
        rwa [A_map_code_is_empty, ← A_map_code_is_empty, hde, A_map_code_is_empty, code.is_empty]
      · rw [eq_of_A_map_code h heγ hdε hde.symm]
        exact A_map_left _ hd _ hdγ
    · cases (hd.A_map_code hdε).not_isEven hd'
    · obtain h | h := d.2.eq_empty_or_nonempty
      · refine' (is_empty.A_map_code h).Equiv _
        rwa [A_map_code_is_empty, ← A_map_code_is_empty, ← hde, A_map_code_is_empty, code.is_empty]
      · have := eq_of_A_map_code h hdε heι hde
        subst this
        exact A_map_A_map _ hd _ hdγ _ heκ

theorem equiv_equivalence : Equivalence ((· ≡ ·) : Code α → Code α → Prop) :=
  ⟨refl, symm, fun _ _ _ => trans⟩

theorem nonempty_iff : ∀ {c d : Code α}, c ≡ d → (c.2.Nonempty ↔ d.2.Nonempty)
  | _, _, refl _ => Iff.rfl
  | _, _, A_map_left c hc β h => aMapCode_nonempty
  | _, _, A_map_right c hc β h => aMapCode_nonempty.symm
  | _, _, A_map_A_map c hc β hcβ γ hcγ => aMapCode_nonempty.trans aMapCode_nonempty.symm

theorem ext : ∀ {c d : Code α}, c ≡ d → c.1 = d.1 → c = d
  | _, _, refl _, _ => rfl
  | _, _, A_map_left c hc β h, H => (h H.symm).elim
  | _, _, A_map_right c hc β h, H => (h H).elim
  | _, _, A_map_A_map c hc β hcβ γ hcγ, H => by simp only [fst_A_map_code, Iio.coe_inj] at H ;
    subst H

@[simp]
theorem bot_left_iff {s} :
    mk ⊥ s ≡ c ↔ mk ⊥ s = c ∨ ∃ β : Iio α, c = mk β (aMap IioBot.bot_ne_coe s) := by
  simp [equiv_iff, A_map_code_ne_bot.symm, eq_comm]

@[simp]
theorem bot_right_iff {s} :
    c ≡ mk ⊥ s ↔ c = mk ⊥ s ∨ ∃ β : Iio α, c = mk β (aMap IioBot.bot_ne_coe s) := by
  simp [equiv_iff, A_map_code_ne_bot.symm, eq_comm]

@[simp]
theorem bot_bot_iff {s t} : (mk ⊥ s : Code α) ≡ mk ⊥ t ↔ s = t := by
  simp [equiv_iff, A_map_code_ne_bot.symm, eq_comm, Sigma.ext_iff]

theorem singleton (hβγ : β ≠ γ) (g : Tangle β) :
    mk β {g} ≡ mk γ (typedNearLitter '' localCardinal (fMap (coe_ne hβγ) g)) :=
  by
  convert equiv.A_map_right (mk β {g}) (is_even_singleton _) _ hβγ
  rw [extension, dif_neg]
  simp only [snd_mk, A_map_singleton]

theorem singleton_iff {g} :
    c ≡ mk β {g} ↔
      c = mk β {g} ∨ ∃ γ : Iio α, (c.1 : TypeIndex) = some γ ∧ β ≠ γ ∧ c = aMapCode γ (mk β {g}) :=
  by
  classical
  refine' ⟨fun h => _, _⟩
  · rw [equiv_iff] at h
    simp only [mem_Iio, is_even_singleton, fst_mk, Ne.def, SetCoe.exists, Iio.coe_mk,
      true_and_iff] at h
    obtain rfl | ⟨γ, hβγ, hcβ, rfl⟩ | ⟨hc, γ, hγ, γne, h⟩ | ⟨d, hd, γ, hγ, γne, δ, hδ, δne, -, h⟩ :=
      h
    · exact Or.inl rfl
    · simp only [Subtype.coe_mk, SetCoe.exists, exists_and_left]
      exact Or.inr ⟨_, rfl, hβγ, hcβ, rfl⟩
    · cases congr_arg Sigma.fst h
      cases A_map_code_ne_singleton γne h.symm
    · cases congr_arg Sigma.fst h
      cases A_map_code_ne_singleton δne h.symm
  · rintro (rfl | ⟨γ, hc, hβγ, rfl⟩)
    · rfl
    · convert (singleton hβγ g).symm
      simp only [snd_mk, A_map_code, extension_ne _ _ hβγ, A_map_singleton]

end Equiv

theorem extension_eq_of_singleton_equiv_singleton {γ : Iio ↑α} {a b}
    (h : (⟨β, {a}⟩ : Code α) ≡ ⟨γ, {b}⟩) : β = γ :=
  by
  obtain h | ⟨ε, hc, hβε, hA⟩ := equiv.singleton_iff.1 h
  · exact (Sigma.ext_iff.1 h).1
  · cases A_map_code_ne_singleton _ hA.symm
    cases congr_arg Sigma.fst hA
    exact hβε

theorem IsEven.unique : ∀ {c d : Code α}, c.IsEven → d.IsEven → c ≡ d → c = d
  | c, _, _, _, Equiv.refl _ => rfl
  | c, _, hc, hd, equiv.A_map_left d _ β hdβ => by cases (hd.A_map_code hdβ).not_isEven hc
  | c, _, hc, hd, equiv.A_map_right d _ β hcβ => by cases (hc.A_map_code hcβ).not_isEven hd
  | c, _, hc, hd, equiv.A_map_A_map e he β hcβ γ _ => by cases (he.A_map_code hcβ).not_isEven hc

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (d «expr ≡ » c) -/
theorem exists_even_equiv : ∀ c : Code α, ∃ (d : _) (_ : d ≡ c), d.IsEven :=
  by
  rintro ⟨β, s⟩
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨_, equiv.empty_empty _ _, is_even_bot _⟩
  obtain heven | hodd := is_even_or_is_odd ⟨β, s⟩
  · exact ⟨_, equiv.rfl, heven⟩
  simp_rw [is_odd_iff, A_map_rel_iff] at hodd
  obtain ⟨d, ⟨γ, hdγ, hc⟩, hd⟩ := id hodd
  exact ⟨d, (equiv.A_map_right _ hd _ hdγ).trans (equiv.of_eq hc.symm), hd⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (d «expr ≡ » c) -/
protected theorem IsEven.exists_equiv_extension_eq (heven : c.IsEven) :
    ∃ (d : _) (_ : d ≡ c), d.1 = γ := by
  by_cases c.1 = γ
  · exact ⟨c, equiv.rfl, h⟩
  · exact ⟨A_map_code γ c, equiv.A_map_left _ heven _ h, rfl⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (d «expr ≡ » c) -/
theorem exists_equiv_extension_eq : ∀ c : Code α, ∃ (d : _) (_ : d ≡ c), d.1 = γ :=
  by
  rintro ⟨β, s⟩
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨_, equiv.empty_empty _ _, rfl⟩
  obtain heven | hodd := is_even_or_is_odd ⟨β, s⟩
  · exact heven.exists_equiv_extension_eq
  simp_rw [is_odd_iff, A_map_rel_iff] at hodd
  obtain ⟨d, ⟨ε, hdε, hc⟩, hd⟩ := hodd
  obtain ⟨e, he, heγ⟩ := hd.exists_equiv_extension_eq
  exact ⟨e, he.trans <| (equiv.A_map_right _ hd _ hdε).trans <| equiv.of_eq hc.symm, heγ⟩

theorem Equiv.unique : ∀ {c d : Code α}, c ≡ d → c.1 = d.1 → c = d
  | c, _, Equiv.refl _, _ => rfl
  | c, _, equiv.A_map_left d _ β hdβ, h => by cases hdβ h.symm
  | c, _, equiv.A_map_right d _ β hcβ, h => by cases hcβ h
  | c, _, equiv.A_map_A_map e he β _ γ _, h => by have : β = γ := Iio.coe_injective h; subst this

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (d «expr ≡ » c) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (e «expr ≡ » c) -/
theorem equiv_bot_subsingleton : ∀ (d) (_ : d ≡ c), ∀ (e) (_ : e ≡ c), d.1 = ⊥ → e.1 = ⊥ → d = e :=
  fun d hdc e hec hd he => (hdc.trans hec.symm).unique (hd.trans he.symm)

end Code

end ConNF
