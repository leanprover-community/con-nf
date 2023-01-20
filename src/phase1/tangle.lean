import group_theory.group_action.option
import mathlib.group_action
import mathlib.pointwise
import phase1.allowable

noncomputable theory

open function set with_bot
open_locale cardinal pointwise

universe u

namespace con_nf
variables [params.{u}] [position_data.{}]

open code Iio_index

variables (α : Λ) [core_tangle_cumul α] {β : Iio_index α} {γ : Iio α}

namespace semitangle

/-- The possible extensions of a nonempty semitangle. -/
abbreviation extension := Π β : Iio α, tangles (β : Iio_index α)

namespace extension
variables {α} [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- The extensions for a code. -/
protected noncomputable! def extn (s : tangles β) : extension α :=
λ γ, ⟨(A_map_code γ (mk β s)).snd, A_map_code_nonempty.mpr s.2⟩

@[simp] lemma extn_self (s : tangles $ Iio_coe γ) : extension.extn s γ = s :=
begin
  unfold extension.extn,
  refine subtype.ext _,
  simp only [subtype.coe_mk],
  have := A_map_code_mk_eq γ s,
  rw sigma.ext_iff at this,
  exact this.2.eq,
end

lemma extn_of_ne (s : tangles β) (hβγ : β ≠ γ) : extension.extn s γ = ⟨A_map hβγ _, s.2.A_map⟩ :=
begin
  refine subtype.ext _,
  simp only [subtype.coe_mk],
  have := A_map_code_mk_ne β γ hβγ s,
  rw sigma.ext_iff at this,
  exact this.2.eq,
end

end extension

variables [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- Keeps track of the preferred extension of a semitangle, along with coherence conditions
relating each extension of the semitangle. -/
@[nolint has_nonempty_instance] inductive preference (exts : extension α)
| base (atoms : tangles ⊥) :
    (mk ⊥ (atoms : set $ tangle (⊥ : Iio_index α))).is_even →
      (∀ γ, A_map bot_ne_coe (atoms : set $ tangle (⊥ : Iio_index α)) = (exts γ).val) → preference
| proper (β : Iio α) :
    (mk β (show tangles $ Iio_coe β, from exts β) : code α).is_even →
      (∀ (γ : Iio α) (hβγ : Iio_coe β ≠ γ),
        A_map hβγ (show set (tangle $ Iio_coe β), from (exts β).val) = (exts γ).val) →
          preference

variables {α} {members : extension α}

/-- The `-1`-extension associated with a given semitangle extension. -/
def preference.atoms : preference α members → set atom
| (preference.base atoms _ _) := (atoms : set (tangle ⊥))
| (preference.proper _ _ _) := ∅

lemma preference.base_heq_base {m₁ m₂ : extension α} {s₁ s₂ h₁ h₂ h₃ h₄}
  (hm : m₁ = m₂) (hs : s₁ = s₂) :
  (preference.base s₁ h₁ h₂ : preference α m₁) ==
    (preference.base s₂ h₃ h₄ : preference α m₂) :=
by cases hm; cases hs; refl

lemma preference.proper_heq_proper {m₁ m₂ : extension α} {β₁ β₂ h₁ h₂ h₃ h₄}
  (hm : m₁ = m₂) (hs : β₁ = β₂) :
  (preference.proper β₁ h₁ h₂ : preference α m₁) ==
    (preference.proper β₂ h₃ h₄ : preference α m₂) :=
by cases hm; cases hs; refl

end semitangle

open semitangle

variables [positioned_tangle_cumul α] [almost_tangle_cumul α]

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`.

Here, we restrict our definition to just nonempty semitangles; this simplifies the definition. -/
@[nolint has_nonempty_instance]
structure nonempty_semitangle :=
(exts : extension α)
(pref : preference α exts)

namespace nonempty_semitangle
variables {α}

/-- The membership relation for nonempty semitangles. -/
def mem (t : tangle γ) (s : nonempty_semitangle α) : Prop := t ∈ (s.exts γ).val

notation t ` ∈ₙₛₜ `:50 s:50 := mem t s

/-- The even code associated to a nonempty semitangle. -/
def repr_code : nonempty_semitangle α → nonempty_code α
| ⟨exts, preference.base atoms rep hA⟩ := ⟨⟨⊥, atoms⟩, atoms.2⟩
| ⟨exts, preference.proper β rep hA⟩ := ⟨⟨β, exts β⟩, (exts β).2⟩

@[simp] lemma repr_code_base (exts : extension α) (atoms rep hA) :
  repr_code ⟨exts, preference.base atoms rep hA⟩ = ⟨⟨⊥, atoms⟩, atoms.2⟩ := rfl

@[simp] lemma repr_code_proper (exts : extension α) (β rep hA) :
  repr_code ⟨exts, preference.proper β rep hA⟩ = ⟨⟨β, exts β⟩, (exts β).2⟩ := rfl

lemma repr_code_spec : Π (s : nonempty_semitangle α), (repr_code s : code α).is_even
| ⟨exts, preference.proper β rep hA⟩ := rep
| ⟨exts, preference.base atoms rep hA⟩ := rep

lemma repr_code_members_ne :
  Π (s : nonempty_semitangle α) (γ : Iio α) (hcγ : (repr_code s : code α).1 ≠ γ),
  (A_map_code γ (repr_code s)).2 = (s.exts γ : set (tangle $ Iio_coe γ))
| ⟨exts, preference.proper β rep hA⟩ γ hcγ := by rw snd_A_map_code; exact hA _ hcγ
| ⟨exts, preference.base atoms rep hA⟩ γ hcγ := hA _

-- Remark: This formulation of extensionality holds only for types larger than type zero, since
-- it doesn't take into account any `-1`-extension.
lemma ext_core (x y : nonempty_semitangle α) : (∃ γ, γ < α) → x.exts = y.exts → x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp,
  rintro ⟨γ, hγ⟩ rfl,
  have γ : Iio α := ⟨γ, hγ⟩,
  refine congr_arg (λ h, ⟨xs, h⟩) _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨γ, even₂, hA₂⟩ := hys,
  { simp_rw subtype.coe_injective (A_map_injective $ (hA₁ γ).trans (hA₂ _).symm) },
  { cases even₁.A_map_code_ne even₂  bot_ne_mk_coe (sigma.ext_iff.2 ⟨rfl, (hA₁ γ).heq⟩) },
  { cases even₂.A_map_code_ne even₁ bot_ne_mk_coe (sigma.ext_iff.2 ⟨rfl, (hA₂ β).heq⟩) },
  { simp only,
    refine not_ne_iff.1 (λ hβγ, even₂.A_map_code_ne even₁ (Iio.coe_injective.ne hβγ.symm) $
      sigma.ext_iff.2 ⟨rfl, heq_of_eq _⟩),
    rw snd_A_map_code,
    exact hA₂ β (λ h, hβγ.symm (Iio.coe_injective h)) }
end

/-- One useful form of extensionality in tangled type theory. Two nonempty semitangles are equal if
their even codes are equivalent (and hence equal, by uniqueness). -/
lemma ext_code : ∀ {x y : nonempty_semitangle α}, (repr_code x : code α) ≡ repr_code y → x = y
| ⟨x, preference.base atoms₁ even₁ hA₁⟩ ⟨y, preference.base atoms₂ even₂ hA₂⟩ h := begin
  obtain rfl := subtype.coe_injective (code.equiv.bot_bot_iff.1 h),
  obtain rfl : x = y := funext (λ γ, subtype.coe_injective $ (hA₁ _).symm.trans $ hA₂ _),
  refl,
end
| ⟨x, preference.base s even₁ hA₁⟩ ⟨y, preference.proper γ even₂ hA₂⟩ h := begin
  change code.mk _ _ ≡ code.mk _ _ at h,
  obtain ⟨δ, hδ⟩ := (code.equiv.bot_left_iff.1 h).resolve_left
    (ne_of_apply_ne sigma.fst bot_ne_mk_coe),
  rw hδ at even₂,
  cases even₂.not_is_odd (even₁.A_map_code bot_ne_mk_coe),
end
| ⟨x, preference.proper γ even₁ hA₁⟩ ⟨y, preference.base s even₂ hA₂⟩ h := begin
  change code.mk _ _ ≡ code.mk _ _ at h,
  obtain ⟨δ, hδ⟩ := (code.equiv.bot_right_iff.1 h).resolve_left
    (ne_of_apply_ne sigma.fst mk_coe_ne_bot),
  rw hδ at even₁,
  cases even₁.not_is_odd (even₂.A_map_code bot_ne_mk_coe),
end
| ⟨x, preference.proper γ even₁ hA₁⟩ ⟨y, preference.proper δ even₂ hA₂⟩ h := begin
  dsimp at h,
  simp only [code.equiv_iff, sigma.ext_iff, mem_Iio, Iio.coe_inj, ne.def, fst_A_map_code,
    snd_A_map_code, Iio.coe_mk] at h,
  obtain ⟨rfl, h⟩ | ⟨-, γ, hδγ, rfl, h⟩ | ⟨-, δ, hγδ, rfl, h⟩ |
    ⟨c, hc, γ, hcγ, δ, hcδ, ⟨⟨rfl, hx'⟩, hx⟩, _⟩ := h,
  { suffices : x = y,
    { subst this },
    refine funext (λ ε, subtype.coe_injective _),
    obtain rfl | hδε := eq_or_ne δ ε,
    { exact h.eq.symm },
    refine (hA₁ _ (λ h, hδε (Iio.coe_injective h))).symm.trans
      (eq.trans _ $ hA₂ _ (λ h, hδε (Iio.coe_injective h))),
    dsimp,
    rw h.eq },
  { rw h.eq at even₁,
    cases (even₂.A_map_code $ Iio.coe_injective.ne hδγ).not_is_even even₁ },
  { rw h.eq at even₂,
    cases (even₁.A_map_code $ Iio.coe_injective.ne hγδ).not_is_even even₂ },
  { rw hx.eq at even₁,
    cases (hc.A_map_code hcγ).not_is_even even₁ }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `γ < α`.
TODO: This proof can be golfed quite a bit just by cleaning up the `simp` calls. -/
lemma ext (x y : nonempty_semitangle α) (h : x.exts γ = y.exts γ) : x = y :=
begin
  obtain ⟨xs, hxs⟩ := x,
  obtain ⟨ys, hys⟩ := y,
  dsimp only at h,
  refine ext_code _,
  obtain ⟨atoms₁, even₁, hA₁⟩ | ⟨β, even₁, hA₁⟩ := hxs;
    obtain ⟨atoms₂, even₂, hA₂⟩ | ⟨δ, even₂, hA₂⟩ := hys,
  { refine (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _,
    simp only [ne.def, Iio_index.bot_ne_coe, not_false_iff, A_map_code_mk_ne,
      repr_code_base, subtype.coe_mk],
    rw [hA₁ γ, h, ← hA₂ γ],
    exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe },
  { simp only [repr_code_base, subtype.coe_mk, repr_code_proper],
    obtain rfl | hδγ := eq_or_ne δ γ,
    { simp only [is_even_bot, mem_Iio, subtype.val_eq_coe, set_coe.forall,
        ne.def, Iio.coe_inj] at *,
      have := hA₁ δ δ.prop,
      rw subtype.coe_eta at this,
      rw [← h, ← this],
      exact code.equiv.A_map_right _ (code.is_even_bot _) _ bot_ne_mk_coe },
    { refine (code.equiv.A_map_right _ (code.is_even_bot _) γ bot_ne_mk_coe).trans _,
      simp only [ne.def, Iio_index.bot_ne_coe, not_false_iff, A_map_code_mk_ne],
      rw [hA₁ γ, h, ←hA₂ γ (Iio.coe_injective.ne hδγ), ← A_map_code_mk_ne],
      exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ) } },
  { simp only [repr_code_proper, subtype.coe_mk, repr_code_base],
    obtain rfl | hβγ := eq_or_ne β γ,
    { dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall] at *,
      rw [h, ←hA₂ β],
      exact code.equiv.A_map_left _ (code.is_even_bot _) _ bot_ne_mk_coe },
    { refine (code.equiv.A_map_right _ even₁ γ $ Iio.coe_injective.ne hβγ).trans _,
      dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall] at *,
      rw A_map_code_mk_ne _ _ (Iio.coe_injective.ne hβγ),
      rw [hA₁ γ (Iio.coe_injective.ne hβγ), h, ←hA₂ γ],
      exact code.equiv.A_map_left _ (code.is_even_bot _) γ bot_ne_mk_coe } },
  { simp only [repr_code_proper, subtype.coe_mk],
    obtain rfl | hβγ := eq_or_ne β γ,
    { obtain rfl | hδβ := eq_or_ne δ β,
      { rw h },
      { have := A_map_code_ne β (code.mk δ ↑(ys δ)) (Iio.coe_injective.ne hδβ),
        dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall, code.snd_mk] at *,
        rw [h, ←hA₂ _ (Iio.coe_injective.ne hδβ), ← code.mk_def, ← this],
        exact code.equiv.A_map_left _ even₂ _ (Iio.coe_injective.ne hδβ) } },
    obtain rfl | hδγ := eq_or_ne δ γ,
    { have := A_map_code_ne δ (code.mk β ↑(xs β)) (Iio.coe_injective.ne hβγ),
      dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall, code.snd_mk] at *,
      simp_rw [←h, ←hA₁ _ (Iio.coe_injective.ne hβγ), ← code.mk_def, ← this],
      exact code.equiv.A_map_right _ even₁ _ (Iio.coe_injective.ne hβγ) },
    refine (code.equiv.A_map_right _ even₁ γ $ Iio.coe_injective.ne hβγ).trans _,
    have := A_map_code_ne γ (code.mk ↑δ ↑(ys δ)) (Iio.coe_injective.ne hδγ),
    dsimp only [mem_Iio, ne.def, subtype.val_eq_coe, set_coe.forall, code.snd_mk] at *,
    rw A_map_code_ne,
    rw [code.snd_mk, hA₁ γ (Iio.coe_injective.ne hβγ), h, ←hA₂ γ (Iio.coe_injective.ne hδγ)],
    rw ← this,
    exact code.equiv.A_map_left _ even₂ γ (Iio.coe_injective.ne hδγ) }
end

/-- Extensionality in tangled type theory. Two nonempty semitangles are equal if their
`β`-extensions are equal for *any* choice of `β < α`. -/
lemma ext' (x y : nonempty_semitangle α) (h : ∀ t : tangle γ, t ∈ₙₛₜ x ↔ t ∈ₙₛₜ y) : x = y :=
ext x y $ subtype.ext $ set.ext h

/-- Extensionality at the lowest level of tangled type theory.
At type 0, all nonempty semitangles have a `-1`-extension.
Therefore, the extensionality principle in this case applies to the `-1`-extensions. -/
lemma ext_zero (x y : nonempty_semitangle α) (α_zero : is_min α) (h : x.pref.atoms = y.pref.atoms) :
  x = y :=
begin
  obtain ⟨xs, ⟨atoms₁, rep₁, hA₁⟩ | ⟨γ, _, _⟩⟩ := x, swap,
  { cases α_zero.not_lt γ.2 },
  obtain ⟨ys, ⟨atoms₂, rep₂, hA₂⟩ | ⟨γ, _, _⟩⟩ := y, swap,
  { cases α_zero.not_lt γ.2 },
  have : atoms₁ = atoms₂ := subtype.coe_injective h,
  subst this,
  suffices : xs = ys, by subst this,
  ext β -,
  cases α_zero.not_lt β.2,
end

end nonempty_semitangle

/-- A semitangle is either a nonempty semitangle, or the `⊥` element, which is considered the empty
set. Note that in TTT, a set contains no elements at one level if and only if it contains no
elements at all levels. -/
@[reducible] def semitangle := with_bot (nonempty_semitangle α)

variables {α}

namespace semitangle

/-- The membership relation of tangles and semitangles in TTT at this level. -/
def mem (t : tangle γ) (s : semitangle α) := s.elim false $ (∈ₙₛₜ) t

notation t ` ∈ₛₜ `:50 s:50 := mem t s

variables {t : tangle γ} {s : semitangle α}

lemma not_mem_bot (t : tangle γ) : ¬ t ∈ₛₜ ⊥ := id
@[simp] lemma mem_coe {s : nonempty_semitangle α} : t ∈ₛₜ s ↔ t ∈ₙₛₜ s := iff.rfl

lemma eq_bot_of_forall_not_mem (s : semitangle α) (h : ∀ t : tangle γ, ¬ t ∈ₛₜ s) : s = ⊥ :=
begin
  cases s,
  { refl },
  { cases h _ (s.exts _).2.some_spec }
end

lemma ext (x y : semitangle α) : (∀ t : tangle γ, t ∈ₛₜ x ↔ t ∈ₛₜ y) → x = y :=
begin
  intro h,
  cases x,
  { exact (eq_bot_of_forall_not_mem _ $ λ _, (h _).2).symm },
  cases y,
  { exact eq_bot_of_forall_not_mem _ (λ _, (h _).1) },
  rw nonempty_semitangle.ext' x y h,
end

/-- Construct a nonempty semitangle from an even nonempty code. -/
def intro (s : tangles β) (heven : (code.mk β s : code α).is_even) : nonempty_semitangle α :=
⟨extension.extn s, match β, s, heven with
  | ⟨⊥, _⟩, s, _ := preference.base s (code.is_even_bot _) $ λ β, rfl
  | ⟨(γ : Λ), hγ⟩, s, heven := preference.proper ⟨γ, coe_lt_coe.1 hγ⟩
    (by { convert heven, exact extension.extn_self (show tangles (Iio_coe ⟨γ, _⟩), from s) }) $
      λ δ hδ, by { rw extension.extn_of_ne s hδ, congr,
        exact extension.extn_self (show tangles (Iio_coe ⟨γ, _⟩), from s) }
  end⟩

@[simp] lemma exts_intro (s : tangles β) (heven) : (intro s heven).exts = extension.extn s := rfl

end semitangle

open semitangle

variables [core_tangle_data α]

namespace allowable_perm
variables {f : allowable_perm α} {e : extension α}

@[simp] lemma smul_extn (f : allowable_perm α) (s : tangles β) :
  f • extension.extn s = extension.extn (f • s) :=
begin
  funext γ,
  simp only [extension.extn, pi.smul_apply, smul_nonempty_mk],
  by_cases β = γ,
  { subst h,
    have h₁ := congr_arg (λ a, f • a) (A_map_code_mk_eq γ s),
    dsimp only at h₁,
    have h₂ := A_map_code_mk_eq γ (f • s),
    conv_rhs at h₂ { rw ← smul_mk },
    rw ← h₂ at h₁,
    rw sigma.ext_iff at h₁,
    exact h₁.2.eq, },
  { have h₁ := congr_arg (λ a, f • a) (A_map_code_mk_ne β γ h s),
    dsimp only at h₁,
    have h₂ := A_map_code_mk_ne β γ h (f • s),
    rw [smul_mk, smul_A_map] at h₁,
    rw ← h₂ at h₁,
    rw sigma.ext_iff at h₁,
    exact h₁.2.eq, },
end

set_option trace.simp_lemmas true
lemma smul_aux₁ {s : tangles (⊥ : Iio_index α)}
  (h : ∀ (γ : Iio α), A_map bot_ne_coe (s : set (tangle (⊥ : Iio_index α))) =
    (e γ : set (tangle (Iio_coe γ)))) (γ : Iio α) :
  A_map bot_ne_coe (↑(f • s)) = ((f • e) γ : set (tangle (Iio_coe γ))) :=
by simpa only [smul_A_map] using congr_arg (λ c, f • c) (h γ)

lemma smul_aux₂ (h : ∀ (δ : Iio α) (hγδ : Iio_coe γ ≠ δ),
  A_map hγδ (e γ) = (e δ : set (tangle (Iio_coe δ)))) (δ : Iio α) (hγδ : Iio_coe γ ≠ δ) :
  A_map hγδ ((f • e) γ).val = ((f • e) δ).val :=
by simpa only [smul_A_map] using congr_arg (λ c, f • c) (h δ hγδ)

/-- Allowable permutations act on nonempty semitangles. -/
instance : has_smul (allowable_perm α) (nonempty_semitangle α) :=
{ smul := λ f t, ⟨f • t.exts, begin
    obtain ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩ := t,
    { exact preference.base (f • s) (code.is_even_bot _) (smul_aux₁ h) },
    { exact preference.proper _ ht.smul (smul_aux₂ h) }
    end⟩ }

@[simp] lemma members_smul (f : allowable_perm α) (s : nonempty_semitangle α) :
  (f • s).exts = f • s.exts := rfl

@[simp] lemma smul_base (f : allowable_perm α) (e : extension α) (s ht h) :
  f • (⟨e, preference.base s ht h⟩ : nonempty_semitangle α) =
    ⟨f • e, preference.base (f • s) (code.is_even_bot _) (smul_aux₁ h)⟩ := rfl

@[simp] lemma smul_proper (f : allowable_perm α) (e : extension α) (γ ht h) :
  f • (⟨e, preference.proper γ ht h⟩ : nonempty_semitangle α) =
    ⟨f • e, preference.proper _ ht.smul (smul_aux₂ h)⟩ := rfl

instance mul_action_nonempty_semitangle : mul_action (allowable_perm α) (nonempty_semitangle α) := {
  one_smul := begin
    rintro ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩,
    { rw smul_base,
      simp only [one_smul, eq_self_iff_true, true_and],
      refine preference.base_heq_base _ _,
      rw one_smul,
      ext : 1,
      refine (coe_smul_nonempty _ _).trans _,
      rw one_smul },
    { rw smul_proper,
      simp only [one_smul, eq_self_iff_true, true_and],
      refine semitangle.preference.proper_heq_proper _ rfl,
      rw one_smul },
  end,
  mul_smul := begin
    rintro f g ⟨exts, ⟨s, ht, h⟩ | ⟨γ, ht, h⟩⟩,
    { simp only [smul_base, mul_smul, eq_self_iff_true, true_and],
      refine preference.base_heq_base _ _,
      rw mul_smul,
      ext : 1,
      refine (coe_smul_nonempty _ _).trans _,
      rw mul_smul,
      refl },
    { simp only [smul_proper, mul_smul, eq_self_iff_true, true_and],
      refine semitangle.preference.proper_heq_proper _ rfl,
      rw mul_smul },
  end
}

/-- Allowable permutations act on semitangles. -/
instance mul_action_semitangle : mul_action (allowable_perm α) (semitangle α) := option.mul_action

end allowable_perm

variables (α)

/-- A tangle at the new level `α` is a semitangle supported by a small support.
This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
@[nolint has_nonempty_instance]
def new_tangle := {s : semitangle α // supported α (allowable_perm α) s}

variables {α} {c d : code α} {S : set (support_condition α)}

open mul_action

/-- If a set of support conditions supports a code, it supports all equivalent codes. -/
protected lemma code.equiv.supports (hcd : c ≡ d) (hS : supports (allowable_perm α) S c) :
  supports (allowable_perm α) S d :=
λ f h, (hcd.symm.smul.trans $ (code.equiv.of_eq $ hS f h).trans hcd).unique rfl

lemma code.equiv.supports_iff (hcd : c ≡ d) :
  supports (allowable_perm α) S c ↔ supports (allowable_perm α) S d :=
⟨hcd.supports, hcd.symm.supports⟩

/-- If two codes are equivalent, one is supported if and only if the other is. -/
lemma code.equiv.small_supported_iff (hcd : c ≡ d) :
  supported α (allowable_perm α) c ↔ supported α (allowable_perm α) d :=
⟨λ ⟨⟨s, hs, h⟩⟩, ⟨⟨s, hs, hcd.supports h⟩⟩, λ ⟨⟨s, hs, h⟩⟩, ⟨⟨s, hs, hcd.symm.supports h⟩⟩⟩

@[simp] lemma smul_intro (f : allowable_perm α) (s : tangles β) (hs) :
  f • intro s hs = intro (f • s) hs.smul :=
begin
  cases β,
  induction β_val using with_bot.rec_bot_coe,
  { simp only [intro, allowable_perm.smul_base, allowable_perm.smul_extn,
      eq_self_iff_true, true_and],
    refine preference.base_heq_base _ rfl,
    rw allowable_perm.smul_extn },
  { simp only [intro, allowable_perm.smul_proper, allowable_perm.smul_extn,
      eq_self_iff_true, true_and],
    refine preference.proper_heq_proper _ rfl,
    rw allowable_perm.smul_extn }
end

-- TODO: Move next two lemmas elsewhere.
lemma allowable_to_struct_perm_bot (π : allowable (⊥ : Iio_index α)) :
  core_tangle_data.allowable_to_struct_perm π = struct_perm.to_bot_iso.to_monoid_hom π := rfl

lemma _root_.semiallowable_perm.to_allowable_bot (π : semiallowable_perm α) :
  semiallowable_perm.to_allowable ⊥ π = struct_perm.to_near_litter_perm
    (semiallowable_perm.to_struct_perm π) :=
begin
  unfold semiallowable_perm.to_allowable semiallowable_perm.to_struct_perm
    struct_perm.to_near_litter_perm struct_perm.lower allowable.to_struct_perm,
  rw dif_neg with_bot.bot_ne_coe,
  simp only [monoid_hom.coe_mk, monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom,
    comp_app, struct_perm.of_coe_to_coe, allowable_to_struct_perm_bot, mul_equiv.symm_apply_apply],
  refl,
end

/-- For any near-litter `N`, the code `(α, -1, N)` is a tangle at level `α`.
This is called a *typed near litter*. -/
def new_typed_near_litter (N : near_litter) : new_tangle α :=
⟨some $ intro ⟨(show set (tangle (⊥ : Iio_index α)), from N.2.1), N.2.2.nonempty⟩ $
  code.is_even_bot _, ⟨⟨{(sum.inr N, default)}, small_singleton _, λ π h, begin
    simp only [subtype.val_eq_coe, option.smul_some, smul_intro, option.some_inj],
    have := show (struct_perm.lower (bot_lt_coe α).le (semiallowable_perm.to_struct_perm ↑π)) •
      sum.inr N = sum.inr N, from congr_arg prod.fst (h rfl),
    simp only [sum.smul_inr] at this,
    have : π • N = N := this,
    conv_rhs { rw ← this },
    congr' 1,
    ext : 1,
    simp only [coe_smul_nonempty, subtype.coe_mk, allowable_perm.snd_smul_near_litter],
    unfold has_smul.smul has_smul.comp.smul,
    simp only [semiallowable_perm.to_allowable_bot (allowable_perm.coe_hom π)],
  end⟩⟩⟩

/-- For any supported tangle `x`, the code `(α, β, {x})` is a tangle at level `α`. -/
def supported_singleton (x : tangle β) (supp : supported α (allowable_perm α) x) :
  new_tangle α :=
⟨some $ intro ⟨{x}, singleton_nonempty _⟩ (code.is_even_singleton _), begin
  unfreezingI { obtain ⟨s, hs₁, hs₂⟩ := supp },
  refine ⟨⟨s, hs₁, λ π h, _⟩⟩,
  conv_rhs { rw ← hs₂ π h },
  simp only [smul_set_singleton, smul_nonempty_mk, option.smul_some, smul_intro],
  refl,
end⟩

/-- For any small set `B` of supported `β`-tangles, the code `(α, β, B)` is a tangle at level `α` if
it is even. -/
def supported_set (s : tangles β) (hs : small (s : set $ tangle β)) (hc : (mk β s).is_even)
  (symm : ∀ b ∈ (s : set $ tangle β), supported α (allowable_perm α) b) :
  new_tangle α :=
⟨some $ intro s hc, begin
  have symm : Π b ∈ (s : set $ tangle β), support α (allowable_perm α) b,
  { intros b hb, exact (symm b hb).some },
  refine ⟨⟨⋃ b ∈ (s : set $ tangle β), symm b ‹_›, hs.bUnion (λ i hi, (symm _ _).small), λ π h, _⟩⟩,
  suffices : π • s = s,
  { simp only [option.smul_some, smul_intro, option.some_inj, this] },
  have : ∀ x ∈ (s : set $ tangle β), π • x = x,
  { intros x hx,
    refine (symm x hx).supports π _,
    intros a ha,
    refine h _,
    simp only [mem_Union, set_like.mem_coe],
    refine ⟨x, hx, ha⟩ },
  ext : 2,
  refine ⟨λ hx, _, λ hx, _⟩,
  { have := this (π⁻¹ • x) _,
    { rw smul_inv_smul at this,
      rw this,
      rwa ←mem_smul_set_iff_inv_smul_mem },
    { rwa ←mem_smul_set_iff_inv_smul_mem } },
  { rw ← this x hx,
    exact smul_mem_smul_set hx }
end⟩

variables {α}

namespace new_tangle

instance : has_coe (new_tangle α) (semitangle α) := coe_subtype

lemma coe_injective : injective (coe : new_tangle α → semitangle α) := subtype.coe_injective

end new_tangle

namespace allowable_perm

/-- Allowable permutations act on `α`-tangles. -/
--Yaël: I suspect we can generalize `supports.smul` so that it applies here
instance has_smul_new_tangle : has_smul (allowable_perm α) (new_tangle α) :=
⟨λ π t, ⟨π • t, t.2.map $ λ s, { carrier := π • s, small := s.2.image, supports := begin
  intros σ h,
  have := s.supports (π⁻¹ * σ * π) _,
  { conv_rhs { rw [← subtype.val_eq_coe, ← this, ← mul_smul, ← mul_assoc, ← mul_assoc,
      mul_inv_self, one_mul, mul_smul] },
    refl },
  { intros a ha,
    rw [mul_smul, mul_smul, inv_smul_eq_iff],
    exact h (smul_mem_smul_set ha) },
end }⟩⟩

@[simp, norm_cast] lemma coe_smul_new_tangle (f : allowable_perm α) (t : new_tangle α) :
  (↑(f • t) : semitangle α) = f • t := rfl

instance mul_action_new_tangle : mul_action (allowable_perm α) (new_tangle α) :=
new_tangle.coe_injective.mul_action _ coe_smul_new_tangle

end allowable_perm

/-
namespace nonempty_semitangle

def to_pretangle (t : nonempty_semitangle α) : pretangle α :=
pretangle.mk t.pref.atoms (λ β hβ, pretangle_inj β hβ ''
  (t.exts β hβ : set (tangle α β $ coe_lt_coe.mpr hβ)))

lemma to_pretangle_ne_empty (t : nonempty_semitangle α) :
  to_pretangle α t ≠ pretangle.mk ∅ (λ β hβ, ∅) :=
begin
  by_cases hzero : ∃ β, β < α,
  { obtain ⟨β, hβ⟩ := hzero,
    intro h,
    have := congr_arg pretangle.extension h,
    rw pretangle.extension_mk at this,
    have := congr_fun₂ this β hβ,
    rw [to_pretangle, pretangle.extension_mk, set.image_eq_empty] at this,
    exact (t.exts β hβ).prop.ne_empty this },
  { intro h,
    have := congr_arg pretangle.atom_extension h,
    rw [to_pretangle, pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    obtain ⟨ts, ⟨atoms, rep, hA⟩ | ⟨β, hβ, rep, hA⟩⟩ := t,
    { exact atoms.2.ne_empty this },
    { exfalso, exact hzero ⟨β, hβ⟩ } }
end

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst, unfold to_pretangle at hst,
  by_cases h : is_min α,
  { have := congr_arg pretangle.atom_extension hst,
    rw [pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    exact ext_zero _ _ h this },
  { obtain ⟨β, hβ⟩ := not_is_min_iff.1 h,
    have := congr_arg pretangle.extension hst,
    rw [pretangle.extension_mk, pretangle.extension_mk] at this,
    have := congr_fun₂ this β hβ,
    rw set.image_eq_image (embedding.injective _) at this,
    exact ext _ _ _ (subtype.coe_inj.mp this) }
end

end nonempty_semitangle

namespace semitangle

def to_pretangle : semitangle α → pretangle α
| ⊥ := pretangle.mk ∅ (λ β hβ, ∅)
| (t : nonempty_semitangle α) := nonempty_semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst,
  induction s using with_bot.rec_bot_coe; induction t using with_bot.rec_bot_coe,
  { refl },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst.symm },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst },
  { rw nonempty_semitangle.to_pretangle_injective α hst }
end

end semitangle

namespace new_tangle

def to_pretangle (t : new_tangle α) : pretangle α := semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
λ s t hst, subtype.coe_inj.mp (semitangle.to_pretangle_injective α hst)

end new_tangle
-/
end con_nf
