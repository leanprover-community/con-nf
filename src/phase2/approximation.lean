import mathlib.logic.equiv.local_perm
import phase2.flexible
import phase2.sublitter

open set sum
open_locale cardinal pointwise

universe u

namespace con_nf
variable [params.{u}]

/-!
# Near-litter approximations
-/

@[ext] structure near_litter_approx :=
(atom_perm : local_perm atom)
(litter_perm : local_perm litter)
(domain_small : ∀ L, small (litter_set L ∩ atom_perm.domain))

namespace near_litter_approx

instance : has_smul near_litter_approx atom := ⟨λ π, π.atom_perm⟩
instance : has_smul near_litter_approx litter := ⟨λ π, π.litter_perm⟩

variables (π : near_litter_approx)

lemma smul_atom_eq {a : atom} : π.atom_perm a = π • a := rfl
lemma smul_litter_eq {L : litter} : π.litter_perm L = π • L := rfl

@[simp] lemma mk_smul_atom {atom_perm : local_perm atom} {litter_perm : local_perm litter}
  {domain_small : ∀ L, small (litter_set L ∩ atom_perm.domain)} {a : atom} :
  { near_litter_approx . atom_perm := atom_perm,
    litter_perm := litter_perm, domain_small := domain_small } • a = atom_perm a := rfl

@[simp] lemma mk_smul_litter {atom_perm : local_perm atom} {litter_perm : local_perm litter}
  {domain_small : ∀ L, small (litter_set L ∩ atom_perm.domain)} {L : litter} :
  { near_litter_approx . atom_perm := atom_perm,
    litter_perm := litter_perm, domain_small := domain_small } • L = litter_perm L := rfl

lemma smul_eq_smul_atom {a₁ a₂ : atom}
  (h₁ : a₁ ∈ π.atom_perm.domain) (h₂ : a₂ ∈ π.atom_perm.domain) :
  π • a₁ = π • a₂ ↔ a₁ = a₂ :=
begin
  unfold has_smul.smul,
  rw [← π.atom_perm.eq_symm_apply h₁ (π.atom_perm.map_domain h₂), local_perm.left_inv _ h₂],
end

lemma smul_eq_smul_litter {L₁ L₂ : litter}
  (h₁ : L₁ ∈ π.litter_perm.domain) (h₂ : L₂ ∈ π.litter_perm.domain) :
  π • L₁ = π • L₂ ↔ L₁ = L₂ :=
begin
  unfold has_smul.smul,
  rw [← π.litter_perm.eq_symm_apply h₁ (π.litter_perm.map_domain h₂), local_perm.left_inv _ h₂],
end

def symm : near_litter_approx := {
  atom_perm := π.atom_perm.symm,
  litter_perm := π.litter_perm.symm,
  domain_small := π.domain_small,
}

@[simp] lemma symm_atom_perm : π.symm.atom_perm = π.atom_perm.symm := rfl
@[simp] lemma symm_litter_perm : π.symm.litter_perm = π.litter_perm.symm := rfl

@[simp] lemma left_inv_atom {a} : a ∈ π.atom_perm.domain → π.symm • π • a = a :=
π.atom_perm.left_inv

@[simp] lemma left_inv_litter {L} : L ∈ π.litter_perm.domain → π.symm • π • L = L :=
π.litter_perm.left_inv

@[simp] lemma right_inv_atom {a} : a ∈ π.atom_perm.domain → π • π.symm • a = a :=
π.atom_perm.right_inv

@[simp] lemma right_inv_litter {L} : L ∈ π.litter_perm.domain → π • π.symm • L = L :=
π.litter_perm.right_inv

lemma symm_smul_atom_eq_iff {a b} :
  a ∈ π.atom_perm.domain → b ∈ π.atom_perm.domain → (π.symm • a = b ↔ a = π • b) :=
begin
  intros ha hb,
  split,
  { rintro rfl,
    exact (π.right_inv_atom ha).symm, },
  { rintro rfl,
    exact π.left_inv_atom hb, },
end

lemma symm_smul_litter_eq_iff {L₁ L₂} :
  L₁ ∈ π.litter_perm.domain → L₂ ∈ π.litter_perm.domain → (π.symm • L₁ = L₂ ↔ L₁ = π • L₂) :=
begin
  intros hL₁ hL₂,
  split,
  { rintro rfl,
    exact (π.right_inv_litter hL₁).symm, },
  { rintro rfl,
    exact π.left_inv_litter hL₂, },
end

lemma eq_symm_apply_atom {a₁ a₂} : a₁ ∈ π.atom_perm.domain → a₂ ∈ π.atom_perm.domain →
  (a₁ = π.symm • a₂ ↔ π • a₁ = a₂) := π.atom_perm.eq_symm_apply

lemma eq_symm_apply_litter {L₁ L₂} : L₁ ∈ π.litter_perm.domain → L₂ ∈ π.litter_perm.domain →
  (L₁ = π.symm • L₂ ↔ π • L₁ = L₂) := π.litter_perm.eq_symm_apply

lemma near_litter_domain_small (N : near_litter) : small ((N : set atom) ∩ π.atom_perm.domain) :=
begin
  rw [← symm_diff_symm_diff_cancel_left (litter_set N.fst) N, inter_symm_diff_distrib_right],
  exact small.symm_diff (π.domain_small N.fst) (small.mono (inter_subset_left _ _) N.2.prop),
end

section generate

variables (π)

/-- Gives the largest sublitter of `π` on which `π.atom_perm` is not defined. -/
def largest_sublitter (L : litter) : sublitter := {
  litter := L,
  carrier := litter_set L \ π.atom_perm.domain,
  subset := diff_subset _ _,
  diff_small := by simpa only [sdiff_sdiff_right_self, inf_eq_inter] using π.domain_small L,
}

@[simp] lemma largest_sublitter_litter (L : litter) : (π.largest_sublitter L).litter = L := rfl
@[simp] lemma coe_largest_sublitter (L : litter) :
  (π.largest_sublitter L : set atom) = litter_set L \ π.atom_perm.domain := rfl

lemma mem_largest_sublitter_of_not_mem_domain (a : atom) (h : a ∉ π.atom_perm.domain) :
  a ∈ π.largest_sublitter a.1 := ⟨rfl, h⟩

lemma not_mem_domain_of_mem_largest_sublitter {a : atom} {L : litter}
  (h : a ∈ π.largest_sublitter L) : a ∉ π.atom_perm.domain := h.2

/-- Computes the action of `π` on this sublitter, assuming it is in `sublitter_domain`. -/
def generate_sublitter (S : sublitter) : sublitter := π.largest_sublitter (π • S.litter)

def sublitter_domain : set sublitter :=
{S | S.litter ∈ π.litter_perm.domain ∧ (S : set atom) = litter_set S.litter \ π.atom_perm.domain}

lemma mem_sublitter_domain (S : sublitter) (h : S ∈ π.sublitter_domain) :
  (S : set atom) = litter_set S.litter \ π.atom_perm.domain :=
h.2

lemma generate_sublitter_mem_domain ⦃S : sublitter⦄ (h : S ∈ sublitter_domain π) :
  generate_sublitter π S ∈ sublitter_domain π :=
⟨π.litter_perm.map_domain h.1, rfl⟩

lemma generate_sublitter_left_inv ⦃S : sublitter⦄ (h : S ∈ sublitter_domain π) :
  generate_sublitter π.symm (generate_sublitter π S) = S :=
begin
  ext : 1,
  simp only [h.2, largest_sublitter, generate_sublitter, symm_atom_perm, local_perm.symm_domain,
    sublitter.coe_mk, π.left_inv_litter h.1],
end

/-- Generates the unique near-litter approximation given by an atom local permutation and a
near-litter local permutation. This uniqueness is only up to evaluating everything on the domain
of the permutation. -/
def generate_sublitter_perm : local_perm sublitter := {
  to_fun := generate_sublitter π,
  inv_fun := generate_sublitter π.symm,
  domain := sublitter_domain π,
  to_fun_domain' := generate_sublitter_mem_domain π,
  inv_fun_domain' := generate_sublitter_mem_domain π.symm,
  left_inv' := generate_sublitter_left_inv π,
  right_inv' := generate_sublitter_left_inv π.symm,
}

@[simp] lemma generate_symm :
  (generate_sublitter_perm π).symm = generate_sublitter_perm π.symm := rfl

@[simp] lemma generate_sublitter_perm_domain :
  (generate_sublitter_perm π).domain = sublitter_domain π := rfl

@[simp] lemma generate_sublitter_apply (S : sublitter) :
  generate_sublitter_perm π S = generate_sublitter π S := rfl

instance : has_smul near_litter_approx sublitter := ⟨λ π, π.generate_sublitter_perm⟩

@[simp] lemma smul_sublitter (S : sublitter) :
  (π • S).litter = π • S.litter := rfl

lemma smul_eq_smul_sublitter {S₁ S₂ : sublitter}
  (h₁ : S₁ ∈ sublitter_domain π) (h₂ : S₂ ∈ sublitter_domain π) :
  π • S₁ = π • S₂ ↔ S₁ = S₂ :=
begin
  unfold has_smul.smul,
  rw [← π.generate_sublitter_perm.eq_symm_apply h₁ (π.generate_sublitter_perm.map_domain h₂),
    local_perm.left_inv _ _],
  exact h₂,
end

@[simp] lemma left_inv_sublitter {S} : S ∈ π.sublitter_domain → π.symm • π • S = S :=
π.generate_sublitter_perm.left_inv

@[simp] lemma right_inv_sublitter {S} : S ∈ π.sublitter_domain → π • π.symm • S = S :=
π.generate_sublitter_perm.right_inv

lemma eq_symm_apply_sublitter {S₁ S₂} : S₁ ∈ π.sublitter_domain →
  S₂ ∈ π.sublitter_domain → (S₁ = π.symm • S₂ ↔ π • S₁ = S₂) :=
π.generate_sublitter_perm.eq_symm_apply

/-- Computes the action of `π` on this near-litter. This action is not injective.
The nicest properties will hold when `N` is a litter. -/
def generate_near_litter (π : near_litter_approx) (N : near_litter) : near_litter :=
⟨π • N.1, π.largest_sublitter (π • N.1) ∪ π • (N \ π.largest_sublitter N.1), begin
  refine small.union _ _,
  { rw ← diff_diff,
    exact small.mono (diff_subset _ _) (π.largest_sublitter (π • N.1)).diff_small, },
  { rw union_diff_distrib,
    refine small.union _ _,
    { have := (π.largest_sublitter (π • N.1)).subset,
      rw [largest_sublitter_litter, sublitter.carrier_eq_coe] at this,
      rw diff_eq_empty.mpr this,
      exact small_empty, },
    { refine small.mono (diff_subset _ _) (small.image _),
      have := small.union (small.mono (subset_union_right _ _) N.2.prop)
        (π.largest_sublitter N.1).diff_small,
      simp only [largest_sublitter_litter, sublitter.carrier_eq_coe] at this,
      refine small.mono _ this,
      intros a ha,
      by_cases a ∈ litter_set N.fst,
      exact or.inr ⟨h, ha.2⟩,
      exact or.inl ⟨ha.1, h⟩, }, },
end⟩

instance : has_smul near_litter_approx near_litter := ⟨generate_near_litter⟩

@[simp] lemma smul_near_litter_coe (π : near_litter_approx) (N : near_litter) :
  ((π • N : near_litter) : set atom) =
    π.largest_sublitter (π • N.1) ∪ π • (N \ π.largest_sublitter N.1) := rfl

end generate

def _root_.con_nf.near_litter_perm.is_exception (π : near_litter_perm) (a : atom) : Prop :=
π • a ∉ litter_set (π • a.1) ∨ π⁻¹ • a ∉ litter_set (π⁻¹ • a.1)

@[mk_iff] structure approximates (π₀ : near_litter_approx) (π : near_litter_perm) : Prop :=
(map_atom : ∀ a, a ∈ π₀.atom_perm.domain → π₀ • a = π • a)
(map_litter : ∀ L, L ∈ π₀.litter_perm.domain → π₀ • L = π • L)

lemma approximates.symm_map_atom {π₀ : near_litter_approx} {π : near_litter_perm}
  (hπ : π₀.approximates π) (a : atom) (ha : a ∈ π₀.atom_perm.domain) : π₀.symm • a = π⁻¹ • a :=
begin
  have := hπ.map_atom (π₀.symm • a) (π₀.symm.atom_perm.map_domain ha),
  rw ← inv_smul_eq_iff at this,
  rw [← this, smul_left_cancel_iff],
  exact (π₀.atom_perm).right_inv ha,
end

lemma approximates.symm_map_litter {π₀ : near_litter_approx} {π : near_litter_perm}
  (hπ : π₀.approximates π) (L : litter) (hL : L ∈ π₀.litter_perm.domain) : π₀.symm • L = π⁻¹ • L :=
begin
  have := hπ.map_litter (π₀.symm • L) (π₀.symm.litter_perm.map_domain hL),
  rw ← inv_smul_eq_iff at this,
  rw [← this, smul_left_cancel_iff],
  exact (π₀.litter_perm).right_inv hL,
end

@[mk_iff] structure exactly_approximates (π₀ : near_litter_approx) (π : near_litter_perm)
  extends approximates π₀ π : Prop :=
(exception_mem : ∀ a, π.is_exception a → a ∈ π₀.atom_perm.domain)

lemma exactly_approximates.of_is_exception {π₀ : near_litter_approx} {π : near_litter_perm}
  (hπ : π₀.exactly_approximates π) (a : atom) (ha : a.1 ∈ π₀.litter_perm.domain) :
  π.is_exception a → π₀ • a ∉ litter_set (π₀ • a.1) ∨ π₀.symm • a ∉ litter_set (π₀.symm • a.1) :=
begin
  intro h,
  rw [hπ.map_litter a.fst ha, hπ.symm_map_litter a.fst ha,
    hπ.map_atom a (hπ.exception_mem a h), hπ.symm_map_atom a (hπ.exception_mem a h)],
  exact h,
end

lemma exactly_approximates.mem_litter_set {π₀ : near_litter_approx} {π : near_litter_perm}
  (hπ : π₀.exactly_approximates π) (a : atom) (ha : a ∉ π₀.atom_perm.domain) :
  π • a ∈ litter_set (π • a.1) :=
by contrapose! ha; exact hπ.exception_mem _ (or.inl ha)

lemma exactly_approximates.mem_litter_set_inv {π₀ : near_litter_approx} {π : near_litter_perm}
  (hπ : π₀.exactly_approximates π) (a : atom) (ha : a ∉ π₀.atom_perm.domain) :
  π⁻¹ • a ∈ litter_set (π⁻¹ • a.1) :=
by contrapose! ha; exact hπ.exception_mem _ (or.inr ha)

lemma exactly_approximates.map_near_litter {π₀ : near_litter_approx} {π : near_litter_perm}
  (hπ : π₀.exactly_approximates π) (N : near_litter)
  (h₁ : N.fst ∈ π₀.litter_perm.domain)
  (h₂ : litter_set N.fst ∆ N ⊆ π₀.atom_perm.domain) :
  π₀ • N = π • N :=
begin
  rw ← set_like.coe_set_eq,
  rw smul_near_litter_coe,
  ext a : 1,
  simp only [coe_largest_sublitter, mem_union, mem_diff, mem_litter_set, near_litter_perm.coe_smul],
  split,
  { rintro (⟨ha₁, ha₂⟩ | ⟨b, ⟨hb₁, hb₂⟩, rfl⟩),
    { rw [hπ.map_litter _ h₁, ← inv_smul_eq_iff] at ha₁,
      have := (hπ.exception_mem a).mt ha₂,
      simp only [near_litter_perm.is_exception, not_or_distrib, not_not,
        mem_litter_set, eq_inv_smul_iff, ha₁] at this,
      rw mem_smul_set_iff_inv_smul_mem,
      contrapose! ha₂,
      have h : π₀ • _ ∈ _ := π₀.atom_perm.map_domain (h₂ (or.inl ⟨this.2, ha₂⟩)),
      rw [hπ.map_atom _ (h₂ (or.inl ⟨this.2, ha₂⟩)), smul_inv_smul] at h,
      exact h, },
    { simp only [mem_diff, mem_litter_set, not_and, not_not_mem] at hb₂,
      suffices : b ∈ π₀.atom_perm.domain,
      { rw hπ.map_atom _ this,
        exact ⟨b, hb₁, rfl⟩, },
      by_cases b.fst = N.fst,
      { exact hb₂ h, },
      { exact h₂ (or.inr ⟨hb₁, h⟩), }, }, },
  { rintro ⟨b, hb, rfl⟩,
    by_cases b ∈ π₀.atom_perm.domain,
    { right,
      refine ⟨b, ⟨hb, _⟩, hπ.map_atom b h⟩,
      simp only [mem_diff, mem_litter_set, not_and, not_not_mem],
      exact λ _, h, },
    { left,
      split,
      { have := (@h₂ b).mt h,
        simp only [mem_symm_diff, hb, mem_litter_set,
          not_true, and_false, true_and, false_or, not_not] at this,
        rw [hπ.map_litter _ h₁, ← this],
        by_contra h',
        exact h (hπ.exception_mem b (or.inl h')), },
      { intro hb₁,
        have hb₂ : π₀.symm • _ ∈ _ := π₀.symm.atom_perm.map_domain hb₁,
        rw [hπ.symm_map_atom _ hb₁, inv_smul_smul] at hb₂,
        exact h hb₂, }, }, },
end

instance : preorder near_litter_approx := {
  le := λ π π', π.atom_perm ≤ π'.atom_perm ∧ π.litter_perm ≤ π'.litter_perm,
  le_refl := λ π, ⟨le_rfl, le_rfl⟩,
  le_trans := λ _ _ _ h₁ h₂, ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
}

lemma approximates_of_le {π₀ π₀' : near_litter_approx} {π : near_litter_perm}
  (hle : π₀' ≤ π₀) (h : π₀.approximates π) : π₀'.approximates π :=
⟨λ a ha, (hle.1.2 ha).trans (h.1 a (hle.1.1 ha)), λ N hN, (hle.2.2 hN).trans (h.2 N (hle.2.1 hN))⟩

def free (α : Λ) [position_data.{}] [phase_2_assumptions α] {β : type_index}
  (π : near_litter_approx) (A : extended_index β) : Prop :=
∀ L ∈ π.litter_perm.domain, flexible α L A

end near_litter_approx

/-!
# Structural approximations
-/

/-- A `β`-structural approximation is a product that assigns a near-litter approximation to each
`β`-extended index. -/
def struct_approx (β : type_index) := extended_index β → near_litter_approx

namespace struct_approx

-- TODO: Could refactor struct_perm as a map `extended_index β → near_litter_perm`.

def approximates {β : type_index} (π₀ : struct_approx β) (π : struct_perm β) : Prop :=
∀ A, (π₀ A).approximates (struct_perm.of_bot $ struct_perm.derivative A π)

def exactly_approximates {β : type_index} (π₀ : struct_approx β) (π : struct_perm β) : Prop :=
∀ A, (π₀ A).exactly_approximates (struct_perm.of_bot $ struct_perm.derivative A π)

variables {α : Λ} [position_data.{}] [phase_2_assumptions α]

/-- A structural approximation `π` *supports* a set of support conditions if all of the support
conditions lie in the domain of `π` and all near-litter support conditions are litters. -/
@[mk_iff] structure supports {β : Iic α} (π₀ : struct_approx β) (S : set (support_condition β)) :
  Prop :=
(atom_mem_domain : ∀ a B, (inl a, B) ∈ S → a ∈ (π₀ B).atom_perm.domain)
(near_litter_mem_domain : ∀ (N : near_litter) B, (inr N, B) ∈ S → N.1 ∈ (π₀ B).litter_perm.domain)
(is_litter : ∀ (N : near_litter) B, (inr N, B) ∈ S → N.is_litter)

instance has_smul_support_condition {β : type_index} :
  has_smul (struct_approx β) (support_condition β) :=
⟨λ π c, ⟨π c.snd • c.fst, c.snd⟩⟩

lemma smul_support_condition_eq {β : type_index} (π : struct_approx β) (c : support_condition β) :
  π • c = ⟨π c.snd • c.fst, c.snd⟩ := rfl

lemma smul_eq_of_supports {β : Iic α} {π₀ : struct_approx β} {π : allowable β}
  (hπ : π₀.exactly_approximates π.to_struct_perm)
  {S : set (support_condition β)} (hS : π₀.supports S)
  {c : support_condition β} (hc : c ∈ S) : π₀ • c = π • c :=
begin
  obtain ⟨a | N, A⟩ := c,
  { refine prod.ext _ rfl,
    change inl _ = inl _,
    exact congr_arg inl ((hπ A).map_atom a (hS.atom_mem_domain a A hc)), },
  refine prod.ext _ rfl,
  change inr _ = inr _,
  refine congr_arg inr _,
  ext : 1,
  exact (hπ A).map_litter N.fst (hS.near_litter_mem_domain N A hc),
  rw (hS.is_litter N A hc).eq_fst_to_near_litter,
  ext a : 1,
  simp only [near_litter_approx.smul_near_litter_coe, litter.to_near_litter_fst,
    near_litter_approx.coe_largest_sublitter, litter.coe_to_near_litter, sdiff_sdiff_right_self,
    inf_eq_inter, mem_union, mem_diff, mem_litter_set, set_like.mem_coe],
  split,
  { rintro (⟨h₁, h₂⟩ | ⟨a, ⟨ha₁, ha₂⟩, rfl⟩),
    { refine ⟨(struct_perm.derivative A π.to_struct_perm)⁻¹ • a, _,
        by simp only [struct_perm.coe_to_near_litter_perm, struct_perm.of_bot_smul, smul_inv_smul]⟩,
      simp only [litter.coe_to_near_litter, mem_litter_set],
      have := (hπ A).mem_litter_set_inv a h₂,
      rw [h₁, (hπ A).map_litter _ (hS.near_litter_mem_domain N A hc),
        mem_litter_set, inv_smul_smul, struct_perm.of_bot_inv_smul] at this,
      exact this, },
    { exact ⟨a, ha₁, ((hπ A).map_atom a ha₂).symm⟩, }, },
  { rintro ⟨a, ha, rfl⟩,
    simp only [litter.coe_to_near_litter, mem_litter_set] at ha,
    simp only [struct_perm.coe_to_near_litter_perm, struct_perm.of_bot_smul],
    by_cases a ∈ (π₀ A).atom_perm.domain,
    { exact or.inr ⟨a, ⟨ha, h⟩, (hπ A).map_atom a h⟩, },
    { refine or.inl ⟨_, _⟩,
      { have := (hπ A).mem_litter_set a h,
        simp only [struct_perm.of_bot_smul, mem_litter_set] at this,
        rw [this, ha],
        exact ((hπ A).map_litter _ (hS.near_litter_mem_domain N A hc)).symm, },
      { contrapose! h,
        have := (hπ A).symm_map_atom _ h,
        simp only [struct_perm.of_bot_inv_smul, inv_smul_smul] at this,
        rw ← this,
        exact (π₀ A).symm.atom_perm.map_domain h, }, }, },
end

/-- If two allowable permutations exactly approximate some structural approximation, then their
actions agree on everything that the structural approximation supports. -/
lemma smul_eq_smul_of_exactly_approximates {β : Iic α}
  {π₀ π₀' : struct_approx β} {π π' : allowable β}
  (hπ : π₀.exactly_approximates π.to_struct_perm)
  (hπ' : π₀'.exactly_approximates π'.to_struct_perm)
  (S : set (support_condition β)) (t : tangle β)
  (hS : π₀.supports S) (hS' : π₀'.supports S) (ht : mul_action.supports (allowable β) S t)
  (hSπ : ∀ c ∈ S, π₀ • c = π₀' • c) : π • t = π' • t :=
begin
  have := ht (π'⁻¹ * π) _,
  { rw [mul_smul, inv_smul_eq_iff] at this,
    exact this, },
  intros c hc,
  rw [mul_smul, inv_smul_eq_iff, ← smul_eq_of_supports hπ hS hc, ← smul_eq_of_supports hπ' hS' hc],
  exact hSπ c hc,
end

lemma smul_eq_smul_of_exactly_approximates' {β : Iio α}
  {π₀ π₀' : struct_approx β} {π π' : allowable β}
  (hπ : π₀.exactly_approximates π.to_struct_perm)
  (hπ' : π₀'.exactly_approximates π'.to_struct_perm)
  (S : set (support_condition β)) (t : tangle β)
  (hS : (show struct_approx (β : Iic α), from π₀).supports S)
  (hS' :(show struct_approx (β : Iic α), from π₀').supports S)
  (ht : mul_action.supports (allowable β) S t)
  (hSπ : ∀ c ∈ S, π₀ • c = π₀' • c) : π • t = π' • t :=
@smul_eq_smul_of_exactly_approximates _ _ _ _ (β : Iic α) _ _ _ _ hπ hπ' S t hS hS' ht hSπ

def free {β : Iic α} (π₀ : struct_approx β) : Prop := ∀ A, (π₀ A).free α A

/-!
# Induction on support conditions
-/

/-- The inductive hypothesis used to construct the induced action of an approximation in the
freedom of action theorem. -/
structure hypothesis {β : Iic α} (c : support_condition β) :=
(atom_image : Π a A, (relation.trans_gen (constrains α β)) ⟨inl a, A⟩ c → atom)
(near_litter_image : Π N A, (relation.trans_gen (constrains α β)) ⟨inr N, A⟩ c → near_litter)

namespace hypothesis
variable {β : Iic α}

/-- Two hypotheses are compatible if they agree everywhere that they are both defined. -/
@[mk_iff] structure compatible {c d : support_condition β}
  (Hc : hypothesis c) (Hd : hypothesis d) : Prop :=
(atom_compatible : ∀ a A hc hd, Hc.atom_image a A hc = Hd.atom_image a A hd)
(near_litter_compatible : ∀ N A hc hd, Hc.near_litter_image N A hc = Hd.near_litter_image N A hd)

def fix_map :
  (psum (Σ' (_ : atom), extended_index β) (Σ' (_ : near_litter), extended_index β)) →
  support_condition β
| (psum.inl ⟨a, A⟩) := ⟨inl a, A⟩
| (psum.inr ⟨N, A⟩) := ⟨inr N, A⟩

def fix_wf : has_well_founded
  (psum (Σ' (_ : atom), extended_index β) (Σ' (_ : near_litter), extended_index β)) :=
⟨inv_image (relation.trans_gen (constrains α β)) fix_map,
  inv_image.wf _ (constrains_wf α β).trans_gen⟩

/-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
This is used to compute the induced action of an approximation on all atoms and near-litters. -/
noncomputable! mutual def fix_atom, fix_near_litter
  (Fa : Π a (A : extended_index β), hypothesis ⟨inl a, A⟩ → atom)
  (FN : Π N (A : extended_index β), hypothesis ⟨inr N, A⟩ → near_litter)
with fix_atom : atom → extended_index β → atom
| a A := Fa a A ⟨λ b B hb, fix_atom b B, λ N B hb, fix_near_litter N B⟩
with fix_near_litter : near_litter → extended_index β → near_litter
| N A := FN N A ⟨λ b B hb, fix_atom b B, λ N B hb, fix_near_litter N B⟩
using_well_founded { rel_tac := λ _ _, `[exact fix_wf], dec_tac := `[exact hb] }

lemma fix_atom_eq (Fa FN) (a : atom) (A : extended_index β) :
  fix_atom Fa FN a A =
  Fa a A ⟨λ b B hb, fix_atom Fa FN b B, λ N B hb, fix_near_litter Fa FN N B⟩ :=
by rw fix_atom

lemma fix_near_litter_eq (Fa FN) (N : near_litter) (A : extended_index β) :
  fix_near_litter Fa FN N A =
  FN N A ⟨λ b B hb, fix_atom Fa FN b B, λ N B hb, fix_near_litter Fa FN N B⟩ :=
by rw fix_near_litter

end hypothesis

end struct_approx

end con_nf
