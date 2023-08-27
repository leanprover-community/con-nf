import ConNF.Mathlib.Logic.Equiv.LocalPerm
import ConNF.Foa.Basic.Flexible
import ConNF.Foa.Basic.Sublitter

open Quiver Set Sum

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Near-litter approximations
-/

@[ext]
structure NearLitterApprox where
  atomPerm : LocalPerm Atom
  litterPerm : LocalPerm Litter
  domain_small : ∀ L, Small (litterSet L ∩ atomPerm.domain)

namespace NearLitterApprox

instance : SMul NearLitterApprox Atom :=
  ⟨fun π => π.atomPerm⟩

instance : SMul NearLitterApprox Litter :=
  ⟨fun π => π.litterPerm⟩

variable (π : NearLitterApprox)

theorem smul_atom_eq {a : Atom} : π.atomPerm a = π • a :=
  rfl

theorem smul_litter_eq {L : Litter} : π.litterPerm L = π • L :=
  rfl

@[simp]
theorem mk_smul_atom {atomPerm : LocalPerm Atom} {litterPerm : LocalPerm Litter}
    {domain_small : ∀ L, Small (litterSet L ∩ atomPerm.domain)} {a : Atom} :
    (⟨atomPerm, litterPerm, domain_small⟩ : NearLitterApprox) • a = atomPerm a :=
  rfl

@[simp]
theorem mk_smul_litter {atomPerm : LocalPerm Atom} {litterPerm : LocalPerm Litter}
    {domain_small : ∀ L, Small (litterSet L ∩ atomPerm.domain)} {L : Litter} :
    (⟨atomPerm, litterPerm, domain_small⟩ : NearLitterApprox) • L = litterPerm L :=
  rfl

theorem smul_eq_smul_atom {a₁ a₂ : Atom} (h₁ : a₁ ∈ π.atomPerm.domain)
    (h₂ : a₂ ∈ π.atomPerm.domain) : π • a₁ = π • a₂ ↔ a₁ = a₂ := by
  rw [mk_smul_atom, mk_smul_atom,
    ← π.atomPerm.eq_symm_apply h₁ (π.atomPerm.map_domain h₂), LocalPerm.left_inv _ h₂]

theorem smul_eq_smul_litter {L₁ L₂ : Litter} (h₁ : L₁ ∈ π.litterPerm.domain)
    (h₂ : L₂ ∈ π.litterPerm.domain) : π • L₁ = π • L₂ ↔ L₁ = L₂ := by
  rw [mk_smul_litter, mk_smul_litter,
    ← π.litterPerm.eq_symm_apply h₁ (π.litterPerm.map_domain h₂), LocalPerm.left_inv _ h₂]

def symm : NearLitterApprox where
  atomPerm := π.atomPerm.symm
  litterPerm := π.litterPerm.symm
  domain_small := π.domain_small

@[simp]
theorem symm_atomPerm : π.symm.atomPerm = π.atomPerm.symm :=
  rfl

@[simp]
theorem symm_litterPerm : π.symm.litterPerm = π.litterPerm.symm :=
  rfl

@[simp]
theorem left_inv_atom {a} : a ∈ π.atomPerm.domain → π.symm • π • a = a :=
  π.atomPerm.left_inv

@[simp]
theorem left_inv_litter {L} : L ∈ π.litterPerm.domain → π.symm • π • L = L :=
  π.litterPerm.left_inv

@[simp]
theorem right_inv_atom {a} : a ∈ π.atomPerm.domain → π • π.symm • a = a :=
  π.atomPerm.right_inv

@[simp]
theorem right_inv_litter {L} : L ∈ π.litterPerm.domain → π • π.symm • L = L :=
  π.litterPerm.right_inv

theorem symm_smul_atom_eq_iff {a b} :
    a ∈ π.atomPerm.domain → b ∈ π.atomPerm.domain → (π.symm • a = b ↔ a = π • b) :=
  by
  intro ha hb
  constructor
  · rintro rfl
    exact (π.right_inv_atom ha).symm
  · rintro rfl
    exact π.left_inv_atom hb

theorem symm_smul_litter_eq_iff {L₁ L₂} :
    L₁ ∈ π.litterPerm.domain → L₂ ∈ π.litterPerm.domain → (π.symm • L₁ = L₂ ↔ L₁ = π • L₂) :=
  by
  intro hL₁ hL₂
  constructor
  · rintro rfl
    exact (π.right_inv_litter hL₁).symm
  · rintro rfl
    exact π.left_inv_litter hL₂

theorem eq_symm_apply_atom {a₁ a₂} :
    a₁ ∈ π.atomPerm.domain → a₂ ∈ π.atomPerm.domain → (a₁ = π.symm • a₂ ↔ π • a₁ = a₂) :=
  π.atomPerm.eq_symm_apply

theorem eq_symm_apply_litter {L₁ L₂} :
    L₁ ∈ π.litterPerm.domain → L₂ ∈ π.litterPerm.domain → (L₁ = π.symm • L₂ ↔ π • L₁ = L₂) :=
  π.litterPerm.eq_symm_apply

theorem nearLitter_domain_small (N : NearLitter) : Small ((N : Set Atom) ∩ π.atomPerm.domain) := by
  rw [← symmDiff_symmDiff_cancel_left (litterSet N.fst) N, inter_symmDiff_distrib_right]
  exact Small.symmDiff (π.domain_small N.fst) (Small.mono (inter_subset_left _ _) N.2.prop)

section Generate

/-- Gives the largest sublitter of `π` on which `π.atom_perm` is not defined. -/
def largestSublitter (L : Litter) : Sublitter
    where
  litter := L
  carrier := litterSet L \ π.atomPerm.domain
  subset := diff_subset _ _
  diff_small := by simpa only [sdiff_sdiff_right_self, inf_eq_inter] using π.domain_small L

@[simp]
theorem largestSublitter_litter (L : Litter) : (π.largestSublitter L).litter = L :=
  rfl

@[simp]
theorem coe_largestSublitter (L : Litter) :
    (π.largestSublitter L : Set Atom) = litterSet L \ π.atomPerm.domain :=
  rfl

theorem mem_largestSublitter_of_not_mem_domain (a : Atom) (h : a ∉ π.atomPerm.domain) :
    a ∈ π.largestSublitter a.1 :=
  ⟨rfl, h⟩

theorem not_mem_domain_of_mem_largestSublitter {a : Atom} {L : Litter}
    (h : a ∈ π.largestSublitter L) : a ∉ π.atomPerm.domain :=
  h.2

/-- Computes the action of `π` on this sublitter, assuming it is in `sublitter_domain`. -/
def generateSublitter (S : Sublitter) : Sublitter :=
  π.largestSublitter (π • S.litter)

def sublitterDomain : Set Sublitter :=
  {S | S.litter ∈ π.litterPerm.domain ∧ (S : Set Atom) = litterSet S.litter \ π.atomPerm.domain}

theorem mem_sublitterDomain (S : Sublitter) (h : S ∈ π.sublitterDomain) :
    (S : Set Atom) = litterSet S.litter \ π.atomPerm.domain :=
  h.2

theorem generateSublitter_mem_domain ⦃S : Sublitter⦄ (h : S ∈ sublitterDomain π) :
    generateSublitter π S ∈ sublitterDomain π :=
  ⟨π.litterPerm.map_domain h.1, rfl⟩

theorem generateSublitter_left_inv ⦃S : Sublitter⦄ (h : S ∈ sublitterDomain π) :
    generateSublitter π.symm (generateSublitter π S) = S := by
  ext : 1
  simp only [h.2, largestSublitter, generateSublitter, symm_atomPerm, LocalPerm.symm_domain,
    Sublitter.coe_mk, π.left_inv_litter h.1]

/-- Generates the unique near-litter approximation given by an atom local permutation and a
near-litter local permutation. This uniqueness is only up to evaluating everything on the domain
of the permutation. -/
def generateSublitterPerm : LocalPerm Sublitter
    where
  toFun := generateSublitter π
  invFun := generateSublitter π.symm
  domain := sublitterDomain π
  toFun_domain' := generateSublitter_mem_domain π
  invFun_domain' := generateSublitter_mem_domain π.symm
  left_inv' := generateSublitter_left_inv π
  right_inv' := generateSublitter_left_inv π.symm

@[simp]
theorem generate_symm : (generateSublitterPerm π).symm = generateSublitterPerm π.symm :=
  rfl

@[simp]
theorem generateSublitterPerm_domain : (generateSublitterPerm π).domain = sublitterDomain π :=
  rfl

@[simp]
theorem generateSublitter_apply (S : Sublitter) :
    generateSublitterPerm π S = generateSublitter π S :=
  rfl

instance : SMul NearLitterApprox Sublitter :=
  ⟨fun π => π.generateSublitterPerm⟩

theorem smul_sublitter_eq (S : Sublitter) : π • S = generateSublitterPerm π S :=
  rfl

@[simp]
theorem smul_sublitter_litter (S : Sublitter) : (π • S).litter = π • S.litter :=
  rfl

theorem smul_eq_smul_sublitter {S₁ S₂ : Sublitter} (h₁ : S₁ ∈ sublitterDomain π)
    (h₂ : S₂ ∈ sublitterDomain π) : π • S₁ = π • S₂ ↔ S₁ = S₂ := by
  rw [smul_sublitter_eq, smul_sublitter_eq,
    ← π.generateSublitterPerm.eq_symm_apply h₁ (π.generateSublitterPerm.map_domain h₂),
    LocalPerm.left_inv _ _]
  exact h₂

@[simp]
theorem left_inv_sublitter {S} : S ∈ π.sublitterDomain → π.symm • π • S = S :=
  π.generateSublitterPerm.left_inv

@[simp]
theorem right_inv_sublitter {S} : S ∈ π.sublitterDomain → π • π.symm • S = S :=
  π.generateSublitterPerm.right_inv

theorem eq_symm_apply_sublitter {S₁ S₂} :
    S₁ ∈ π.sublitterDomain → S₂ ∈ π.sublitterDomain → (S₁ = π.symm • S₂ ↔ π • S₁ = S₂) :=
  π.generateSublitterPerm.eq_symm_apply

/-- Computes the action of `π` on this near-litter. This action is not injective.
The nicest properties will hold when `N` is a litter. -/
def generateNearLitter (π : NearLitterApprox) (N : NearLitter) : NearLitter :=
  ⟨π • N.1, π.largestSublitter (π • N.1) ∪ π • ((N : Set Atom) \ π.largestSublitter N.1), by
    refine Small.union ?_ ?_
    · rw [← diff_diff]
      exact Small.mono (diff_subset _ _) (π.largestSublitter (π • N.1)).diff_small
    · rw [union_diff_distrib]
      refine Small.union ?_ ?_
      · have := (π.largestSublitter (π • N.1)).subset
        rw [largestSublitter_litter, Sublitter.carrier_eq_coe] at this
        rw [diff_eq_empty.mpr this]
        exact small_empty
      · refine Small.mono (diff_subset _ _) (Small.image ?_)
        have := Small.union (Small.mono (subset_union_right _ _) N.2.prop)
            (π.largestSublitter N.1).diff_small
        simp only [largestSublitter_litter, Sublitter.carrier_eq_coe] at this
        refine Small.mono ?_ this
        intro a ha
        by_cases a ∈ litterSet N.fst
        exact Or.inr ⟨h, ha.2⟩
        exact Or.inl ⟨ha.1, h⟩⟩

instance : SMul NearLitterApprox NearLitter :=
  ⟨generateNearLitter⟩

@[simp]
theorem smul_nearLitter_coe (π : NearLitterApprox) (N : NearLitter) :
    ((π • N : NearLitter) : Set Atom) =
      (π.largestSublitter (π • N.1) : Set Atom) ∪ π • ((N : Set Atom) \ π.largestSublitter N.1) :=
  rfl

end Generate

def _root_.ConNF.NearLitterPerm.IsException (π : NearLitterPerm) (a : Atom) : Prop :=
  π • a ∉ litterSet (π • a.1) ∨ π⁻¹ • a ∉ litterSet (π⁻¹ • a.1)

@[mk_iff]
structure Approximates (π₀ : NearLitterApprox) (π : NearLitterPerm) : Prop where
  map_atom : ∀ a, a ∈ π₀.atomPerm.domain → π₀ • a = π • a
  map_litter : ∀ L, L ∈ π₀.litterPerm.domain → π₀ • L = π • L

theorem Approximates.symm_map_atom {π₀ : NearLitterApprox} {π : NearLitterPerm}
    (hπ : π₀.Approximates π) (a : Atom) (ha : a ∈ π₀.atomPerm.domain) :
    π₀.symm • a = π⁻¹ • a := by
  have := hπ.map_atom (π₀.symm • a) (π₀.symm.atomPerm.map_domain ha)
  rw [← inv_smul_eq_iff] at this
  rw [← this, smul_left_cancel_iff]
  exact π₀.atomPerm.right_inv ha

theorem Approximates.symm_map_litter {π₀ : NearLitterApprox} {π : NearLitterPerm}
    (hπ : π₀.Approximates π) (L : Litter) (hL : L ∈ π₀.litterPerm.domain) :
    π₀.symm • L = π⁻¹ • L := by
  have := hπ.map_litter (π₀.symm • L) (π₀.symm.litterPerm.map_domain hL)
  rw [← inv_smul_eq_iff] at this
  rw [← this, smul_left_cancel_iff]
  exact π₀.litterPerm.right_inv hL

@[mk_iff]
structure ExactlyApproximates (π₀ : NearLitterApprox) (π : NearLitterPerm) extends
    Approximates π₀ π : Prop where
  exception_mem : ∀ a, π.IsException a → a ∈ π₀.atomPerm.domain

theorem ExactlyApproximates.of_isException {π₀ : NearLitterApprox} {π : NearLitterPerm}
    (hπ : π₀.ExactlyApproximates π) (a : Atom) (ha : a.1 ∈ π₀.litterPerm.domain) :
    π.IsException a → π₀ • a ∉ litterSet (π₀ • a.1) ∨ π₀.symm • a ∉ litterSet (π₀.symm • a.1) :=
  by
  intro h
  rw [hπ.map_litter a.fst ha, hπ.symm_map_litter a.fst ha, hπ.map_atom a (hπ.exception_mem a h),
    hπ.symm_map_atom a (hπ.exception_mem a h)]
  exact h

theorem ExactlyApproximates.mem_litterSet {π₀ : NearLitterApprox} {π : NearLitterPerm}
    (hπ : π₀.ExactlyApproximates π) (a : Atom) (ha : a ∉ π₀.atomPerm.domain) :
    π • a ∈ litterSet (π • a.1) := by contrapose! ha; exact hπ.exception_mem _ (Or.inl ha)

theorem ExactlyApproximates.mem_litterSet_inv {π₀ : NearLitterApprox} {π : NearLitterPerm}
    (hπ : π₀.ExactlyApproximates π) (a : Atom) (ha : a ∉ π₀.atomPerm.domain) :
    π⁻¹ • a ∈ litterSet (π⁻¹ • a.1) := by contrapose! ha; exact hπ.exception_mem _ (Or.inr ha)

theorem ExactlyApproximates.map_nearLitter {π₀ : NearLitterApprox} {π : NearLitterPerm}
    (hπ : π₀.ExactlyApproximates π) (N : NearLitter) (h₁ : N.fst ∈ π₀.litterPerm.domain)
    (h₂ : litterSet N.fst ∆ N ⊆ π₀.atomPerm.domain) : π₀ • N = π • N := by
  rw [← SetLike.coe_set_eq]
  rw [smul_nearLitter_coe]
  ext a : 1
  simp only [coe_largestSublitter, mem_union, mem_diff, ConNF.mem_litterSet,
    NearLitterPerm.smul_nearLitter_coe]
  constructor
  · rintro (⟨ha₁, ha₂⟩ | ⟨b, ⟨hb₁, hb₂⟩, rfl⟩)
    · rw [hπ.map_litter _ h₁, ← inv_smul_eq_iff] at ha₁
      have := (hπ.exception_mem a).mt ha₂
      simp only [NearLitterPerm.IsException, not_or, Classical.not_not, ConNF.mem_litterSet,
        eq_inv_smul_iff, ha₁] at this
      rw [mem_smul_set_iff_inv_smul_mem]
      contrapose! ha₂
      have h : π₀ • (π⁻¹ • a) ∈ _ := π₀.atomPerm.map_domain (h₂ (Or.inl ⟨this.2, ha₂⟩))
      rw [hπ.map_atom _ (h₂ (Or.inl ⟨this.2, ha₂⟩)), smul_inv_smul] at h
      exact h
    · simp only [mem_diff, ConNF.mem_litterSet, not_and, not_not_mem] at hb₂
      suffices b ∈ π₀.atomPerm.domain by
        dsimp only
        rw [hπ.map_atom _ this]
        exact ⟨b, hb₁, rfl⟩
      by_cases b.fst = N.fst
      · exact hb₂ h
      · exact h₂ (Or.inr ⟨hb₁, h⟩)
  · rintro ⟨b, hb, rfl⟩
    by_cases b ∈ π₀.atomPerm.domain
    · right
      refine' ⟨b, ⟨hb, _⟩, hπ.map_atom b h⟩
      simp only [mem_diff, ConNF.mem_litterSet, not_and, not_not_mem]
      exact fun _ => h
    · left
      constructor
      · have := (@h₂ b).mt h
        simp only [mem_symmDiff, hb, ConNF.mem_litterSet, not_true, and_false_iff, true_and_iff,
          false_or_iff, Classical.not_not] at this
        rw [hπ.map_litter _ h₁, ← this]
        by_contra h'
        exact h (hπ.exception_mem b (Or.inl h'))
      · intro hb₁
        have hb₂ : π₀.symm • (π • b) ∈ _ := π₀.symm.atomPerm.map_domain hb₁
        rw [hπ.symm_map_atom _ hb₁, inv_smul_smul] at hb₂
        exact h hb₂

instance : Preorder NearLitterApprox
    where
  le π π' := π.atomPerm ≤ π'.atomPerm ∧ π.litterPerm ≤ π'.litterPerm
  le_refl π := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem approximatesOfLe {π₀ π₀' : NearLitterApprox} {π : NearLitterPerm} (hle : π₀' ≤ π₀)
    (h : π₀.Approximates π) : π₀'.Approximates π :=
  ⟨fun a ha => (hle.1.2 ha).trans (h.1 a (hle.1.1 ha)), fun N hN =>
    (hle.2.2 hN).trans (h.2 N (hle.2.1 hN))⟩

def Free (α : Λ) [BasePositions] [Phase2Assumptions α] {β : TypeIndex} (π : NearLitterApprox)
    (A : ExtendedIndex β) : Prop :=
  ∀ L ∈ π.litterPerm.domain, Flexible α L A

end NearLitterApprox

/-!
# Structural approximations
-/

/-- A `β`-structural approximation is a product that assigns a near-litter approximation to each
`β`-extended index. -/
def StructApprox (β : TypeIndex) :=
  ExtendedIndex β → NearLitterApprox

namespace StructApprox

-- TODO: Could refactor StructPerm as a map `extended_index β → near_litter_perm`.
def Approximates {β : TypeIndex} (π₀ : StructApprox β) (π : StructPerm β) : Prop :=
  ∀ A, (π₀ A).Approximates (StructPerm.ofBot <| StructPerm.derivative A π)

def ExactlyApproximates {β : TypeIndex} (π₀ : StructApprox β) (π : StructPerm β) : Prop :=
  ∀ A, (π₀ A).ExactlyApproximates (StructPerm.ofBot <| StructPerm.derivative A π)

variable {α : Λ} [BasePositions] [Phase2Assumptions α]

-- TODO: I think these were never used.
/-
/-- A structural approximation `π` *supports* a set of support conditions if all of the support
conditions lie in the domain of `π` and all near-litter support conditions are litters. -/
@[mk_iff]
structure Supports {β : Iic α} (π₀ : StructApprox β) (S : Set (SupportCondition β)) : Prop where
  atom_mem_domain : ∀ a B, (inl a, B) ∈ S → a ∈ (π₀ B).atomPerm.domain
  nearLitter_mem_domain : ∀ (N : NearLitter) (B), (inr N, B) ∈ S → N.1 ∈ (π₀ B).litterPerm.domain
  IsLitter : ∀ (N : NearLitter) (B), (inr N, B) ∈ S → N.IsLitter

instance hasSmulSupportCondition {β : TypeIndex} : SMul (StructApprox β) (SupportCondition β) :=
  ⟨fun π c => ⟨π c.snd • c.fst, c.snd⟩⟩

theorem smul_supportCondition_eq {β : TypeIndex} (π : StructApprox β) (c : SupportCondition β) :
    π • c = ⟨π c.snd • c.fst, c.snd⟩ :=
  rfl

theorem smul_eq_of_supports {β : Iic α} {π₀ : StructApprox β} {π : Allowable β}
    (hπ : π₀.ExactlyApproximates (Allowable.toStructPerm π))
    {S : Set (SupportCondition β)} (hS : π₀.Supports S)
    {c : SupportCondition β} (hc : c ∈ S) : π₀ • c = π • c := by
  obtain ⟨a | N, A⟩ := c
  · refine Prod.ext ?_ rfl
    change inl _ = inl _
    exact congr_arg inl ((hπ A).map_atom a (hS.atom_mem_domain a A hc))
  refine Prod.ext ?_ rfl
  change inr _ = inr _
  refine congr_arg inr ?_
  refine SetLike.coe_injective ?_
  -- ext a : 1
  -- exact (hπ A).map_litter N.fst (hS.nearLitter_mem_domain N A hc)
  dsimp only
  rw [(hS.is_litter N A hc).eq_fst_toNearLitter]
  ext a : 1
  simp only [near_litter_approx.smul_near_litter_coe, litter.to_near_litter_fst,
    near_litter_approx.coe_largest_sublitter, litter.coe_to_near_litter, sdiff_sdiff_right_self,
    inf_eq_inter, mem_union, mem_diff, mem_litter_set, SetLike.mem_coe]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨a, ⟨ha₁, ha₂⟩, rfl⟩)
    · refine'
        ⟨(StructPerm.derivative A π.to_StructPerm)⁻¹ • a, _, by
          simp only [StructPerm.coe_to_near_litter_perm, StructPerm.of_bot_smul, smul_inv_smul]⟩
      simp only [litter.coe_to_near_litter, mem_litter_set]
      have := (hπ A).mem_litterSet_inv a h₂
      rw [h₁, (hπ A).map_litter _ (hS.near_litter_mem_domain N A hc), mem_litter_set, inv_smul_smul,
        StructPerm.of_bot_inv_smul] at this
      exact this
    · exact ⟨a, ha₁, ((hπ A).map_atom a ha₂).symm⟩
  · rintro ⟨a, ha, rfl⟩
    simp only [litter.coe_to_near_litter, mem_litter_set] at ha
    simp only [StructPerm.coe_to_near_litter_perm, StructPerm.of_bot_smul]
    by_cases a ∈ (π₀ A).atomPerm.domain
    · exact Or.inr ⟨a, ⟨ha, h⟩, (hπ A).map_atom a h⟩
    · refine' Or.inl ⟨_, _⟩
      · have := (hπ A).mem_litterSet a h
        simp only [StructPerm.of_bot_smul, mem_litter_set] at this
        rw [this, ha]
        exact ((hπ A).map_litter _ (hS.near_litter_mem_domain N A hc)).symm
      · contrapose! h
        have := (hπ A).symm_map_atom _ h
        simp only [StructPerm.of_bot_inv_smul, inv_smul_smul] at this
        rw [← this]
        exact (π₀ A).symm.atomPerm.map_domain h

/-- If two allowable permutations exactly approximate some structural approximation, then their
actions agree on everything that the structural approximation supports. -/
theorem smul_eq_smul_of_exactlyApproximates {β : Iic α} {π₀ π₀' : StructApprox β}
    {π π' : Allowable β} (hπ : π₀.ExactlyApproximates π.toStructPerm)
    (hπ' : π₀'.ExactlyApproximates π'.toStructPerm) (S : Set (SupportCondition β)) (t : Tangle β)
    (hS : π₀.Supports S) (hS' : π₀'.Supports S) (ht : MulAction.Supports (Allowable β) S t)
    (hSπ : ∀ c ∈ S, π₀ • c = π₀' • c) : π • t = π' • t :=
  by
  have := ht (π'⁻¹ * π) _
  · rw [mul_smul, inv_smul_eq_iff] at this
    exact this
  intro c hc
  rw [mul_smul, inv_smul_eq_iff, ← smul_eq_of_supports hπ hS hc, ← smul_eq_of_supports hπ' hS' hc]
  exact hSπ c hc

theorem smul_eq_smul_of_exactly_approximates' {β : Iio α} {π₀ π₀' : StructApprox β}
    {π π' : Allowable β} (hπ : π₀.ExactlyApproximates π.toStructPerm)
    (hπ' : π₀'.ExactlyApproximates π'.toStructPerm) (S : Set (SupportCondition β)) (t : Tangle β)
    (hS : (show StructApprox (β : Iic α) from π₀).Supports S)
    (hS' : (show StructApprox (β : Iic α) from π₀').Supports S)
    (ht : MulAction.Supports (Allowable β) S t) (hSπ : ∀ c ∈ S, π₀ • c = π₀' • c) :
    π • t = π' • t :=
  @smul_eq_smul_of_exactlyApproximates _ _ _ _ (β : Iic α) _ _ _ _ hπ hπ' S t hS hS' ht hSπ
-/

def Free {β : Iic α} (π₀ : StructApprox β) : Prop :=
  ∀ A, (π₀ A).Free α A

/-!
# Derivatives of structural approximations
-/


def comp {β γ : TypeIndex} (π₀ : StructApprox β) (A : Path β γ) : StructApprox γ := fun B =>
  π₀ (A.comp B)

@[simp]
theorem comp_apply {β γ : TypeIndex} (π₀ : StructApprox β) (A : Path β γ) (B : ExtendedIndex γ) :
    π₀.comp A B = π₀ (A.comp B) :=
  rfl

theorem Approximates.comp {β γ : TypeIndex} {π₀ : StructApprox β} {π : StructPerm β}
    (h : π₀.Approximates π) (A : Path β γ) : (π₀.comp A).Approximates (StructPerm.derivative A π) :=
  by
  intro B
  rw [comp_apply, StructPerm.derivative_derivative]
  exact h _

theorem ExactlyApproximates.comp {β γ : TypeIndex} {π₀ : StructApprox β} {π : StructPerm β}
    (h : π₀.ExactlyApproximates π) (A : Path β γ) :
    (π₀.comp A).ExactlyApproximates (StructPerm.derivative A π) :=
  by
  intro B
  rw [comp_apply, StructPerm.derivative_derivative]
  exact h _

/-!
# Induction on support conditions
-/


/-- The inductive hypothesis used to construct the induced action of an approximation in the
freedom of action theorem. -/
structure Hypothesis {β : Iic α} (c : SupportCondition β) where
  atomImage : ∀ A a, ⟨inl a, A⟩ <[α] c → Atom
  nearLitterImage : ∀ A N, ⟨inr N, A⟩ <[α] c → NearLitter

namespace Hypothesis

variable {β : Iic α}

def fixMap :
    PSum (Σ' _ : ExtendedIndex β, Atom) (Σ' _ : ExtendedIndex β, NearLitter) → SupportCondition β
  | PSum.inl ⟨A, a⟩ => ⟨inl a, A⟩
  | PSum.inr ⟨A, N⟩ => ⟨inr N, A⟩

def fixWf :
    WellFoundedRelation
      (PSum (Σ' _ : ExtendedIndex β, Atom) (Σ' _ : ExtendedIndex β, NearLitter)) :=
  ⟨InvImage (Relation.TransGen (Constrains α β)) fixMap,
    InvImage.wf _ (WellFounded.transGen <| constrains_wf α β)⟩

mutual
  /-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
  This is used to compute the induced action of an approximation on all atoms and near-litters. -/
  noncomputable def fixAtom (Fa : ∀ (A : ExtendedIndex β) (a), Hypothesis ⟨inl a, A⟩ → Atom)
      (FN : ∀ (A : ExtendedIndex β) (N), Hypothesis ⟨inr N, A⟩ → NearLitter) :
      ExtendedIndex β → Atom → Atom
    | A, a => Fa A a ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩
  /-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
  This is used to compute the induced action of an approximation on all atoms and near-litters. -/
  noncomputable def fixNearLitter (Fa : ∀ (A : ExtendedIndex β) (a), Hypothesis ⟨inl a, A⟩ → Atom)
      (FN : ∀ (A : ExtendedIndex β) (N), Hypothesis ⟨inr N, A⟩ → NearLitter) :
      ExtendedIndex β → NearLitter → NearLitter
    | A, N => FN A N ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩
end
termination_by' fixWf

theorem fixAtom_eq (Fa FN) (A : ExtendedIndex β) (a : Atom) :
    fixAtom Fa FN A a =
      Fa A a ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩ :=
  by rw [fixAtom]

theorem fixNearLitter_eq (Fa FN) (A : ExtendedIndex β) (N : NearLitter) :
    fixNearLitter Fa FN A N =
      FN A N ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩ :=
  by rw [fixNearLitter]

end Hypothesis

end StructApprox

end ConNF
