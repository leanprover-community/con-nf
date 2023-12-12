import ConNF.Mathlib.Logic.Equiv.LocalPerm
import ConNF.FOA.Basic.Flexible
import ConNF.FOA.Basic.Sublitter

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

def Free [BasePositions] [Level] [FOAAssumptions] {β : TypeIndex} (π : NearLitterApprox)
    (A : ExtendedIndex β) : Prop :=
  ∀ L ∈ π.litterPerm.domain, Flexible A L

end NearLitterApprox

end ConNF
