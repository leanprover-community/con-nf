import Mathlib.Tactic.Have
import Mathlib.ModelTheory.Satisfiability

/-!
# Typical ambiguity
-/

noncomputable section

open FirstOrder Language Theory Structure

namespace ConNF.Specker

variable {L : Language} (ϕ : L →ᴸ L) (M : Type _) [L.Structure M] [Nonempty M]

/-- A weaker version of the assumption that `ϕ` is an expansion on `M`. -/
class IsEndomorphismOn (ϕ : L →ᴸ L) (M : Type _) [L.Structure M] : Prop where
  map_onSentence : ∀ (S : L.Sentence), M ⊨ ϕ.onSentence S ↔ M ⊨ S

class IsTheoryEndomorphism (ϕ : L →ᴸ L) (T : L.Theory) where
  map_onSentence : ∀ (S : L.Sentence), ϕ.onSentence S ∈ T ↔ S ∈ T

export IsEndomorphismOn (map_onSentence)

variable [IsEndomorphismOn ϕ M]

attribute [simp] map_onSentence

@[simp]
theorem onTerm_relabel {α β : Type _} {L L' : Language}
    (ϕ : L →ᴸ L') (T : L.Term α) (g : α → β) :
    ϕ.onTerm (T.relabel g) = (ϕ.onTerm T).relabel g := by
  induction T
  case var x => rfl
  case func l f ts ih =>
    simp only [LHom.onTerm, Term.relabel, Term.func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i

@[simp]
theorem onBoundedFormula_relabel {α β : Type _} {L L' : Language} {n k : ℕ}
    (ϕ : L →ᴸ L') (F : L.BoundedFormula α n) (g : α → β ⊕ Fin k) :
    ϕ.onBoundedFormula (F.relabel g) = (ϕ.onBoundedFormula F).relabel g := by
  induction F
  case falsum i => rfl
  case equal i t₁ t₂ =>
    simp only [LHom.onBoundedFormula, onTerm_relabel]
    rfl
  case rel n l R ts =>
    simp only [LHom.onBoundedFormula, Function.comp, onTerm_relabel]
    rfl
  case imp i f₁ f₂ ih₁ ih₂ =>
    simp only [LHom.onBoundedFormula, BoundedFormula.relabel_imp, BoundedFormula.imp.injEq]
    exact ⟨ih₁, ih₂⟩
  case all i f ih =>
    simp only [LHom.onBoundedFormula, BoundedFormula.castLE_rfl, BoundedFormula.relabel_all,
      Nat.add_eq, Nat.add_zero, BoundedFormula.all.injEq]
    exact ih

@[simp]
theorem onFormula_relabel {α β : Type _} {L L' : Language}
    (ϕ : L →ᴸ L') (F : L.Formula α) (g : α → β) :
    ϕ.onFormula (F.relabel g) = (ϕ.onFormula F).relabel g :=
  onBoundedFormula_relabel ϕ F _

@[simp]
theorem onFormula_realize_of_isEmpty {α : Type _} [IsEmpty α] (F : L.Formula α) (v : α → M) :
    (ϕ.onFormula F).Realize v ↔ F.Realize v := by
  have : v = (default : Empty → M) ∘ (default : α → Empty)
  · ext x
    exact IsEmpty.elim inferInstance x
  rw [this, ← Formula.realize_relabel, ← Formula.realize_relabel]
  change M ⊨ (ϕ.onFormula F).relabel default ↔ M ⊨ F.relabel default
  rw [← map_onSentence (ϕ := ϕ) (F.relabel default), ← onFormula_relabel]
  rfl

open scoped Classical in
/-- If the `Prop` is false, apply a `∼` to the formula. -/
def xnorProp {α : Type _} {n : ℕ} (F : L.BoundedFormula α n) (P : Prop) : L.BoundedFormula α n :=
  if P then F else ∼F

theorem xnorProp_true {α : Type _} {n : ℕ} {F : L.BoundedFormula α n} {P : Prop} (h : P) :
    xnorProp F P = F := by
  rw [xnorProp, if_pos h]

theorem xnorProp_false {α : Type _} {n : ℕ} {F : L.BoundedFormula α n} {P : Prop} (h : ¬P) :
    xnorProp F P = ∼F := by
  rw [xnorProp, if_neg h]

theorem xnorProp_realize {α : Type _} {n : ℕ} {F : L.BoundedFormula α n} {P : Prop}
    {v : α → M} {xs : Fin n → M} :
    (xnorProp F P).Realize v xs ↔ (F.Realize v xs ↔ P) := by
  by_cases h : P
  · simp only [h, xnorProp_true, iff_true]
  · simp only [h, not_false_eq_true, xnorProp_false, BoundedFormula.realize_not, iff_false]

@[simp]
theorem onBoundedFormula_ex {α : Type _} {n : ℕ} (F : L.BoundedFormula α (n + 1)) :
    ϕ.onBoundedFormula (∃' F) = ∃' ϕ.onBoundedFormula F :=
  rfl

@[simp]
theorem onBoundedFormula_inf {α : Type _} {n : ℕ} (F G : L.BoundedFormula α n) :
    ϕ.onBoundedFormula (F ⊓ G) = ϕ.onBoundedFormula F ⊓ ϕ.onBoundedFormula G :=
  rfl

theorem onBoundedFormula_foldr {α β : Type _} {n : ℕ} (l : List β) (F : β → L.BoundedFormula α n) :
    ϕ.onBoundedFormula (List.foldr (· ⊓ ·) ⊤ (l.map F)) =
    List.foldr (· ⊓ ·) ⊤ (l.map (fun i => ϕ.onBoundedFormula (F i))) := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, List.foldr_cons, List.map_cons, List.foldr_cons, onBoundedFormula_inf, ih]

@[simp]
theorem onBoundedFormula_iInf {α β : Type _} {n : ℕ} (s : Finset β) (F : β → L.BoundedFormula α n) :
    ϕ.onBoundedFormula (BoundedFormula.iInf s F) =
    BoundedFormula.iInf s (fun i => ϕ.onBoundedFormula (F i)) := by
  rw [BoundedFormula.iInf, BoundedFormula.iInf, onBoundedFormula_foldr]

@[simp]
theorem onBoundedFormula_xnorProp {α : Type _} {n : ℕ} (F : L.BoundedFormula α n) (P : Prop) :
    ϕ.onBoundedFormula (xnorProp F P) = xnorProp (ϕ.onBoundedFormula F) P := by
  unfold xnorProp
  split_ifs <;> rfl

private def Q₁ {α : Type _} [Fintype α] {n : ℕ}
    (P : α → L.Formula (Fin (n + 1))) (ε : α → Prop) : L.Formula (Fin n) :=
  letI Q' : L.BoundedFormula (Fin n) 1 :=
    BoundedFormula.iInf (Finset.univ)
    (fun i =>
      xnorProp (BoundedFormula.relabel
        (fun j : Fin (n + 1) => if h : (j : ℕ) < n then Sum.inl ⟨j, h⟩ else Sum.inr 0) (P i))
        (ε i))
  ∃' Q'

private def Q₂ {α : Type _} [Fintype α] {n : ℕ}
    (P : α → L.Formula (Fin (n + 1))) (ε : α → Prop) : L.Formula (Fin n) :=
  letI Q' : L.BoundedFormula (Fin n) 1 :=
    BoundedFormula.iInf (Finset.univ)
    (fun i =>
      xnorProp (BoundedFormula.relabel (Fin.cases (Sum.inr 0) Sum.inl) (P i)) (ε i))
  ∃' Q'

private theorem Q₁_realize {α : Type _} [Fintype α] {n : ℕ}
    (P : α → L.Formula (Fin (n + 1))) (ε : α → Prop) (e : Fin (n + 1) → M) :
    (Q₁ P ε).Realize (fun j => e j) ↔
    ∃ x : M, ∀ i : α,
      (BoundedFormula.relabel
        (fun j : Fin (n + 1) => if h : (j : ℕ) < n then Sum.inl ⟨j, h⟩ else Sum.inr 0)
        (P i) : L.BoundedFormula (Fin n) 1).Realize (fun j => e j) (fun _ => x) ↔
      ε i := by
  simp only [Q₁, Formula.Realize, BoundedFormula.realize_ex, BoundedFormula.realize_iInf,
    xnorProp_realize]
  constructor
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i
    exact h i (Finset.mem_univ i)
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i _
    exact h i

private theorem Q₁_realize_onFormula {α : Type _} [Fintype α] {n : ℕ}
    (P : α → L.Formula (Fin (n + 1))) (ε : α → Prop) (e : Fin (n + 1) → M) :
    (ϕ.onFormula (Q₁ P ε)).Realize (fun j => e j.succ) ↔
    ∃ x : M, ∀ i : α,
      (BoundedFormula.relabel
        (fun j : Fin (n + 1) => if h : (j : ℕ) < n then Sum.inl ⟨j, h⟩ else Sum.inr 0)
        (ϕ.onFormula (P i)) : L.BoundedFormula (Fin n) 1).Realize (fun j => e j.succ) (fun _ => x) ↔
      ε i := by
  simp only [Q₁, Formula.Realize, LHom.onFormula, onBoundedFormula_ex, onBoundedFormula_iInf,
    onBoundedFormula_xnorProp, onBoundedFormula_relabel]
  simp only [BoundedFormula.realize_ex, BoundedFormula.realize_iInf, xnorProp_realize]
  constructor
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i
    exact h i (Finset.mem_univ i)
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i _
    exact h i

private theorem Q₂_realize {α : Type _} [Fintype α] {n : ℕ}
    (P : α → L.Formula (Fin (n + 1))) (ε : α → Prop) (e : Fin (n + 1) → M) :
    (Q₂ P ε).Realize (fun j => e j) ↔
    ∃ x : M, ∀ i : α,
      (BoundedFormula.relabel (Fin.cases (Sum.inr 0) Sum.inl) (P i) :
        L.BoundedFormula (Fin n) 1).Realize (fun j => e j) (fun _ => x) ↔
      ε i := by
  simp only [Q₂, Formula.Realize, BoundedFormula.realize_ex, BoundedFormula.realize_iInf,
    xnorProp_realize]
  constructor
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i
    exact h i (Finset.mem_univ i)
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i _
    exact h i

private theorem Q₂_realize_onFormula {α : Type _} [Fintype α] {n : ℕ}
    (P : α → L.Formula (Fin (n + 1))) (ε : α → Prop) (e : Fin (n + 1) → M) :
    (ϕ.onFormula (Q₂ P ε)).Realize (fun j => e j.succ) ↔
    ∃ x : M, ∀ i : α,
      (BoundedFormula.relabel (Fin.cases (Sum.inr 0) Sum.inl)
        (ϕ.onFormula (P i)) : L.BoundedFormula (Fin n) 1).Realize (fun j => e j.succ) (fun _ => x) ↔
      ε i := by
  simp only [Q₂, Formula.Realize, LHom.onFormula, onBoundedFormula_ex, onBoundedFormula_iInf,
    onBoundedFormula_xnorProp, onBoundedFormula_relabel]
  simp only [BoundedFormula.realize_ex, BoundedFormula.realize_iInf, xnorProp_realize]
  constructor
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i
    exact h i (Finset.mem_univ i)
  · rintro ⟨x, h⟩
    refine ⟨x, ?_⟩
    intro i _
    exact h i

theorem relabel_realize₁ {n : ℕ} (F : L.Formula (Fin (n + 1))) (e : Fin (n + 1) → M) :
    (BoundedFormula.relabel
      (fun j : Fin (n + 1) => if h : (j : ℕ) < n then Sum.inl ⟨j, h⟩ else Sum.inr 0)
      F : L.BoundedFormula (Fin n) 1).Realize (fun j => e j) (fun _ => e n) ↔
    F.Realize e := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, iff_eq_eq]
  refine congr_arg₂ _ ?_ ?_
  · funext j
    dsimp only [Function.comp]
    by_cases h : (j : ℕ) < n
    · rw [dif_pos h]
      simp only [Fin.coe_eq_castSucc, Nat.add_zero, Fin.cast_nat_eq_last, Fin.castAdd_zero,
        Fin.cast_refl, CompTriple.comp_eq, Sum.elim_inl, Fin.castSucc_mk, Fin.eta]
    · have := eq_of_le_of_not_lt (Nat.le_of_lt_succ j.prop) h
      rw [dif_neg h]
      simp only [Fin.coe_eq_castSucc, Nat.add_zero, Fin.cast_nat_eq_last, Fin.castAdd_zero,
        Fin.cast_refl, CompTriple.comp_eq, Fin.isValue, Sum.elim_inr]
      congr 1
      refine Fin.val_injective ?_
      exact this.symm
  · funext i
    cases Nat.not_lt_zero i i.prop

theorem relabel_realize₂ {n : ℕ} (F : L.Formula (Fin (n + 1))) (e : Fin (n + 1) → M) (x : M) :
    (BoundedFormula.relabel
      (fun j : Fin (n + 1) => if h : (j : ℕ) < n then Sum.inl ⟨j, h⟩ else Sum.inr 0)
      F : L.BoundedFormula (Fin n) 1).Realize (fun j => e j.succ) (fun _ => x) ↔
    F.Realize (fun j => if h : (j.succ : ℕ) < n + 1 then e ⟨j.succ, h⟩ else x) := by
  refine Iff.trans ?_
    (relabel_realize₁ M F (fun j => if h : (j.succ : ℕ) < n + 1 then e ⟨j.succ, h⟩ else x))
  rw [iff_eq_eq]
  refine congr_arg₂ _ ?_ ?_
  · funext j
    simp only [Fin.coe_eq_castSucc, Fin.val_succ, Fin.coe_castSucc, add_lt_add_iff_right, Fin.is_lt,
      ↓reduceDite]
    rfl
  · funext
    simp only [Fin.cast_nat_eq_last, Fin.succ_last, Fin.val_last, lt_self_iff_false, ↓reduceDite]

theorem relabel_realize₃ {n : ℕ} (F : L.Formula (Fin (n + 1))) (e : Fin (n + 1) → M) :
    (BoundedFormula.relabel
      (Fin.cases (Sum.inr 0) Sum.inl)
      F : L.BoundedFormula (Fin n) 1).Realize (fun j => e j.succ) (fun _ => e 0) ↔
    F.Realize e := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, iff_eq_eq]
  refine congr_arg₂ _ ?_ ?_
  · funext j
    exact Fin.cases rfl (fun _ => rfl) j
  · funext i
    cases Nat.not_lt_zero i i.prop

theorem relabel_realize₄ {n : ℕ} (F : L.Formula (Fin (n + 1))) (e : Fin (n + 1) → M) (x : M) :
    (BoundedFormula.relabel (Fin.cases (Sum.inr 0) Sum.inl) F
      : L.BoundedFormula (Fin n) 1).Realize (fun j => e j) (fun _ => x) ↔
    F.Realize (Fin.cases x (fun j => e j)) := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, iff_eq_eq]
  refine congr_arg₂ _ ?_ ?_
  · funext j
    exact Fin.cases rfl (fun _ => rfl) j
  · funext i
    cases Nat.not_lt_zero i i.prop

theorem specker_aux' {α : Type _} [Fintype α] {n : ℕ} (A : L.BoundedFormula Empty 1)
    (P : α → L.Formula (Fin n)) (k : Fin (n + 1)) :
    ∃ e : Fin (n + 1) → M,
    (∀ x : M, A.Realize Empty.elim (fun _ => x) → A.Realize Empty.elim (fun _ => e k)) ∧
    ∀ i, (P i).Realize (fun j => e j) ↔ (ϕ.onFormula (P i)).Realize (fun j => e j.succ) := by
  classical
  induction n generalizing α with
  | zero =>
    refine ⟨fun _ => Classical.epsilon (fun x : M => A.Realize Empty.elim (fun _ => x)), ?_, ?_⟩
    · intro x hx
      exact Classical.epsilon_spec (p := fun x : M => A.Realize Empty.elim (fun _ => x)) ⟨x, hx⟩
    · simp only [onFormula_realize_of_isEmpty, implies_true]
  | succ n ih =>
    refine Fin.cases ?_ ?_ k
    · obtain ⟨e, he₁, he₂⟩ := ih (Q₁ P) 0
      specialize he₂ (fun i => (P i).Realize e)
      rw [Q₁_realize, Q₁_realize_onFormula] at he₂
      have := he₂.mp ?_
      swap
      · refine ⟨e n, ?_⟩
        intro i
        rw [relabel_realize₁]
      obtain ⟨x, hx⟩ := this
      refine ⟨fun j => if h : (j : ℕ) < n + 1 then e ⟨j, h⟩ else x, ?_, ?_⟩
      · intro y hy
        dsimp only
        rw [dif_pos (by exact Nat.zero_lt_succ _)]
        exact he₁ y hy
      · intro i
        have := hx i
        rw [relabel_realize₂] at this
        rw [this, iff_eq_eq]
        refine congr_arg _ ?_
        funext j
        simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.is_lt, ↓reduceDite, Fin.eta]
    · intro k
      obtain ⟨e, he₁, he₂⟩ := ih (Q₂ P) k
      specialize he₂ (fun i => (ϕ.onFormula (P i)).Realize e)
      rw [Q₂_realize, Q₂_realize_onFormula] at he₂
      have := he₂.mpr ?_
      swap
      · refine ⟨e 0, ?_⟩
        intro i
        rw [relabel_realize₃]
      obtain ⟨x, hx⟩ := this
      refine ⟨Fin.cases x e, ?_, ?_⟩
      · intro y hy
        exact he₁ y hy
      · intro i
        have := hx i
        rw [relabel_realize₄] at this
        refine Iff.trans ?_ this
        rw [iff_eq_eq]
        refine congr_arg _ ?_
        funext j
        refine Fin.cases rfl ?_ j
        intro j
        dsimp only
        have : (j.succ : Fin (n + 2)) = (j : Fin (n + 1)).succ
        · refine Fin.val_injective ?_
          simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.coe_eq_castSucc,
            Fin.coe_castSucc]
          rw [Fin.val_add_eq_ite, if_neg]
          · simp only [Fin.val_nat_cast, Fin.val_one, add_left_inj, Nat.mod_succ_eq_iff_lt]
            exact j.prop.trans (by linarith)
          · rw [Fin.val_cast_of_lt]
            · have := j.prop
              simp only [Fin.val_one, not_le, add_lt_add_iff_right, gt_iff_lt]
              linarith
            · exact j.prop.trans (by linarith)
        rw [this]
        rfl

theorem realize_boundedFormula_congr_freeVarFinset {M : Type _} [L.Structure M]
    {α : Type _} [DecidableEq α]
    {n : ℕ} {F : L.BoundedFormula α n} {v₁ v₂ : α → M} {xs₁ xs₂ : Fin n → M}
    (hv : ∀ i ∈ F.freeVarFinset, v₁ i = v₂ i) (hxs : ∀ i : Fin n, xs₁ i = xs₂ i) :
    F.Realize v₁ xs₁ ↔ F.Realize v₂ xs₂ := by
  rw [← F.realize_restrictFreeVar subset_rfl, ← F.realize_restrictFreeVar subset_rfl, iff_eq_eq]
  refine congr_arg₂ _ ?_ ?_
  · funext i
    exact hv i i.prop
  · funext i
    exact hxs i

theorem realize_formula_congr_freeVarFinset {M : Type _} [L.Structure M]
    {α : Type _} [DecidableEq α] {F : L.Formula α} {t₁ t₂ : α → M}
    (h : ∀ v ∈ F.freeVarFinset, t₁ v = t₂ v) :
    F.Realize t₁ ↔ F.Realize t₂ :=
  realize_boundedFormula_congr_freeVarFinset h (fun _ => rfl)

@[simp]
theorem onTerm_freeVarFinset {α β : Type _} [DecidableEq α] {T : L.Term (α ⊕ β)} :
    (ϕ.onTerm T).varFinsetLeft = T.varFinsetLeft := by
  induction T with
  | var => rfl
  | func _ ts ih => simp only [Term.varFinsetLeft, ih]

@[simp]
theorem onBoundedFormula_freeVarFinset {α : Type _} [DecidableEq α]
    {n : ℕ} {F : L.BoundedFormula α n} :
    (ϕ.onBoundedFormula F).freeVarFinset = F.freeVarFinset := by
  induction F with
  | falsum => rfl
  | equal t₁ t₂ => simp only [BoundedFormula.freeVarFinset, onTerm_freeVarFinset]
  | rel _ ts => simp only [BoundedFormula.freeVarFinset, Function.comp_apply, onTerm_freeVarFinset]
  | imp f₁ f₂ ih₁ ih₂ => simp only [BoundedFormula.freeVarFinset, ih₁, ih₂]
  | all f ih => simp only [BoundedFormula.freeVarFinset, ih]

@[simp]
theorem onFormula_freeVarFinset {α : Type _} [DecidableEq α] {F : L.Formula α} :
    (ϕ.onFormula F).freeVarFinset = F.freeVarFinset :=
  onBoundedFormula_freeVarFinset ϕ

theorem specker_aux (A : L.BoundedFormula Empty 1) (P : Finset (L.Formula ℤ)) :
    ∃ e : ℤ → M,
    (∀ x : M, A.Realize Empty.elim (fun _ => x) → A.Realize Empty.elim (fun _ => e 0)) ∧
    ∀ F ∈ P, F.Realize e ↔ (ϕ.onFormula F).Realize (e ∘ (· + 1)) := by
  have : ∃ n : ℕ, ∀ F ∈ P, ∀ j ∈ F.freeVarFinset, -n < j ∧ j < n
  · have : ∀ n : ℕ, ∀ j : ℤ, j.natAbs < n ↔ -n < j ∧ j < n := by omega
    refine ⟨P.sup (fun F => F.freeVarFinset.sup Int.natAbs) + 1, ?_⟩
    intro F hF j hj
    rw [← this, Nat.lt_succ]
    exact le_trans (Finset.le_sup hj)
      (Finset.le_sup (f := fun F => F.freeVarFinset.sup Int.natAbs) hF)
  obtain ⟨n, hP⟩ := this
  obtain ⟨e, he₁, he₂⟩ := specker_aux' ϕ M A
    (fun F : P => F.val.relabel (fun j : ℤ => ((j + n).toNat : Fin (2 * n + 1)))) n
  refine ⟨fun j => e (j + n).toNat, ?_, ?_⟩
  · intro x hx
    simp only [zero_add, Int.toNat_ofNat]
    exact he₁ x hx
  · intro F hF
    convert he₂ ⟨F, hF⟩ using 1
    · simp only [Fin.coe_eq_castSucc, Formula.realize_relabel]
      refine realize_formula_congr_freeVarFinset ?_
      intro j hj
      simp only [Function.comp_apply]
      refine congr_arg _ ?_
      refine Fin.val_injective ?_
      simp only [Fin.val_nat_cast, Fin.coe_castSucc]
      have := hP F hF j hj
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
      · rw [Int.toNat_lt' (by exact Nat.succ_ne_zero _)]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, gt_iff_lt]
        linarith
      · rw [Int.toNat_lt' (by exact Nat.succ_ne_zero _)]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, gt_iff_lt]
        linarith
    · simp only [onFormula_relabel, Formula.realize_relabel]
      refine realize_formula_congr_freeVarFinset ?_
      intro j hj
      simp only [Function.comp_apply]
      refine congr_arg _ ?_
      refine Fin.val_injective ?_
      simp only [Fin.val_nat_cast, Fin.val_succ]
      rw [onFormula_freeVarFinset] at hj
      have := hP F hF j hj
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
      · rw [add_assoc, add_comm 1, ← add_assoc, ← Int.toNat_add_nat]
        rfl
        linarith
      · rw [Int.toNat_lt' (by exact Nat.succ_ne_zero _)]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, gt_iff_lt]
        linarith
      · rw [Int.toNat_lt' (by exact Nat.succ_ne_zero _)]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, gt_iff_lt]
        linarith

/-- Define the type raising endomorphism on constants indexed by `ℤ`. -/
def raise : constantsOn ℤ →ᴸ constantsOn ℤ where
  onFunction := fun n => match n with
    | 0 => fun c : ℤ => c + 1
    | 1 => PEmpty.elim
    | 2 => PEmpty.elim
    | (_ + 3) => PEmpty.elim
  onRelation := fun n => match n with
    | 0 => PEmpty.elim
    | 1 => PEmpty.elim
    | 2 => PEmpty.elim
    | (_ + 3) => PEmpty.elim

def speckerTheory₁ {L : Language} (ϕ : L →ᴸ L) (T : L.Theory) (A : L.BoundedFormula Empty 1) :
    L[[ℤ]].Theory :=
  (L.lhomWithConstants ℤ).onTheory T ∪
  {∃' ((L.lhomWithConstants ℤ).onBoundedFormula A) ⟹
    ((L.lhomWithConstants ℤ).onFormula A.toFormula).subst (fun _ => Constants.term (L.con 0))} ∪
  ⋃ (F : L[[ℤ]].Sentence), {F ⇔ (ϕ.sumMap raise).onSentence F}

def speckerTheory₁' {L : Language} (ϕ : L →ᴸ L) (T : L.Theory) (A : L.BoundedFormula Empty 1) :
    L[[ℤ]].Theory :=
  (L.lhomWithConstants ℤ).onTheory T ∪
  {∃' ((L.lhomWithConstants ℤ).onBoundedFormula A) ⟹
    ((L.lhomWithConstants ℤ).onFormula A.toFormula).subst (fun _ => Constants.term (L.con 0))} ∪
  ⋃ (F : L[[ℤ]].Sentence), {F ⇔ (ϕ.sumMap raise).onSentence F}

theorem isSatisfiable_union_iUnion_iff_isSatisfiable_union_iUnion_finset {L : Language} {ι : Type*}
    (T₁ : L.Theory) (T₂ : ι → L.Theory) :
    IsSatisfiable (T₁ ∪ ⋃ i, T₂ i) ↔ ∀ s : Finset ι, IsSatisfiable (T₁ ∪ ⋃ i ∈ s, T₂ i) := by
  constructor
  · intro h s
    refine h.mono ?_
    simp only [Set.union_subset_iff, Set.subset_union_left, Set.iUnion_subset_iff, true_and]
    intro i _ S hS
    simp only [Set.mem_union, Set.mem_iUnion]
    exact Or.inr ⟨i, hS⟩
  obtain (hι | hι) := isEmpty_or_nonempty ι
  · simp only [Set.iUnion_of_empty, Set.union_empty, forall_const, imp_self]
  · rw [Set.union_iUnion T₁ T₂, isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset]
    intro h s
    refine (h s).mono ?_
    simp only [Set.iUnion_subset_iff, Set.union_subset_iff, Set.subset_union_left, true_and]
    intro i hi S hS
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
    exact Or.inr ⟨i, hi, hS⟩

theorem isEndomorphismOn_of_isTheoryEndomorphism {L : Language} (ϕ : L →ᴸ L) (T : L.Theory)
    (hT : T.IsMaximal) (hT' : IsTheoryEndomorphism ϕ T) (M : Type _)
    [L.Structure M] [M ⊨ T] : IsEndomorphismOn ϕ M := by
  constructor
  intro S
  obtain (hS | hS) := hT.2 S
  · have hS' := (hT'.map_onSentence S).mpr hS
    simp only [Model.realize_of_mem S hS, Model.realize_of_mem _ hS']
  · have hS' := (hT'.map_onSentence _).mpr hS
    have h₁ : ¬M ⊨ S := Model.realize_of_mem (M := M) _ hS
    have h₂ : ¬M ⊨ ϕ.onSentence S := Model.realize_of_mem (M := M) _ hS'
    simp only [h₂, h₁]

@[simp]
theorem onBoundedFormula_relabelEquiv {α β : Type _} {L L' : Language} {n : ℕ}
    (ϕ : L →ᴸ L') (F : L.BoundedFormula α n) (g : α ≃ β) :
    ϕ.onBoundedFormula (BoundedFormula.relabelEquiv g F) =
    BoundedFormula.relabelEquiv g (ϕ.onBoundedFormula F) := by
  induction F
  case falsum i => rfl
  case equal i t₁ t₂ =>
    simp only [LHom.onBoundedFormula, Term.relabelEquiv_apply, onTerm_relabel,
      BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply, Equiv.coe_refl]
    rfl
  case rel n l R ts =>
    simp only [LHom.onBoundedFormula, Equiv.refl_apply, Term.relabelEquiv_apply, Function.comp,
      onTerm_relabel, BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply,
      Equiv.coe_refl]
    rfl
  case imp i f₁ f₂ ih₁ ih₂ =>
    simp only [LHom.onBoundedFormula, Equiv.coe_refl, BoundedFormula.relabelEquiv,
      BoundedFormula.mapTermRelEquiv_apply, BoundedFormula.mapTermRel, BoundedFormula.imp.injEq]
    exact ⟨ih₁, ih₂⟩
  case all i f ih =>
    simp only [LHom.onBoundedFormula, Equiv.coe_refl, id_eq, BoundedFormula.relabelEquiv,
      BoundedFormula.mapTermRelEquiv_apply, BoundedFormula.mapTermRel, BoundedFormula.all.injEq]
    exact ih

@[simp]
theorem onTerm_constantsVarsEquivLeft {L L' : Language} {ϕ : L →ᴸ L'}
    {α β : Type _} {n : ℕ} (T : L[[α]].Term (β ⊕ Fin n)) :
    ϕ.onTerm (Term.constantsToVars T) =
    Term.constantsToVars ((ϕ.sumMap (LHom.id _)).onTerm T) := by
  induction' T with x l f ts ih
  · rfl
  · cases' f with f f
    · cases' l with l
      · simp only [LHom.onTerm, Term.constantsToVars, constantsOn, mk₂_Functions, Nat.zero_eq,
          LHom.sumMap_onFunction, LHom.id_onFunction, id_eq, Sum.map_inl, Term.func.injEq,
          heq_eq_eq, true_and]
        funext i
        cases i.val.not_lt_zero i.prop
      · simp only [LHom.onTerm, ih, constantsOn, Term.constantsToVars, mk₂_Functions,
          LHom.sumMap_onFunction, LHom.id_onFunction, id_eq, Sum.map_inl]
    · cases' l with l
      · rfl
      cases' l with l; cases f
      cases' l with l; cases f
      cases f

theorem onRelation_sumEmpty_eq {L L' : Language} (ϕ : L →ᴸ L') {α : Type _} {l : ℕ}
    (R : L[[α]].Relations l) :
    ϕ.onRelation (Equiv.sumEmpty (L.Relations l) ((constantsOn α).Relations l) R) =
    Equiv.sumEmpty (L'.Relations l) ((constantsOn α).Relations l)
      (Sum.map (fun f => ϕ.onRelation f) id R) := by
  obtain (R | R) := R
  · rfl
  · cases' l with l
    cases R
    cases' l with l
    cases R
    cases' l with l
    cases R
    cases R

@[simp]
theorem onBoundedFormula_constantsVarsEquiv {L L' : Language} {ϕ : L →ᴸ L'}
    {α β : Type _} {n : ℕ} (F : L[[α]].BoundedFormula β n) :
    ϕ.onBoundedFormula (BoundedFormula.constantsVarsEquiv F) =
    BoundedFormula.constantsVarsEquiv ((ϕ.sumMap (LHom.id _)).onBoundedFormula F) := by
  induction F
  case falsum i => rfl
  case equal i t₁ t₂ =>
    simp only [LHom.onBoundedFormula, Term.constantsVarsEquivLeft_apply, onTerm_relabel,
      onTerm_constantsVarsEquivLeft, constantsOn, BoundedFormula.constantsVarsEquiv, mk₂_Relations,
      BoundedFormula.mapTermRelEquiv_apply, BoundedFormula.mapTermRel]
    rfl
  case rel n l R ts =>
    simp only [LHom.onBoundedFormula, constantsOn, mk₂_Relations, Term.constantsVarsEquivLeft_apply,
      Function.comp, onTerm_relabel, onTerm_constantsVarsEquivLeft,
      BoundedFormula.constantsVarsEquiv, LHom.sumMap_onRelation, LHom.id_onRelation, id_eq,
      BoundedFormula.mapTermRelEquiv_apply, BoundedFormula.mapTermRel, Relations.boundedFormula]
    congr
    exact onRelation_sumEmpty_eq ϕ R
  case imp i f₁ f₂ ih₁ ih₂ =>
    simp only [LHom.onBoundedFormula, constantsOn, mk₂_Relations, BoundedFormula.constantsVarsEquiv,
      BoundedFormula.mapTermRelEquiv_apply, BoundedFormula.mapTermRel, BoundedFormula.imp.injEq]
    exact ⟨ih₁, ih₂⟩
  case all i f ih =>
    simp only [LHom.onBoundedFormula, constantsOn, mk₂_Relations, id_eq,
      BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv_apply,
      BoundedFormula.mapTermRel, BoundedFormula.all.injEq]
    exact ih

@[simp]
theorem onFormula_equivSentence_symm {L L' : Language} {ϕ : L →ᴸ L'}
    {α : Type _} (S : L[[α]].Sentence) :
    ϕ.onFormula (Formula.equivSentence.symm S) =
    Formula.equivSentence.symm ((ϕ.sumMap (LHom.id _)).onSentence S) := by
  simp only [LHom.onFormula, Formula.equivSentence, Equiv.symm_symm, Equiv.trans_apply,
    onBoundedFormula_relabelEquiv, onBoundedFormula_constantsVarsEquiv, constantsOn,
    LHom.onSentence]

theorem relabel_relabelEquiv' {α β : Type _} {n : ℕ}
    (F : L.BoundedFormula (α ⊕ Empty) n) (f : α → β) :
    BoundedFormula.relabel (n := 0) (Sum.inl ∘ f)
      (BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty) F) =
    BoundedFormula.relabelEquiv (Equiv.sumEmpty β Empty) (F.relabel (Sum.inl ∘ Sum.map f id)) := by
  induction F
  case falsum i => rfl
  case equal i t₁ t₂ =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.relabelAux,
      Term.relabelEquiv_apply, Term.relabel_relabel, BoundedFormula.relabelEquiv,
      BoundedFormula.mapTermRelEquiv_apply, BoundedFormula.equal.injEq]
    refine ⟨?_, ?_⟩
    · congr 1
      funext x
      obtain ((x | x) | x) := x
      · rfl
      · cases x
      · rfl
    · congr 1
      funext x
      obtain ((x | x) | x) := x
      · rfl
      · cases x
      · rfl
  case rel n l R ts =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, Equiv.refl_apply, id_eq,
      BoundedFormula.relabelAux, Term.relabelEquiv_apply, Term.relabel_relabel,
      BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply, BoundedFormula.rel.injEq,
      heq_eq_eq, true_and]
    funext i
    congr 1
    funext x
    obtain ((x | x) | x) := x
    · rfl
    · cases x
    · rfl
  case imp i f₁ f₂ ih₁ ih₂ =>
    simp only [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply, Equiv.coe_refl,
      BoundedFormula.relabel_imp, BoundedFormula.mapTermRel] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  case all i f ih =>
    simp only [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply, Equiv.coe_refl,
      BoundedFormula.mapTermRel, id_eq, BoundedFormula.relabel_all, Nat.add_eq, Nat.add_zero,
      BoundedFormula.all.injEq] at ih ⊢
    exact ih

theorem relabel_relabelEquiv {α β : Type _} (F : L.Formula (α ⊕ Empty)) (f : α → β) :
    Formula.relabel f (BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty) F) =
    BoundedFormula.relabelEquiv (Equiv.sumEmpty β Empty) (F.relabel (Sum.map f id)) :=
  relabel_relabelEquiv' F f

theorem relabel_term_injective {α β : Type _} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (Term.relabel (L := L) f) := by
  intro T₁ T₂ h
  induction T₁ generalizing T₂
  case var x =>
    rw [Term.relabel] at h
    cases T₂
    · simp only [Term.relabel, Term.var.injEq] at h
      cases hf h
      rfl
    · cases h
  case func l f ts ih =>
    rw [Term.relabel] at h
    cases T₂
    · cases h
    · simp only [Term.relabel, Term.func.injEq] at h
      cases h.1
      simp only [heq_eq_eq, true_and] at h
      cases h.1
      simp only [Term.func.injEq, heq_eq_eq, true_and]
      funext i
      exact ih _ (congr_fun h.2 i)

theorem relabel_inl_injective {α : Type _} {n : ℕ} :
    Function.Injective (Term.relabel (L := L) (Sum.inl : α → α ⊕ Fin n)) :=
  relabel_term_injective _ Sum.inl_injective

theorem relabelAux_injective {α β : Type _} {n k : ℕ}
    (f : α → β ⊕ Fin n) (hf : Function.Injective f) :
    Function.Injective (BoundedFormula.relabelAux (n := n) f k) := by
  refine Function.Injective.comp ?_ (Function.Injective.comp ?_ ?_)
  · rw [Sum.map_injective]
    refine ⟨fun _ _ => id, ?_⟩
    exact Equiv.injective _
  · exact Equiv.injective _
  · rw [Sum.map_injective]
    refine ⟨hf, fun _ _ => id⟩

theorem relabel_injective {α β : Type _} {k n : ℕ} (f : α → β ⊕ Fin n) (hf : Function.Injective f) :
    Function.Injective (BoundedFormula.relabel (k := k) (L := L) f) := by
  intro F₁ F₂ h
  induction F₁
  case falsum =>
    cases F₂ <;> cases h; rfl
  case equal n t₁ t₂ =>
    rw [BoundedFormula.relabel] at h
    cases F₂
    case equal =>
      simp only [BoundedFormula.mapTermRel, BoundedFormula.relabel, BoundedFormula.equal.injEq] at h
      cases relabel_term_injective _ (relabelAux_injective f hf) h.1
      cases relabel_term_injective _ (relabelAux_injective f hf) h.2
      rfl
    all_goals cases h
  case rel n l R ts =>
    rw [BoundedFormula.relabel] at h
    cases F₂
    case rel =>
      simp only [BoundedFormula.mapTermRel, id_eq, BoundedFormula.relabel,
        BoundedFormula.rel.injEq] at h
      cases h.1
      simp only [heq_eq_eq, true_and] at h
      cases h.1
      simp only [BoundedFormula.rel.injEq, heq_eq_eq, true_and]
      funext i
      exact relabel_term_injective _ (relabelAux_injective f hf) (congr_fun h.2 i)
    all_goals cases h
  case imp n f₁ f₂ ih₁ ih₂ =>
    rw [BoundedFormula.relabel] at h
    cases F₂
    case imp =>
      simp only [BoundedFormula.mapTermRel, BoundedFormula.relabel, BoundedFormula.imp.injEq] at h
      cases ih₁ h.1
      cases ih₂ h.2
      rfl
    all_goals cases h
  case all n f ih =>
    rw [BoundedFormula.relabel] at h
    cases F₂
    case all =>
      simp only [BoundedFormula.mapTermRel, BoundedFormula.castLE_rfl, BoundedFormula.relabel,
        BoundedFormula.all.injEq] at h
      rw [BoundedFormula.all.injEq]
      refine ih ?_
      simp only [BoundedFormula.relabel]
      exact h
    all_goals cases h

theorem toFormula_injective {α : Type _} {n : ℕ} :
    Function.Injective (BoundedFormula.toFormula (L := L) (α := α) (n := n)) := by
  intro F₁ F₂ h
  induction F₁
  case falsum n =>
    cases F₂ <;> cases h; rfl
  case equal n t₁ t₂ =>
    rw [BoundedFormula.toFormula] at h
    cases F₂
    case equal =>
      simp only [Term.equal, Term.bdEqual, BoundedFormula.toFormula, BoundedFormula.equal.injEq,
        relabel_inl_injective.eq_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    all_goals cases h
  case rel n k R ts =>
    rw [BoundedFormula.toFormula] at h
    cases F₂
    case rel =>
      simp only [Relations.formula, Relations.boundedFormula, BoundedFormula.toFormula,
        BoundedFormula.rel.injEq] at h
      cases h.1
      simp only [heq_eq_eq, true_and] at h
      cases h.1
      simp only [BoundedFormula.rel.injEq, heq_eq_eq, true_and]
      funext i
      exact relabel_inl_injective (congr_fun h.2 i)
    all_goals cases h
  case imp n f₁ f₂ ih₁ ih₂ =>
    rw [BoundedFormula.toFormula] at h
    cases F₂
    case imp =>
      simp only [BoundedFormula.toFormula, BoundedFormula.imp.injEq] at h
      cases ih₁ h.1
      cases ih₂ h.2
      rfl
    all_goals cases h
  case all n f ih =>
    rw [BoundedFormula.toFormula] at h
    cases F₂
    case all =>
      simp only [BoundedFormula.toFormula, BoundedFormula.all.injEq] at h
      rw [BoundedFormula.all.injEq]
      refine ih ?_
      refine relabel_injective _ ?_ h
      intro i j hij
      obtain (i | i) := i <;> obtain (j | j) := j
      · cases hij; rfl
      · simp only [Sum.elim_inl, Function.comp_apply, Sum.elim_inr] at hij
        set c := finSumFinEquiv.symm j
        clear_value c
        cases c
        cases hij
        cases hij
      · simp only [Sum.elim_inl, Function.comp_apply, Sum.elim_inr] at hij
        set c := finSumFinEquiv.symm i
        clear_value c
        cases c
        cases hij
        cases hij
      · simp only [Sum.elim_inr, Function.comp_apply] at hij
        have := (Sum.map_injective (f := Sum.inr) (g := id)).mpr
          ⟨Sum.inr_injective, fun _ _ => id⟩ hij
        rw [EmbeddingLike.apply_eq_iff_eq] at this
        rw [this]
    all_goals cases h

theorem relabelAux_eq {α β : Type _} (f : α ≃ β) {l : ℕ} :
    (Sum.inl ∘ (Equiv.sumCongr f (Equiv.refl (Fin l))) : α ⊕ Fin l → (β ⊕ Fin l) ⊕ Fin 0) =
      (BoundedFormula.relabelAux (Sum.inl ∘ Sum.map id (Fin.cast (zero_add _))) 0 ∘
        Sum.inl ∘ BoundedFormula.relabelAux (Sum.inl ∘ f) l) := by
  funext i
  obtain (i | i) := i
  · rfl
  · simp only [Function.comp_apply, Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, id_eq,
      Nat.add_zero, BoundedFormula.relabelAux, Equiv.sumAssoc_apply_inr, finSumFinEquiv_apply_right,
      Sum.map_inl, Fin.cast_natAdd, Equiv.sumAssoc_apply_inl_inl, Sum.inl.injEq, Sum.inr.injEq]
    rfl

theorem relabel_relabel {α β γ : Type _} {n a b : ℕ} (f : α → β ⊕ Fin a) (g : β → γ ⊕ Fin b)
    (F : L.BoundedFormula α n) :
    (F.relabel f).relabel g =
      (F.relabel (Sum.elim (Sum.map id (finSumFinEquiv ∘ Sum.inl) ∘ g)
        (Sum.inr ∘ finSumFinEquiv ∘ Sum.inr) ∘ f) : L.BoundedFormula γ ((b + a) + n)).castLE
      (by rw [add_assoc]) := by
  induction F
  case falsum n => rfl
  case equal _ l t₁ t₂ =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.relabelAux,
      Term.relabel_relabel, BoundedFormula.castLE, BoundedFormula.equal.injEq]
    refine ⟨?_, ?_⟩
    · congr 1
      funext i
      obtain (i | i) := i
      · simp only [Function.comp_apply, Sum.map_inl, Sum.map_map, CompTriple.comp_eq]
        set c := f i
        clear_value c
        obtain (c | c) := c
        · simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Sum.elim_inl, Function.comp_apply]
          set d := g c
          clear_value d
          obtain (d | d) := d
          · rfl
          · rfl
        · rfl
      · simp only [Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
          finSumFinEquiv_apply_right, Sum.inr.injEq]
        refine Fin.val_injective ?_
        simp only [Fin.coe_natAdd, Fin.coe_castLE]
        rw [add_assoc]
    · congr 1
      funext i
      obtain (i | i) := i
      · simp only [Function.comp_apply, Sum.map_inl, Sum.map_map, CompTriple.comp_eq]
        set c := f i
        clear_value c
        obtain (c | c) := c
        · simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Sum.elim_inl, Function.comp_apply]
          set d := g c
          clear_value d
          obtain (d | d) := d
          · rfl
          · rfl
        · rfl
      · simp only [Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
          finSumFinEquiv_apply_right, Sum.inr.injEq]
        refine Fin.val_injective ?_
        simp only [Fin.coe_natAdd, Fin.coe_castLE]
        rw [add_assoc]
  case rel n k R ts =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, id_eq, BoundedFormula.relabelAux,
      Term.relabel_relabel, BoundedFormula.castLE, BoundedFormula.rel.injEq, heq_eq_eq, true_and]
    funext j
    simp only [Function.comp_apply, Term.relabel_relabel]
    congr 1
    funext i
    obtain (i | i) := i
    · simp only [Function.comp_apply, Sum.map_inl, Sum.map_map, CompTriple.comp_eq]
      set c := f i
      clear_value c
      obtain (c | c) := c
      · simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Sum.elim_inl, Function.comp_apply]
        set d := g c
        clear_value d
        obtain (d | d) := d
        · rfl
        · rfl
      · rfl
    · simp only [Function.comp_apply, Sum.map_inr, id_eq, Equiv.sumAssoc_apply_inr,
        finSumFinEquiv_apply_right, Sum.inr.injEq]
      refine Fin.val_injective ?_
      simp only [Fin.coe_natAdd, Fin.coe_castLE]
      rw [add_assoc]
  case imp n F₁ F₂ ih₁ ih₂ =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.castLE,
      BoundedFormula.imp.injEq] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
    simp only [and_self]
  case all n F ih =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      BoundedFormula.castLE_rfl, BoundedFormula.castLE, BoundedFormula.all.injEq] at ih ⊢
    rw [ih]

theorem finSumFinEquiv_symm_eq (n : ℕ) (i : Fin (0 + (n + 1))) :
    (finSumFinEquiv.symm (Fin.cast (by rw [zero_add]) i) : Fin n ⊕ Fin 1) =
    (finSumFinEquiv.symm i : Fin (0 + n) ⊕ Fin 1).map (Fin.cast (by rw [zero_add])) id := by
  simp only [finSumFinEquiv, Equiv.coe_fn_symm_mk, Fin.addCases]
  split_ifs with h₁ h₂ h₂
  · simp only [Sum.map_inl, Sum.inl.injEq]
    rfl
  · simp only [Fin.coe_cast, zero_add, not_lt] at h₁ h₂
    cases not_lt_of_le h₂ h₁
  · simp only [Fin.coe_cast, not_lt, zero_add] at h₁ h₂
    cases not_lt_of_le h₁ h₂
  · simp only [id_eq, eq_mpr_eq_cast, Fin.cast_trans, Fin.coe_cast, eq_rec_constant, Sum.map_inr,
      Sum.inr.injEq]
    exact Subsingleton.elim _ _

theorem relabel_eq_relabelEquiv' {α β : Type _} {n : ℕ} (f : α ≃ β) (F : L.BoundedFormula α n) :
    (BoundedFormula.relabelEquiv f F).toFormula =
    (F.relabel (n := 0) (Sum.inl ∘ f)).toFormula.relabel
      (Sum.map id (Fin.cast (zero_add _))) := by
  induction F
  case falsum n => rfl
  case equal _ l t₁ t₂ =>
    simp only [BoundedFormula.toFormula, Term.equal, Term.bdEqual, Term.relabelEquiv_apply,
      Term.relabel_relabel, relabelAux_eq, Nat.add_zero, Formula.relabel, BoundedFormula.relabel,
      BoundedFormula.mapTermRel]
  case rel n k R ts =>
    simp only [BoundedFormula.toFormula, Relations.formula, Relations.boundedFormula,
      Equiv.refl_apply, Term.relabelEquiv_apply, Term.relabel_relabel, relabelAux_eq, Nat.add_zero,
      Formula.relabel, id_eq, BoundedFormula.relabel, BoundedFormula.mapTermRel]
  case imp n f₁ f₂ ih₁ ih₂ =>
    simp only [Formula.relabel, BoundedFormula.relabel, BoundedFormula.toFormula, Equiv.coe_refl,
      BoundedFormula.mapTermRel, Nat.add_zero, BoundedFormula.imp.injEq] at ih₁ ih₂ ⊢
    exact ⟨ih₁, ih₂⟩
  case all n F ih =>
    rw [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply] at ih
    rw [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply,
      BoundedFormula.mapTermRel, id, BoundedFormula.toFormula, Formula.relabel,
      BoundedFormula.relabel_all, BoundedFormula.toFormula, BoundedFormula.relabel_all,
      BoundedFormula.all.injEq, ih, Formula.relabel, relabel_relabel, relabel_relabel,
      BoundedFormula.castLE_rfl, BoundedFormula.castLE_rfl]
    congr 1
    funext i
    obtain (i | i) := i
    · rfl
    simp only [Nat.add_zero, Function.comp_apply, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
      Sum.map_map, CompTriple.comp_eq]
    have := finSumFinEquiv_symm_eq n i
    set c : Fin (0 + n) ⊕ Fin 1 := finSumFinEquiv.symm i with hc
    set d : Fin n ⊕ Fin 1 := finSumFinEquiv.symm (Fin.cast (by rw [zero_add]) i) with hd
    clear_value c d
    obtain (c | c) := c
    · rw [Sum.map_inl] at this
      rw [this]
      rfl
    · rw [Sum.map_inr] at this
      rw [this]
      simp only [id_eq, Sum.map_inr, Function.comp_apply, Sum.elim_inr, finSumFinEquiv_apply_right,
        Sum.inr.injEq]
      exact Subsingleton.elim _ _

theorem relabel_id' {α : Type _} {n : ℕ} (F : L.BoundedFormula α n) :
    (BoundedFormula.relabel (Sum.inl ∘ id : α → α ⊕ Fin 0) F).toFormula =
      F.toFormula.relabel (Sum.map id (Fin.cast (by rw [zero_add]))) := sorry

theorem relabel_id {α : Type _} (F : L.Formula α) :
    Formula.relabel id F = F := sorry

theorem relabel_eq_relabelEquiv {α β : Type _} (f : α ≃ β) (F : L.Formula α) :
    BoundedFormula.relabelEquiv f F = F.relabel f := by
  have := relabel_eq_relabelEquiv' f F
  simp only [Nat.add_zero, Fin.cast_refl, Sum.map_id_id, relabel_id] at this
  exact toFormula_injective this

theorem relabel_constantsVarsEquiv' {α β : Type _} {n : ℕ}
    (F : L[[α]].BoundedFormula Empty n) (f : α → β) :
    (BoundedFormula.relabel (n := 0) (Sum.inl ∘ Sum.map f id)
      (BoundedFormula.constantsVarsEquiv F)).toFormula =
    (BoundedFormula.constantsVarsEquiv
      ((L.lhomWithConstantsMap f).onBoundedFormula F)).toFormula.relabel
      (Sum.map id (Fin.cast (zero_add _).symm)) := sorry

theorem relabel_constantsVarsEquiv {α β : Type _} (F : L[[α]].Formula Empty) (f : α → β) :
    Formula.relabel (Sum.map f id) (BoundedFormula.constantsVarsEquiv F) =
    BoundedFormula.constantsVarsEquiv ((L.lhomWithConstantsMap f).onBoundedFormula F) := by
  rw [Formula.relabel]
  have := relabel_constantsVarsEquiv' F f
  simp only [Nat.add_zero, Fin.cast_refl, Sum.map_id_id] at this
  sorry

theorem relabel_equivSentence {α β : Type _} (S : L[[α]].Sentence) (f : α → β) :
    (Formula.equivSentence.symm S).relabel f =
    Formula.equivSentence.symm ((L.lhomWithConstantsMap f).onSentence S) := by
  simp only [Formula.equivSentence, Equiv.symm_symm, Equiv.trans_apply, relabel_relabelEquiv,
    EmbeddingLike.apply_eq_iff_eq, relabel_constantsVarsEquiv]
  rfl

theorem realize_relabelEquiv' {α : Type _} {n : ℕ} (F : L.BoundedFormula (α ⊕ Empty) n)
    (v : α → M) (xs : Fin n → M) :
    BoundedFormula.Realize (BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty) F) v xs ↔
    F.Realize (Sum.elim v Empty.elim) xs := by
  induction F
  case falsum i => rfl
  case equal i t₁ t₂ =>
    simp only [BoundedFormula.Realize, Term.relabelEquiv_apply, Term.realize_relabel]
    rw [iff_eq_eq]
    refine congr_arg₂ _ ?_ ?_
    · congr 1
      funext x
      obtain ((x | x) | x) := x
      · rfl
      · cases x
      · rfl
    · congr 1
      funext x
      obtain ((x | x) | x) := x
      · rfl
      · cases x
      · rfl
  case rel n l R ts =>
    simp only [BoundedFormula.Realize, Equiv.refl_apply, Term.relabelEquiv_apply,
      Term.realize_relabel]
    rw [iff_eq_eq]
    refine congr_arg _ ?_
    funext i
    congr 1
    funext x
    obtain ((x | x) | x) := x
    · rfl
    · cases x
    · rfl
  case imp i f₁ f₂ ih₁ ih₂ =>
    simp only [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply, Equiv.coe_refl,
      BoundedFormula.mapTermRel, BoundedFormula.realize_imp] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  case all i f ih =>
    simp only [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply, Equiv.coe_refl,
      BoundedFormula.mapTermRel, id_eq, BoundedFormula.realize_all] at ih ⊢
    constructor
    · intro h y
      rw [← ih (Fin.snoc xs y)]
      exact h y
    · intro h y
      rw [ih (Fin.snoc xs y)]
      exact h y

theorem realize_relabelEquiv {α : Type _} (F : L.Formula (α ⊕ Empty)) (v : α → M) :
    Formula.Realize (BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty) F) v ↔
    F.Realize (Sum.elim v Empty.elim) :=
  realize_relabelEquiv' M F v default

-- theorem realize_constantsVarsEquiv {α : Type _} {n : ℕ} (F : L.BoundedFormula α n) (v : α → M) :
--     F.Realize (BoundedFormula.constantsVarsEquiv F) (Sum.elim v Empty.elim) := sorry

theorem realize_equivSentence {α : Type _} (S : L[[α]].Sentence) (v : α → M) :
    (Formula.equivSentence.symm S).Realize v =
    letI := constantsOn.structure v
    S.Realize M := by
  simp only [Formula.equivSentence, Equiv.symm_symm, Equiv.trans_apply, eq_iff_iff,
    realize_relabelEquiv]
  sorry

@[simp]
theorem equivSentence_symm_iff {α : Type _} (S T : L[[α]].Sentence) :
    Formula.equivSentence.symm (S ⇔ T) =
    Formula.equivSentence.symm S ⇔ Formula.equivSentence.symm T :=
  rfl

theorem comp_add_id_eq {L : Language} (ϕ : L →ᴸ L) :
    LHom.comp (L.lhomWithConstantsMap (· + 1)) (ϕ.sumMap (LHom.id _)) = ϕ.sumMap raise := by
  ext : 1
  · funext n f
    cases f
    · rfl
    cases' n with n; rfl
    cases' n with n; rfl
    cases' n with n; rfl
    rfl
  · funext n f
    cases f
    · rfl
    cases' n with n; rfl
    cases' n with n; rfl
    cases' n with n; rfl
    rfl

theorem speckerTheory₁_isSatisfiable {L : Language} (ϕ : L →ᴸ L) (T : L.Theory)
    (hT : T.IsMaximal) (hT' : IsTheoryEndomorphism ϕ T)
    (A : L.BoundedFormula Empty 1) :
    (speckerTheory₁ ϕ T A).IsSatisfiable := by
  rw [speckerTheory₁, isSatisfiable_union_iUnion_iff_isSatisfiable_union_iUnion_finset]
  intro s
  obtain ⟨M⟩ := hT.1
  haveI hendo := isEndomorphismOn_of_isTheoryEndomorphism ϕ T hT hT' M
  obtain ⟨e, he₁, he₂⟩ := specker_aux ϕ M A (s.map Formula.equivSentence.symm.toEmbedding)
  letI iMℤ : (constantsOn ℤ).Structure M := constantsOn.structure e
  refine ⟨@ModelType.mk _ _ M inferInstance ?_ inferInstance⟩
  simp only [model_iff, Set.mem_union, Set.mem_iUnion, exists_prop]
  rintro S ((⟨S, hS, rfl⟩ | rfl) | ⟨S, hS, rfl⟩)
  · rw [LHom.realize_onSentence]
    exact M.is_model.realize_of_mem S hS
  · simp only [Sentence.Realize, LHom.onFormula, Formula.Realize, BoundedFormula.realize_imp,
      BoundedFormula.realize_ex, LHom.realize_onBoundedFormula, BoundedFormula.realize_subst,
      Term.realize_constants, forall_exists_index]
    intro x hx
    have := he₁ x ?_
    · have h := BoundedFormula.realize_toFormula A (Sum.elim Empty.elim (fun _ => e 0))
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
      rw [← h, Formula.Realize] at this
      convert this using 1
      funext i
      obtain (i | _) := i
      · cases i
      · rfl
    · convert hx using 1
  · have := he₂ (Formula.equivSentence.symm S) ?_
    · rw [onFormula_equivSentence_symm] at this
      rw [← realize_equivSentence, equivSentence_symm_iff, Formula.realize_iff, this,
        ← Formula.realize_relabel, iff_eq_eq, relabel_equivSentence]
      refine congr_arg₂ _ ?_ rfl
      simp only [EmbeddingLike.apply_eq_iff_eq, LHom.onSentence, LHom.onFormula]
      have := LHom.comp_onBoundedFormula
        (L.lhomWithConstantsMap (· + (1 : ℤ))) (ϕ.sumMap (LHom.id _)) (α := Empty) (n := 0)
      have := congr_fun this S
      dsimp only [Function.comp] at this
      rw [← this, comp_add_id_eq]
    · simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
      exact hS

end ConNF.Specker
