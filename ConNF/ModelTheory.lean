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

def speckerTheory₁ {L : Language} (ϕ : L →ᴸ L) (T : L.Theory) (A : L.BoundedFormula Empty 1) :
    L[[ℤ]].Theory :=
  (L.lhomWithConstants ℤ).onTheory T ∪
  {∃' ((L.lhomWithConstants ℤ).onBoundedFormula A) ⟹
    ((L.lhomWithConstants ℤ).onFormula A.toFormula).subst (fun _ => Constants.term (L.con 0))} ∪
  ⋃ (F : L.Formula ℤ), {
    ((L.lhomWithConstants ℤ).onFormula F).subst (fun z => Constants.term (L.con z)) ⇔
    ((L.lhomWithConstants ℤ).onFormula (ϕ.onFormula F)).subst
      (fun z => Constants.term (L.con (z + 1)))
  }

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

theorem speckerTheory₁_isSatisfiable {L : Language} (ϕ : L →ᴸ L) (T : L.Theory)
    (hT : T.IsMaximal) (hT' : IsTheoryEndomorphism ϕ T)
    (A : L.BoundedFormula Empty 1) :
    (speckerTheory₁ ϕ T A).IsSatisfiable := by
  rw [speckerTheory₁, isSatisfiable_union_iUnion_iff_isSatisfiable_union_iUnion_finset]
  intro s
  obtain ⟨M⟩ := hT.1
  haveI hendo := isEndomorphismOn_of_isTheoryEndomorphism ϕ T hT hT' M
  obtain ⟨e, he₁, he₂⟩ := specker_aux ϕ M A s
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
  · have := he₂ S hS
    simp only [Formula.Realize, LHom.onFormula, Sentence.Realize, BoundedFormula.realize_iff,
      BoundedFormula.realize_subst, Term.realize_constants, LHom.realize_onBoundedFormula] at this ⊢
    exact this

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

end ConNF.Specker
