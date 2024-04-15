import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Have
import Mathlib.ModelTheory.Satisfiability

/-!
# Typical ambiguity
-/

noncomputable section

open FirstOrder Language Theory Structure

namespace ConNF

variable {L : Language} (ϕ : L →ᴸ L) (M : Type _) [L.Structure M] [Nonempty M]

/-- A weaker version of the assumption that `ϕ` is an expansion on `M`. -/
class IsEndomorphismOn (ϕ : L →ᴸ L) (M : Type _) [L.Structure M] : Prop where
  map_onSentence : ∀ (S : L.Sentence), M ⊨ ϕ.onSentence S ↔ M ⊨ S

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

theorem specker_aux {α : Type _} [DecidableEq α] [Fintype α] {n : ℕ} (A : L.BoundedFormula Empty 1)
    (P : α → L.Formula (Fin n))
    (k : Fin (n + 1)) :
    ∃ e : Fin (n + 1) → M,
    (∀ x : M, A.Realize Empty.elim (fun _ => x) → A.Realize Empty.elim (fun _ => e k)) ∧
    ∀ i, (P i).Realize (fun j => e j) ↔ (ϕ.onFormula (P i)).Realize (fun j => e j.succ) := by
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

end ConNF
