module

public import ConNF.FOA.Coherent

/-!
# Base actions

In this file, we define base actions.

## Main declarations

* `ConNF.BaseAction`: The type of base actions.
-/

@[expose] public noncomputable section

universe u

open Cardinal Ordinal
open scoped SetRel symmDiff

namespace ConNF

variable [Params.{u}]

structure BaseAction where
  atoms : SetRel Atom Atom
  nearLitters : SetRel NearLitter NearLitter
  atoms_dom_small' : Small atoms.dom
  nearLitters_dom_small' : Small nearLitters.dom
  atoms_oneOne' : atoms.OneOne
  mem_iff_mem' {a₁ a₂ : Atom} {N₁ N₂ : NearLitter} :
    a₁ ~[atoms] a₂ → N₁ ~[nearLitters] N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ)
  litter_eq_litter_iff' {N₁ N₂ N₃ N₄ : NearLitter} :
    N₁ ~[nearLitters] N₃ → N₂ ~[nearLitters] N₄ → (N₁ᴸ = N₂ᴸ ↔ N₃ᴸ = N₄ᴸ)
  interference_subset_dom' {N₁ N₂ : NearLitter} :
    N₁ ∈ nearLitters.dom → N₂ ∈ nearLitters.dom → interference N₁ N₂ ⊆ atoms.dom
  interference_subset_cod' {N₁ N₂ : NearLitter} :
    N₁ ∈ nearLitters.cod → N₂ ∈ nearLitters.cod → interference N₁ N₂ ⊆ atoms.cod

namespace BaseAction

theorem mem_symmDiff_iff_mem_symmDiff {ξ : BaseAction} {a₁ a₂ : Atom} {N₁ N₂ N₃ N₄ : NearLitter} :
    a₁ ~[ξ.atoms] a₂ → N₁ ~[ξ.nearLitters] N₂ → N₃ ~[ξ.nearLitters] N₄ →
      (a₁ ∈ N₁ᴬ ∆ N₃ᴬ ↔ a₂ ∈ N₂ᴬ ∆ N₄ᴬ) := by
  intro ha hN₁₂ hN₃₄
  simp only [Set.mem_symmDiff, ξ.mem_iff_mem' ha hN₁₂, ξ.mem_iff_mem' ha hN₃₄]

theorem nearLitters_coinjective (ξ : BaseAction) : ξ.nearLitters.Coinjective := by
  constructor
  intro N₁ N₂ N h₁ h₂
  apply NearLitter.ext
  rw [← Set.symmDiff_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro a ha
  have := ξ.interference_subset_cod' ⟨_, h₁⟩ ⟨_, h₂⟩
  rw [interference_eq_of_litter_eq ((ξ.litter_eq_litter_iff' h₁ h₂).mp rfl)] at this
  obtain ⟨b, hba⟩ := this ha
  rw [← mem_symmDiff_iff_mem_symmDiff hba h₁ h₂] at ha
  simp only [symmDiff_self, Set.bot_eq_empty, Set.mem_empty_iff_false] at ha

theorem nearLitters_injective (ξ : BaseAction) : ξ.nearLitters.Injective := by
  constructor
  intro N₁ N₂ N h₁ h₂
  apply NearLitter.ext
  rw [← Set.symmDiff_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro a ha
  have := ξ.interference_subset_dom' ⟨_, h₁⟩ ⟨_, h₂⟩
  rw [interference_eq_of_litter_eq ((ξ.litter_eq_litter_iff' h₁ h₂).mpr rfl)] at this
  obtain ⟨b, hba⟩ := this ha
  rw [mem_symmDiff_iff_mem_symmDiff hba h₁ h₂] at ha
  simp only [symmDiff_self, Set.bot_eq_empty, Set.mem_empty_iff_false] at ha

instance : BaseActionClass BaseAction where
  atoms := atoms
  atoms_oneOne := atoms_oneOne'
  nearLitters := nearLitters
  nearLitters_oneOne ξ := ⟨ξ.nearLitters_injective, ξ.nearLitters_coinjective⟩

@[ext]
theorem ext {ξ ζ : BaseAction} (atoms : ξᴬ = ζᴬ) (nearLitters : ξᴺ = ζᴺ) : ξ = ζ := by
  cases ξ
  cases ζ
  cases atoms
  cases nearLitters
  rfl

theorem atoms_dom_small (ξ : BaseAction) : Small ξᴬ.dom :=
  ξ.atoms_dom_small'

theorem nearLitters_dom_small (ξ : BaseAction) : Small ξᴺ.dom :=
  ξ.nearLitters_dom_small'

theorem atoms_oneOne (ξ : BaseAction) : ξᴬ.OneOne :=
  ξ.atoms_oneOne'

theorem mem_iff_mem {ξ : BaseAction} {a₁ a₂ : Atom} {N₁ N₂ : NearLitter} :
    a₁ ~[ξᴬ] a₂ → N₁ ~[ξᴺ] N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ) :=
  ξ.mem_iff_mem'

theorem litter_eq_litter_iff {ξ : BaseAction} {N₁ N₂ N₃ N₄ : NearLitter} :
    N₁ ~[ξᴺ] N₃ → N₂ ~[ξᴺ] N₄ → (N₁ᴸ = N₂ᴸ ↔ N₃ᴸ = N₄ᴸ) :=
  ξ.litter_eq_litter_iff'

theorem interference_subset_dom {ξ : BaseAction} {N₁ N₂ : NearLitter} :
    N₁ ∈ ξᴺ.dom → N₂ ∈ ξᴺ.dom → interference N₁ N₂ ⊆ ξᴬ.dom :=
  ξ.interference_subset_dom'

theorem interference_subset_cod {ξ : BaseAction} {N₁ N₂ : NearLitter} :
    N₁ ∈ ξᴺ.cod → N₂ ∈ ξᴺ.cod → interference N₁ N₂ ⊆ ξᴬ.cod :=
  ξ.interference_subset_cod'

theorem atoms_cod_small (ξ : BaseAction) : Small ξᴬ.cod :=
  small_cod_of_small_dom ξ.atoms_oneOne.toCoinjective ξ.atoms_dom_small

theorem nearLitters_cod_small (ξ : BaseAction) : Small ξᴺ.cod :=
  small_cod_of_small_dom ξ.nearLitters_coinjective ξ.nearLitters_dom_small

def inv (ξ : BaseAction) : BaseAction where
  atoms := ξᴬ.inv
  nearLitters := ξᴺ.inv
  atoms_dom_small' := ξ.atoms_cod_small
  nearLitters_dom_small' := ξ.nearLitters_cod_small
  atoms_oneOne' := ξ.atoms_oneOne.inv
  mem_iff_mem' h₁ h₂ := (ξ.mem_iff_mem h₁ h₂).symm
  litter_eq_litter_iff' h₁ h₂ := (ξ.litter_eq_litter_iff h₁ h₂).symm
  interference_subset_dom' := ξ.interference_subset_cod
  interference_subset_cod' := ξ.interference_subset_dom

instance : Inv BaseAction where
  inv := inv

@[simp]
theorem inv_atoms (ξ : BaseAction) : ξ⁻¹ᴬ = ξᴬ.inv :=
  rfl

@[simp]
theorem inv_nearLitters (ξ : BaseAction) : ξ⁻¹ᴺ = ξᴺ.inv :=
  rfl

@[simp]
theorem inv_inv (ξ : BaseAction) : ξ⁻¹⁻¹ = ξ :=
  rfl

theorem nearLitters_oneOne (ξ : BaseAction) : ξᴺ.OneOne :=
  ⟨ξ.nearLitters_injective, ξ.nearLitters_coinjective⟩

def litters (ξ : BaseAction) : SetRel Litter Litter :=
  {(L₁, L₂) | ∃ N₁ N₂, N₁ᴸ = L₁ ∧ N₂ᴸ = L₂ ∧ N₁ ~[ξᴺ] N₂}

instance : SuperL BaseAction (SetRel Litter Litter) where
  superL := litters

theorem litters_iff {ξ : BaseAction} (L₁ L₂ : Litter) :
    L₁ ~[ξᴸ] L₂ ↔ ∃ N₁ N₂, N₁ᴸ = L₁ ∧ N₂ᴸ = L₂ ∧ N₁ ~[ξᴺ] N₂ := .rfl

theorem litters_coinjective (ξ : BaseAction) : ξᴸ.Coinjective := by
  constructor
  intro L₁ L₂ L h₁ h₂
  rw [litters_iff] at h₁ h₂
  obtain ⟨N₃, N₁, h₃, rfl, h₁⟩ := h₁
  obtain ⟨N₄, N₂, h₄, rfl, h₂⟩ := h₂
  exact (litter_eq_litter_iff h₁ h₂).mp (h₃.trans h₄.symm)

theorem litters_dom_small (ξ : BaseAction) : Small ξᴸ.dom := by
  have := mk_le_of_surjective (f := λ (N : ξᴺ.dom) ↦
      (⟨N.valᴸ, N.prop.chooseᴸ, _, _, rfl, rfl, N.prop.choose_spec⟩ : ξᴸ.dom)) ?_
  · exact this.trans_lt ξ.nearLitters_dom_small
  · rintro ⟨L₁, L₂, hL⟩
    rw [litters_iff] at hL
    obtain ⟨N₁, N₂, rfl, rfl, h⟩ := hL
    exact ⟨⟨N₁, N₂, h⟩, rfl⟩

theorem litters_cod_small (ξ : BaseAction) : Small ξᴸ.cod :=
  small_cod_of_small_dom ξ.litters_coinjective ξ.litters_dom_small

@[simp]
theorem inv_litters (ξ : BaseAction) : ξ⁻¹ᴸ = ξᴸ.inv := by
  ext ⟨L₁, L₂⟩
  simp only [litters_iff, inv_nearLitters, exists_and_left, SetRel.mem_inv]
  tauto

theorem litters_injective (ξ : BaseAction) : ξᴸ.Injective := by
  have := ξ⁻¹.litters_coinjective
  rwa [inv_litters, SetRel.inv_coinjective_iff] at this

theorem litters_oneOne (ξ : BaseAction) : ξᴸ.OneOne :=
  ⟨ξ.litters_injective, ξ.litters_coinjective⟩

instance : LE BaseAction where
  le ξ ζ := ξᴬ ≤ ζᴬ ∧ ξᴺ = ζᴺ

instance : PartialOrder BaseAction where
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (le_antisymm h₁.1 h₂.1) h₁.2

theorem litters_eq_of_le {ξ ζ : BaseAction} (h : ξ ≤ ζ) : ξᴸ = ζᴸ := by
  ext ⟨L₁, L₂⟩
  simp only [litters_iff, h.2]

theorem inv_le_inv {ξ ζ : BaseAction} (h : ξ⁻¹ ≤ ζ⁻¹) :
    ξ ≤ ζ := by
  constructor
  · have := h.1
    rwa [inv_atoms, inv_atoms, SetRel.inv_le_inv_iff] at this
  · have := h.2
    rwa [inv_nearLitters, inv_nearLitters, SetRel.inv_inj] at this

theorem inv_le {ξ ζ : BaseAction} (h : ξ⁻¹ ≤ ζ) :
    ξ ≤ ζ⁻¹ :=
  inv_le_inv h

theorem inv_le_inv_iff {ξ ζ : BaseAction} :
    ξ⁻¹ ≤ ζ⁻¹ ↔ ξ ≤ ζ :=
  ⟨inv_le_inv, inv_le_inv (ξ := ξ⁻¹) (ζ := ζ⁻¹)⟩

/-- A definition that can be used to reduce the proof obligations of extending a base action. -/
def extend (ξ : BaseAction) (r : SetRel Atom Atom) (r_dom_small : Small r.dom) (r_oneOne : r.OneOne)
    (r_dom_disjoint : Disjoint ξᴬ.dom r.dom) (r_cod_disjoint : Disjoint ξᴬ.cod r.cod)
    (r_mem_iff_mem : ∀ {a₁ a₂ N₁ N₂}, a₁ ~[r] a₂ → N₁ ~[ξᴺ] N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ)) :
    BaseAction where
  atoms := ξᴬ ⊔ r
  nearLitters := ξᴺ
  atoms_dom_small' := by
    rw [SetRel.sup_dom]
    exact small_union ξ.atoms_dom_small r_dom_small
  nearLitters_dom_small' := ξ.nearLitters_dom_small
  atoms_oneOne' := ξ.atoms_oneOne.sup r_oneOne r_dom_disjoint r_cod_disjoint
  mem_iff_mem' ha hN := by
    obtain (ha | ha) := ha
    · exact ξ.mem_iff_mem ha hN
    · exact r_mem_iff_mem ha hN
  litter_eq_litter_iff' := ξ.litter_eq_litter_iff
  interference_subset_dom' h₁ h₂ a ha := by
    rw [SetRel.sup_dom]
    exact Or.inl (ξ.interference_subset_dom h₁ h₂ ha)
  interference_subset_cod' h₁ h₂ a ha := by
    rw [SetRel.sup_cod]
    exact Or.inl (ξ.interference_subset_cod h₁ h₂ ha)

theorem le_extend {ξ : BaseAction} {r : SetRel Atom Atom} {r_dom_small : Small r.dom}
    {r_oneOne : r.OneOne} {r_dom_disjoint : Disjoint ξᴬ.dom r.dom}
    {r_cod_disjoint : Disjoint ξᴬ.cod r.cod}
    {r_mem_iff_mem : ∀ {a₁ a₂ N₁ N₂}, a₁ ~[r] a₂ → N₁ ~[ξᴺ] N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ)} :
    ξ ≤ ξ.extend r r_dom_small r_oneOne r_dom_disjoint r_cod_disjoint r_mem_iff_mem :=
  ⟨le_sup_left, rfl⟩

@[mk_iff]
structure Nice (ξ : BaseAction) : Prop where
  symmDiff_subset_dom : ∀ N ∈ ξᴺ.dom, Nᴬ ∆ Nᴸᴬ ⊆ ξᴬ.dom
  symmDiff_subset_cod : ∀ N ∈ ξᴺ.cod, Nᴬ ∆ Nᴸᴬ ⊆ ξᴬ.cod

theorem Nice.mem_litter_dom_iff {ξ : BaseAction} (h : ξ.Nice)
    {N : NearLitter} (hN : N ∈ ξᴺ.dom) {a : Atom} (ha : a ∉ ξᴬ.dom) :
    a ∈ Nᴬ ↔ aᴸ = Nᴸ := by
  contrapose! ha
  apply h.symmDiff_subset_dom N hN
  rw [Set.mem_symmDiff]
  tauto

theorem Nice.mem_litter_cod_iff {ξ : BaseAction} (h : ξ.Nice)
    {N : NearLitter} (hN : N ∈ ξᴺ.cod) {a : Atom} (ha : a ∉ ξᴬ.cod) :
    a ∈ Nᴬ ↔ aᴸ = Nᴸ := by
  contrapose! ha
  apply h.symmDiff_subset_cod N hN
  rw [Set.mem_symmDiff]
  tauto

/-!
## Extending orbits inside near-litters
-/

/-- The set of atoms contained in near-litters but not the corresponding litters. -/
def inside (ξ : BaseAction) : Set Atom :=
  {a | ∃ N ∈ ξᴺ.dom, a ∈ Nᴬ ∧ aᴸ ≠ Nᴸ}

theorem inside_small (ξ : BaseAction) :
    Small ξ.inside := by
  have : Small (⋃ N ∈ ξᴺ.dom, Nᴬ \ Nᴸᴬ) := by
    apply small_biUnion ξ.nearLitters_dom_small
    intro N _
    exact N.diff_small
  apply this.mono
  rintro a ⟨N, h₁, h₂, h₃⟩
  simp only [Set.mem_iUnion]
  exact ⟨N, h₁, h₂, h₃⟩

@[mk_iff]
structure InsideCandidate (ξ : BaseAction) (L : Litter) (a : Atom) : Prop where
  litter_eq : aᴸ = L
  not_mem_cod : a ∉ ξᴬ.cod
  mem_nearLitter {N : NearLitter} : N ∈ ξᴺ.cod → Nᴸ = L → a ∈ Nᴬ

theorem insideCandidates_not_small (ξ : BaseAction) (L : Litter) :
    ¬Small {a | ξ.InsideCandidate L a} := by
  have h : Small (⋃ N ∈ ξᴺ.cod, ⋃ (_ : Nᴸ = L), Lᴬ \ Nᴬ) := by
    apply small_biUnion ξ.nearLitters_cod_small
    intro N _
    apply small_iUnion_Prop
    rintro rfl
    exact N.diff_small'
  have h' := L.atoms_not_small
  contrapose! h'
  apply (small_union (small_union ξ.atoms_cod_small h) h').mono
  rintro a rfl
  rw [Set.mem_union, or_iff_not_imp_left]
  intro ha
  rw [Set.mem_union, not_or] at ha
  constructor
  · rfl
  · exact ha.1
  · intro N hN₁ hN₂
    by_contra ha'
    apply ha.2
    simp only [Set.mem_iUnion]
    exact ⟨N, hN₁, hN₂, rfl, ha'⟩

theorem card_inside_lt_card_insideCandidates (ξ : BaseAction) (L : Litter) :
    #ξ.inside < #{a | ξ.InsideCandidate L a} :=
  ξ.inside_small.trans_le <| κ_le_of_not_small <| ξ.insideCandidates_not_small L

def insideMap (ξ : BaseAction) (L : Litter) :
    ξ.inside ↪ {a | ξ.InsideCandidate L a} :=
  Nonempty.some (ξ.card_inside_lt_card_insideCandidates L).le

theorem insideMap_litter_eq {ξ : BaseAction} (L : Litter) (x : ξ.inside) :
    (ξ.insideMap L x : Atom)ᴸ = L :=
  (ξ.insideMap L x).prop.litter_eq

theorem insideMap_not_mem_cod {ξ : BaseAction} (L : Litter) (x : ξ.inside) :
    (ξ.insideMap L x : Atom) ∉ ξᴬ.cod :=
  (ξ.insideMap L x).prop.not_mem_cod

theorem insideMap_mem_nearLitter  {ξ : BaseAction} (L : Litter) (x : ξ.inside) {N : NearLitter} :
    N ∈ ξᴺ.cod → Nᴸ = L → (ξ.insideMap L x : Atom) ∈ Nᴬ :=
  (ξ.insideMap L x).prop.mem_nearLitter

def insideRel (ξ : BaseAction) : SetRel Atom Atom :=
    {(a₁, a₂) | ∃ N₁ N₂ h, N₁ ~[ξᴺ] N₂ ∧ a₁ ∉ ξᴬ.dom ∧ a₂ = ξ.insideMap N₂ᴸ ⟨a₁, N₁, h⟩}

theorem insideRel_dom_small (ξ : BaseAction) : Small ξ.insideRel.dom := by
  apply ξ.inside_small.mono
  rintro a ⟨_, N₁, N₂, h, _, _, rfl⟩
  exact ⟨N₁, h⟩

theorem insideRel_injective (ξ : BaseAction) : ξ.insideRel.Injective := by
  constructor
  rintro a b c ⟨Na₁, Na₂, ha₁, ha₂⟩ ⟨Nb₁, Nb₂, hb₁, hb₂⟩
  have := ha₂.2.2.symm.trans hb₂.2.2
  have ha := insideMap_litter_eq Na₂ᴸ ⟨a, Na₁, ha₁⟩
  have hb := insideMap_litter_eq Nb₂ᴸ ⟨b, Nb₁, hb₁⟩
  have hab := ha.symm.trans ((congr_arg (·ᴸ) this).trans hb)
  rwa [hab, Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq, Subtype.mk_eq_mk] at this

theorem insideRel_coinjective (ξ : BaseAction) : ξ.insideRel.Coinjective := by
  constructor
  rintro a b c ⟨Na₁, Na₂, ha₁, ha₂⟩ ⟨Nb₁, Nb₂, hb₁, hb₂⟩
  have : Na₁ᴸ = Nb₁ᴸ := by
    have : c ∉ interference Na₁ Nb₁ := λ h ↦ ha₂.2.1 (ξ.interference_subset_dom ha₁.1 hb₁.1 h)
    by_contra hN
    rw [interference_eq_of_litter_ne hN] at this
    exact this ⟨ha₁.2.1, hb₁.2.1⟩
  rw [ξ.litter_eq_litter_iff ha₂.1 hb₂.1] at this
  rw [ha₂.2.2, hb₂.2.2, this]

theorem insideRel_oneOne (ξ : BaseAction) : ξ.insideRel.OneOne :=
  ⟨ξ.insideRel_injective, ξ.insideRel_coinjective⟩

theorem insideRel_dom (ξ : BaseAction) : Disjoint ξᴬ.dom ξ.insideRel.dom := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro a ⟨ha, _, _, _, _, _, ha', _⟩
  contradiction

theorem insideRel_cod (ξ : BaseAction) : Disjoint ξᴬ.cod ξ.insideRel.cod := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨⟨a, ha⟩, b, N₁, N₂, h, _, _, rfl⟩
  exact insideMap_not_mem_cod N₂ᴸ ⟨b, N₁, h⟩ ⟨a, ha⟩

theorem insideRel_mem_iff_mem {ξ : BaseAction} {a₁ a₂ : Atom} {N₁ N₂ : NearLitter}
    (ha : a₁ ~[ξ.insideRel] a₂) (hN : N₁ ~[ξᴺ] N₂) :
    a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ := by
  obtain ⟨N₁', N₂', h, hN', ha₁, rfl⟩ := ha
  constructor
  · intro h'
    apply insideMap_mem_nearLitter N₂'ᴸ ⟨a₁, N₁', h⟩ ⟨N₁, hN⟩
    rw [← litter_eq_litter_iff hN hN']
    by_contra hL
    refine ha₁ (ξ.interference_subset_dom ⟨N₂, hN⟩ ⟨N₂', hN'⟩ ?_)
    rw [interference_eq_of_litter_ne hL]
    exact ⟨h', h.2.1⟩
  · intro h'
    contrapose! ha₁
    apply ξ.interference_subset_dom ⟨N₂, hN⟩ ⟨N₂', hN'⟩
    rw [interference_eq_of_litter_eq]
    · exact Or.inr ⟨h.2.1, ha₁⟩
    rw [litter_eq_litter_iff hN hN']
    by_contra this
    apply ξ.insideMap_not_mem_cod N₂'ᴸ ⟨a₁, N₁', h⟩
    apply ξ.interference_subset_cod ⟨N₁, hN⟩ ⟨N₁', hN'⟩
    rw [interference_eq_of_litter_ne this]
    exact ⟨h', insideMap_mem_nearLitter N₂'ᴸ ⟨a₁, N₁', h⟩ ⟨N₁', hN'⟩ rfl⟩

def insideExtension (ξ : BaseAction) : BaseAction :=
  ξ.extend ξ.insideRel ξ.insideRel_dom_small ξ.insideRel_oneOne
    ξ.insideRel_dom ξ.insideRel_cod insideRel_mem_iff_mem

theorem insideExtension_atoms (ξ : BaseAction) :
    ξ.insideExtensionᴬ = ξᴬ ⊔ ξ.insideRel :=
  rfl

theorem le_insideExtension (ξ : BaseAction) : ξ ≤ ξ.insideExtension :=
  le_extend

theorem insideExtension_spec {ξ : BaseAction} (N : NearLitter) (hN : N ∈ ξᴺ.dom) :
    Nᴬ \ Nᴸᴬ ⊆ ξ.insideExtensionᴬ.dom := by
  intro a ha
  by_contra ha'
  rw [insideExtension_atoms, SetRel.sup_dom, Set.mem_union, not_or] at ha'
  apply ha'.2
  obtain ⟨N', hN⟩ := hN
  exact ⟨_, N, N', ⟨⟨N', hN⟩, ha.1, ha.2⟩, hN, ha'.1, rfl⟩

/-!
## Extending orbits outside near-litters
-/

@[mk_iff]
structure Sandbox (ξ : BaseAction) (L : Litter) : Prop where
  atom_not_mem (a : Atom) : a ∈ ξᴬ.cod → aᴸ ≠ L
  nearLitter_not_mem (N : NearLitter) (a : Atom) : aᴸ = L → N ∈ ξᴺ.cod → a ∉ Nᴬ

def not_sandbox_eq (ξ : BaseAction) :
    {L | ¬ξ.Sandbox L} = (⋃ a ∈ ξᴬ.cod, {aᴸ}) ∪ (⋃ N ∈ ξᴺ.cod, ⋃ a ∈ Nᴬ, {aᴸ}) := by
  ext L
  simp only [sandbox_iff, Set.mem_union, Set.mem_iUnion, exists_prop,
    not_and_or, not_forall, not_not]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨N, a, rfl, hN, ha⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨N, hN, a, ha, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨N, hN, a, ha, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨N, a, rfl, hN, ha⟩

theorem card_not_sandbox (ξ : BaseAction) :
    #{L | ¬ξ.Sandbox L} ≤ #κ := by
  rw [not_sandbox_eq]
  apply (mk_union_le _ _).trans
  apply add_le_of_le κ_isRegular.aleph0_le
  · refine (mk_biUnion_le_of_le 1 ?_).trans ?_
    · simp only [mk_singleton, le_refl, implies_true]
    rw [mul_one]
    exact ξ.atoms_cod_small.le
  · refine (mk_biUnion_le_of_le #κ ?_).trans ?_
    · intro N _
      refine (mk_biUnion_le_of_le 1 ?_).trans ?_
      · simp only [mk_singleton, le_refl, implies_true]
      · rw [mul_one, N.card_atoms]
    · exact mul_le_of_le κ_isRegular.aleph0_le ξ.nearLitters_cod_small.le le_rfl

theorem exists_sandbox (ξ : BaseAction) : {L | ξ.Sandbox L}.Nonempty := by
  by_contra h
  suffices #{L | ξ.Sandbox L} + #{L | ¬ξ.Sandbox L} ≤ #κ by
    have h := mk_sum_compl {L | ξ.Sandbox L}
    have := h.symm.trans_le this
    rw [card_litter, ← not_lt] at this
    exact this κ_lt_μ
  rw [Set.not_nonempty_iff_eq_empty] at h
  rw [h, mk_eq_zero, zero_add]
  exact ξ.card_not_sandbox

def sandbox (ξ : BaseAction) : Litter :=
  ξ.exists_sandbox.some

theorem sandbox_spec (ξ : BaseAction) : ξ.Sandbox ξ.sandbox :=
  ξ.exists_sandbox.some_mem

def outside (ξ : BaseAction) : Set Atom :=
  {a | ∃ N ∈ ξᴺ.dom, a ∉ Nᴬ ∧ aᴸ = Nᴸ}

theorem outside_small (ξ : BaseAction) :
    Small ξ.outside := by
  have : Small (⋃ N ∈ ξᴺ.dom, Nᴸᴬ \ Nᴬ) := by
    apply small_biUnion ξ.nearLitters_dom_small
    intro N _
    exact N.diff_small'
  apply this.mono
  rintro a ⟨N, h₁, h₂, h₃⟩
  simp only [Set.mem_iUnion]
  exact ⟨N, h₁, h₃, h₂⟩

theorem card_outside_lt_card_sandbox (ξ : BaseAction) :
    #ξ.outside < #ξ.sandboxᴬ :=
  ξ.outside_small.trans_le <| κ_le_of_not_small <| ξ.sandbox.atoms_not_small

def outsideMap (ξ : BaseAction) : ξ.outside ↪ ξ.sandboxᴬ :=
  Nonempty.some ξ.card_outside_lt_card_sandbox.le

theorem outsideMap_litter {ξ : BaseAction} (x : ξ.outside) :
    ξ.Sandbox (ξ.outsideMap x : Atom)ᴸ := by
  rw [(ξ.outsideMap x).prop]
  exact ξ.sandbox_spec

def outsideRel (ξ : BaseAction) : SetRel Atom Atom :=
  {(a₁, a₂) | (a₁ ∉ ξᴬ.dom) ∧ ∃ h, a₂ = ξ.outsideMap ⟨a₁, h⟩}

theorem outsideRel_dom_small (ξ : BaseAction) : Small ξ.outsideRel.dom := by
  apply ξ.outside_small.mono
  rintro a ⟨_, _, ha, rfl⟩
  exact ha

theorem outsideRel_injective (ξ : BaseAction) : ξ.outsideRel.Injective := by
  constructor
  rintro a b c ⟨_, _, hac⟩ ⟨_, _, hbc⟩
  have := hac.symm.trans hbc
  rwa [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq, Subtype.mk_eq_mk] at this

theorem outsideRel_coinjective (ξ : BaseAction) : ξ.outsideRel.Coinjective := by
  constructor
  rintro a b c ⟨_, _, rfl⟩ ⟨_, _, rfl⟩
  rfl

theorem outsideRel_oneOne (ξ : BaseAction) : ξ.outsideRel.OneOne :=
  ⟨ξ.outsideRel_injective, ξ.outsideRel_coinjective⟩

theorem outsideRel_dom (ξ : BaseAction) : Disjoint ξᴬ.dom ξ.outsideRel.dom := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro a ⟨ha, _, _, _, _, _, ha', _⟩
  contradiction

theorem outsideRel_cod (ξ : BaseAction) : Disjoint ξᴬ.cod ξ.outsideRel.cod := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨⟨a, hab⟩, b, _, hb', rfl⟩
  exact (outsideMap_litter ⟨b, hb'⟩).atom_not_mem _ ⟨a, hab⟩ rfl

theorem outsideRel_mem_iff_mem {ξ : BaseAction} (hξ : ∀ N ∈ ξᴺ.dom, Nᴬ \ Nᴸᴬ ⊆ ξᴬ.dom)
    {a₁ a₂ : Atom} {N₁ N₂ : NearLitter}
    (ha : a₁ ~[ξ.outsideRel] a₂) (hN : N₁ ~[ξᴺ] N₂) :
    a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ := by
  obtain ⟨h₁, ⟨N₁', ⟨N₂', hN'⟩, h₂, h₃⟩, rfl⟩ := ha
  have := (outsideMap_litter ⟨a₁, N₁', ⟨N₂', hN'⟩, h₂, h₃⟩).nearLitter_not_mem N₂ _ rfl ⟨N₁, hN⟩
  apply (iff_false_right this).mpr
  intro h₄
  suffices N₁'ᴸ ≠ N₁ᴸ from h₁ (hξ N₁ ⟨N₂, hN⟩ ⟨h₄, h₃.trans_ne this⟩)
  contrapose! h₁
  apply ξ.interference_subset_dom ⟨N₂', hN'⟩ ⟨N₂, hN⟩
  rw [interference_eq_of_litter_eq h₁]
  exact Or.inr ⟨h₄, h₂⟩

def outsideExtension (ξ : BaseAction) (hξ : ∀ N ∈ ξᴺ.dom, Nᴬ \ Nᴸᴬ ⊆ ξᴬ.dom) : BaseAction :=
  ξ.extend ξ.outsideRel ξ.outsideRel_dom_small ξ.outsideRel_oneOne
    ξ.outsideRel_dom ξ.outsideRel_cod (ξ.outsideRel_mem_iff_mem hξ)

theorem outsideExtension_atoms (ξ : BaseAction) (hξ : ∀ N ∈ ξᴺ.dom, Nᴬ \ Nᴸᴬ ⊆ ξᴬ.dom) :
    (ξ.outsideExtension hξ)ᴬ = ξᴬ ⊔ ξ.outsideRel :=
  rfl

theorem le_outsideExtension (ξ : BaseAction) (hξ : ∀ N ∈ ξᴺ.dom, Nᴬ \ Nᴸᴬ ⊆ ξᴬ.dom) :
    ξ ≤ ξ.outsideExtension hξ :=
  le_extend

theorem outsideExtension_spec {ξ : BaseAction} {hξ : ∀ N ∈ ξᴺ.dom, Nᴬ \ Nᴸᴬ ⊆ ξᴬ.dom}
    (N : NearLitter) (hN : N ∈ ξᴺ.dom) :
    Nᴸᴬ \ Nᴬ ⊆ (ξ.outsideExtension hξ)ᴬ.dom := by
  intro a ha
  by_contra ha'
  rw [outsideExtension_atoms, SetRel.sup_dom, Set.mem_union, not_or] at ha'
  apply ha'.2
  obtain ⟨N', hN⟩ := hN
  exact ⟨_, ha'.1, ⟨N, ⟨N', hN⟩, ha.2, ha.1⟩, rfl⟩

/-!
## Nice extensions
-/

def doubleInsideExtension (ξ : BaseAction) : BaseAction :=
  ξ.insideExtension⁻¹.insideExtension⁻¹

theorem le_doubleInsideExtension (ξ : BaseAction) :
    ξ ≤ ξ.doubleInsideExtension :=
  ξ.le_insideExtension.trans <| inv_le <| ξ.insideExtension⁻¹.le_insideExtension

theorem doubleInsideExtension_dom {ξ : BaseAction} (N : NearLitter) (hN : N ∈ ξᴺ.dom) :
    Nᴬ \ Nᴸᴬ ⊆ ξ.doubleInsideExtensionᴬ.dom := by
  intro a ha
  have := ξ.insideExtension_spec N hN ha
  rw [doubleInsideExtension, inv_atoms, insideExtension_atoms, SetRel.dom_inv, SetRel.sup_cod]
  left
  exact this

theorem doubleInsideExtension_cod {ξ : BaseAction} (N : NearLitter) (hN : N ∈ ξᴺ.cod) :
    Nᴬ \ Nᴸᴬ ⊆ ξ.doubleInsideExtensionᴬ.cod :=
  ξ.insideExtension⁻¹.insideExtension_spec N hN

theorem niceExtension_aux {ξ : BaseAction} (N : NearLitter) (hN : N ∈ ξᴺ.cod) :
    Nᴬ \ Nᴸᴬ ⊆ (ξ.doubleInsideExtension.outsideExtension ξ.doubleInsideExtension_dom)⁻¹ᴬ.dom := by
  intro a ha
  rw [inv_atoms, outsideExtension_atoms, SetRel.dom_inv, SetRel.sup_cod]
  left
  exact doubleInsideExtension_cod N hN ha

def niceExtension (ξ : BaseAction) : BaseAction :=
  ((ξ.doubleInsideExtension.outsideExtension ξ.doubleInsideExtension_dom)⁻¹.outsideExtension
    ξ.niceExtension_aux)⁻¹

theorem le_niceExtension (ξ : BaseAction) :
    ξ ≤ ξ.niceExtension :=
  ξ.le_doubleInsideExtension.trans <|
    (ξ.doubleInsideExtension.le_outsideExtension _).trans <| inv_le <|
    (ξ.doubleInsideExtension.outsideExtension _)⁻¹.le_outsideExtension _

theorem niceExtension_nice (ξ : BaseAction) : ξ.niceExtension.Nice := by
  constructor
  · rintro N hN a (ha | ha)
    · rw [niceExtension, inv_atoms, SetRel.dom_inv, outsideExtension_atoms, SetRel.sup_cod]
      left
      rw [inv_atoms, SetRel.cod_inv, outsideExtension_atoms, SetRel.sup_dom]
      left
      exact ξ.doubleInsideExtension_dom N hN ha
    · rw [niceExtension, inv_atoms, SetRel.dom_inv, outsideExtension_atoms, SetRel.sup_cod]
      left
      rw [inv_atoms, SetRel.cod_inv]
      exact outsideExtension_spec (ξ := ξ.doubleInsideExtension) N hN ha
  · rintro N hN a (ha | ha)
    · rw [niceExtension, inv_atoms, SetRel.cod_inv, outsideExtension_atoms, SetRel.sup_dom]
      left
      rw [inv_atoms, SetRel.dom_inv, outsideExtension_atoms, SetRel.sup_cod]
      left
      exact ξ.doubleInsideExtension_cod N hN ha
    · rw [niceExtension, inv_atoms, SetRel.cod_inv]
      exact outsideExtension_spec
        (ξ := (ξ.doubleInsideExtension.outsideExtension ξ.doubleInsideExtension_dom)⁻¹) N hN ha

@[simp]
theorem niceExtension_nearLitters (ξ : BaseAction) :
    ξ.niceExtensionᴺ = ξᴺ :=
  rfl

@[simp]
theorem niceExtension_litters (ξ : BaseAction) :
    ξ.niceExtensionᴸ = ξᴸ := by
  ext ⟨L₁, L₂⟩
  simp only [litters_iff, niceExtension_nearLitters]

end BaseAction

end ConNF
