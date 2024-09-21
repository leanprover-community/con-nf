import ConNF.Setup.NearLitter

/-!
# Base actions

In this file, we define base actions.

## Main declarations

* `ConNF.BaseAction`: The type of base actions.
-/

noncomputable section
universe u

open Cardinal Ordinal
open scoped symmDiff

namespace ConNF

variable [Params.{u}]

structure BaseAction where
  atoms : Rel Atom Atom
  nearLitters : Rel NearLitter NearLitter
  atoms_dom_small' : Small atoms.dom
  nearLitters_dom_small' : Small nearLitters.dom
  atoms_oneOne' : atoms.OneOne
  mem_iff_mem' {a₁ a₂ : Atom} {N₁ N₂ : NearLitter} :
    atoms a₁ a₂ → nearLitters N₁ N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ)
  litter_eq_litter_iff' {N₁ N₂ N₃ N₄ : NearLitter} :
    nearLitters N₁ N₃ → nearLitters N₂ N₄ → (N₁ᴸ = N₂ᴸ ↔ N₃ᴸ = N₄ᴸ)
  interference_subset_dom' {N₁ N₂ : NearLitter} :
    N₁ ∈ nearLitters.dom → N₂ ∈ nearLitters.dom → interference N₁ N₂ ⊆ atoms.dom
  interference_subset_codom' {N₁ N₂ : NearLitter} :
    N₁ ∈ nearLitters.codom → N₂ ∈ nearLitters.codom → interference N₁ N₂ ⊆ atoms.codom

namespace BaseAction

instance : SuperA BaseAction (Rel Atom Atom) where
  superA := atoms

instance : SuperN BaseAction (Rel NearLitter NearLitter) where
  superN := nearLitters

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
    ξᴬ a₁ a₂ → ξᴺ N₁ N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ) :=
  ξ.mem_iff_mem'

theorem litter_eq_litter_iff {ξ : BaseAction} {N₁ N₂ N₃ N₄ : NearLitter} :
    ξᴺ N₁ N₃ → ξᴺ N₂ N₄ → (N₁ᴸ = N₂ᴸ ↔ N₃ᴸ = N₄ᴸ) :=
  ξ.litter_eq_litter_iff'

theorem interference_subset_dom {ξ : BaseAction} {N₁ N₂ : NearLitter} :
    N₁ ∈ ξᴺ.dom → N₂ ∈ ξᴺ.dom → interference N₁ N₂ ⊆ ξᴬ.dom :=
  ξ.interference_subset_dom'

theorem interference_subset_codom {ξ : BaseAction} {N₁ N₂ : NearLitter} :
    N₁ ∈ ξᴺ.codom → N₂ ∈ ξᴺ.codom → interference N₁ N₂ ⊆ ξᴬ.codom :=
  ξ.interference_subset_codom'

theorem mem_symmDiff_iff_mem_symmDiff {ξ : BaseAction} {a₁ a₂ : Atom} {N₁ N₂ N₃ N₄ : NearLitter} :
    ξᴬ a₁ a₂ → ξᴺ N₁ N₂ → ξᴺ N₃ N₄ → (a₁ ∈ N₁ᴬ ∆ N₃ᴬ ↔ a₂ ∈ N₂ᴬ ∆ N₄ᴬ) := by
  intro ha hN₁₂ hN₃₄
  simp only [Set.mem_symmDiff, mem_iff_mem ha hN₁₂, mem_iff_mem ha hN₃₄]

theorem nearLitters_coinjective (ξ : BaseAction) : ξᴺ.Coinjective := by
  constructor
  intro N₁ N₂ N h₁ h₂
  apply NearLitter.ext
  rw [← Set.symmDiff_eq_empty, Set.eq_empty_iff_forall_not_mem]
  intro a ha
  have := interference_subset_codom ⟨_, h₁⟩ ⟨_, h₂⟩
  rw [interference_eq_of_litter_eq ((litter_eq_litter_iff h₁ h₂).mp rfl)] at this
  obtain ⟨b, hba⟩ := this ha
  rw [← mem_symmDiff_iff_mem_symmDiff hba h₁ h₂] at ha
  simp only [symmDiff_self, Set.bot_eq_empty, Set.mem_empty_iff_false] at ha

theorem atoms_codom_small (ξ : BaseAction) : Small ξᴬ.codom :=
  small_codom_of_small_dom ξ.atoms_oneOne.toCoinjective ξ.atoms_dom_small

theorem nearLitters_codom_small (ξ : BaseAction) : Small ξᴺ.codom :=
  small_codom_of_small_dom ξ.nearLitters_coinjective ξ.nearLitters_dom_small

def inv (ξ : BaseAction) : BaseAction where
  atoms := ξᴬ.inv
  nearLitters := ξᴺ.inv
  atoms_dom_small' := ξ.atoms_codom_small
  nearLitters_dom_small' := ξ.nearLitters_codom_small
  atoms_oneOne' := ξ.atoms_oneOne.inv
  mem_iff_mem' h₁ h₂ := (ξ.mem_iff_mem h₁ h₂).symm
  litter_eq_litter_iff' h₁ h₂ := (ξ.litter_eq_litter_iff h₁ h₂).symm
  interference_subset_dom' := ξ.interference_subset_codom
  interference_subset_codom' := ξ.interference_subset_dom

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

theorem nearLitters_injective (ξ : BaseAction) : ξᴺ.Injective := by
  have := ξ⁻¹.nearLitters_coinjective
  rwa [inv_nearLitters, Rel.inv_coinjective_iff] at this

theorem nearLitters_oneOne (ξ : BaseAction) : ξᴺ.OneOne :=
  ⟨ξ.nearLitters_injective, ξ.nearLitters_coinjective⟩

inductive litters (ξ : BaseAction) : Rel Litter Litter
  | mk {N₁ N₂ : NearLitter} : ξᴺ N₁ N₂ → ξ.litters N₁ᴸ N₂ᴸ

instance : SuperL BaseAction (Rel Litter Litter) where
  superL := litters

theorem litters_iff {ξ : BaseAction} (L₁ L₂ : Litter) :
    ξᴸ L₁ L₂ ↔ ∃ N₁ N₂, N₁ᴸ = L₁ ∧ N₂ᴸ = L₂ ∧ ξᴺ N₁ N₂ := by
  constructor
  · rintro ⟨⟩
    refine ⟨_, _, rfl, rfl, ?_⟩
    assumption
  · rintro ⟨N₁, N₂, rfl, rfl, h⟩
    exact ⟨h⟩

theorem litters_coinjective (ξ : BaseAction) : ξᴸ.Coinjective := by
  constructor
  intro L₁ L₂ L h₁ h₂
  rw [litters_iff] at h₁ h₂
  obtain ⟨N₃, N₁, h₃, rfl, h₁⟩ := h₁
  obtain ⟨N₄, N₂, h₄, rfl, h₂⟩ := h₂
  exact (litter_eq_litter_iff h₁ h₂).mp (h₃.trans h₄.symm)

@[simp]
theorem inv_litters (ξ : BaseAction) : ξ⁻¹ᴸ = ξᴸ.inv := by
  ext L₁ L₂
  simp only [litters_iff, inv_nearLitters, exists_and_left, Rel.inv_def]
  tauto

theorem litters_injective (ξ : BaseAction) : ξᴸ.Injective := by
  have := ξ⁻¹.litters_coinjective
  rwa [inv_litters, Rel.inv_coinjective_iff] at this

theorem litters_oneOne (ξ : BaseAction) : ξᴸ.OneOne :=
  ⟨ξ.litters_injective, ξ.litters_coinjective⟩

instance : LE BaseAction where
  le ξ ζ := ξᴬ ≤ ζᴬ ∧ ξᴺ = ζᴺ

instance : PartialOrder BaseAction where
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (le_antisymm h₁.1 h₂.1) h₁.2

theorem inv_le_inv {ξ ζ : BaseAction} (h : ξ⁻¹ ≤ ζ⁻¹) :
    ξ ≤ ζ := by
  constructor
  · have := h.1
    rwa [inv_atoms, inv_atoms, Rel.inv_le_inv_iff] at this
  · have := h.2
    rwa [inv_nearLitters, inv_nearLitters, Rel.inv_inj] at this

theorem inv_le {ξ ζ : BaseAction} (h : ξ⁻¹ ≤ ζ) :
    ξ ≤ ζ⁻¹ :=
  inv_le_inv h

theorem inv_le_inv_iff {ξ ζ : BaseAction} :
    ξ⁻¹ ≤ ζ⁻¹ ↔ ξ ≤ ζ :=
  ⟨inv_le_inv, inv_le_inv (ξ := ξ⁻¹) (ζ := ζ⁻¹)⟩

/-- A definition that can be used to reduce the proof obligations of extending a base action. -/
def extend (ξ : BaseAction) (r : Rel Atom Atom) (r_dom_small : Small r.dom) (r_oneOne : r.OneOne)
    (r_dom_disjoint : Disjoint ξᴬ.dom r.dom) (r_codom_disjoint : Disjoint ξᴬ.codom r.codom)
    (r_mem_iff_mem : ∀ {a₁ a₂ N₁ N₂}, r a₁ a₂ → ξᴺ N₁ N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ)) :
    BaseAction where
  atoms := ξᴬ ⊔ r
  nearLitters := ξᴺ
  atoms_dom_small' := by
    rw [Rel.sup_dom]
    exact small_union ξ.atoms_dom_small r_dom_small
  nearLitters_dom_small' := ξ.nearLitters_dom_small
  atoms_oneOne' := Rel.sup_oneOne ξ.atoms_oneOne r_oneOne r_dom_disjoint r_codom_disjoint
  mem_iff_mem' ha hN := by
    obtain (ha | ha) := ha
    · exact ξ.mem_iff_mem ha hN
    · exact r_mem_iff_mem ha hN
  litter_eq_litter_iff' := ξ.litter_eq_litter_iff
  interference_subset_dom' h₁ h₂ a ha := by
    rw [Rel.sup_dom]
    exact Or.inl (ξ.interference_subset_dom h₁ h₂ ha)
  interference_subset_codom' h₁ h₂ a ha := by
    rw [Rel.sup_codom]
    exact Or.inl (ξ.interference_subset_codom h₁ h₂ ha)

theorem le_extend {ξ : BaseAction} {r : Rel Atom Atom} {r_dom_small : Small r.dom}
    {r_oneOne : r.OneOne} {r_dom_disjoint : Disjoint ξᴬ.dom r.dom}
    {r_codom_disjoint : Disjoint ξᴬ.codom r.codom}
    {r_mem_iff_mem : ∀ {a₁ a₂ N₁ N₂}, r a₁ a₂ → ξᴺ N₁ N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ)} :
    ξ ≤ ξ.extend r r_dom_small r_oneOne r_dom_disjoint r_codom_disjoint r_mem_iff_mem :=
  ⟨le_sup_left, rfl⟩

@[mk_iff]
structure Nice (ξ : BaseAction) : Prop where
  symmDiff_subset_dom : ∀ N ∈ ξᴺ.dom, Nᴬ ∆ Nᴸᴬ ⊆ ξᴬ.dom
  symmDiff_subset_codom : ∀ N ∈ ξᴺ.codom, Nᴬ ∆ Nᴸᴬ ⊆ ξᴬ.codom

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
  not_mem_codom : a ∉ ξᴬ.codom
  mem_nearLitter {N : NearLitter} : N ∈ ξᴺ.codom → Nᴸ = L → a ∈ Nᴬ

theorem insideCandidates_not_small (ξ : BaseAction) (L : Litter) :
    ¬Small {a | ξ.InsideCandidate L a} := by
  have h : Small (⋃ N ∈ ξᴺ.codom, ⋃ (_ : Nᴸ = L), Lᴬ \ Nᴬ) := by
    apply small_biUnion ξ.nearLitters_codom_small
    intro N _
    apply small_iUnion_Prop
    rintro rfl
    exact N.diff_small'
  have h' := L.atoms_not_small
  contrapose! h'
  apply (small_union (small_union ξ.atoms_codom_small h) h').mono
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

theorem insideMap_not_mem_codom {ξ : BaseAction} (L : Litter) (x : ξ.inside) :
    (ξ.insideMap L x : Atom) ∉ ξᴬ.codom :=
  (ξ.insideMap L x).prop.not_mem_codom

theorem insideMap_mem_nearLitter  {ξ : BaseAction} (L : Litter) (x : ξ.inside) {N : NearLitter} :
    N ∈ ξᴺ.codom → Nᴸ = L → (ξ.insideMap L x : Atom) ∈ Nᴬ :=
  (ξ.insideMap L x).prop.mem_nearLitter

def insideRel (ξ : BaseAction) : Rel Atom Atom :=
    λ a₁ a₂ ↦ ∃ N₁ N₂ h, ξᴺ N₁ N₂ ∧ a₁ ∉ ξᴬ.dom ∧ a₂ = ξ.insideMap N₂ᴸ ⟨a₁, N₁, h⟩

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
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
  rintro a ⟨ha, _, _, _, _, _, ha', _⟩
  contradiction

theorem insideRel_codom (ξ : BaseAction) : Disjoint ξᴬ.codom ξ.insideRel.codom := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
  rintro _ ⟨⟨a, ha⟩, b, N₁, N₂, h, _, _, rfl⟩
  exact insideMap_not_mem_codom N₂ᴸ ⟨b, N₁, h⟩ ⟨a, ha⟩

theorem insideRel_mem_iff_mem {ξ : BaseAction} {a₁ a₂ : Atom} {N₁ N₂ : NearLitter}
    (ha : ξ.insideRel a₁ a₂) (hN : ξᴺ N₁ N₂) :
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
    apply ξ.insideMap_not_mem_codom N₂'ᴸ ⟨a₁, N₁', h⟩
    apply ξ.interference_subset_codom ⟨N₁, hN⟩ ⟨N₁', hN'⟩
    rw [interference_eq_of_litter_ne this]
    exact ⟨h', insideMap_mem_nearLitter N₂'ᴸ ⟨a₁, N₁', h⟩ ⟨N₁', hN'⟩ rfl⟩

def insideExtension (ξ : BaseAction) : BaseAction :=
  ξ.extend ξ.insideRel ξ.insideRel_dom_small ξ.insideRel_oneOne
    ξ.insideRel_dom ξ.insideRel_codom insideRel_mem_iff_mem

theorem insideExtension_atoms (ξ : BaseAction) :
    ξ.insideExtensionᴬ = ξᴬ ⊔ ξ.insideRel :=
  rfl

theorem le_insideExtension (ξ : BaseAction) : ξ ≤ ξ.insideExtension :=
  le_extend

theorem insideExtension_spec {ξ : BaseAction} (N : NearLitter) (hN : N ∈ ξᴺ.dom) :
    Nᴬ \ Nᴸᴬ ⊆ ξ.insideExtensionᴬ.dom := by
  intro a ha
  by_contra ha'
  rw [insideExtension_atoms, Rel.sup_dom, Set.mem_union, not_or] at ha'
  apply ha'.2
  obtain ⟨N', hN⟩ := hN
  exact ⟨_, N, N', ⟨⟨N', hN⟩, ha.1, ha.2⟩, hN, ha'.1, rfl⟩

/-!
## Extending orbits outside near-litters
-/

@[mk_iff]
structure Sandbox (ξ : BaseAction) (L : Litter) : Prop where
  atom_not_mem (a : Atom) : a ∈ ξᴬ.codom → aᴸ ≠ L
  nearLitter_not_mem (N : NearLitter) (a : Atom) : aᴸ = L → N ∈ ξᴺ.codom → a ∉ Nᴬ

def not_sandbox_eq (ξ : BaseAction) :
    {L | ¬ξ.Sandbox L} = (⋃ a ∈ ξᴬ.codom, {aᴸ}) ∪ (⋃ N ∈ ξᴺ.codom, ⋃ a ∈ Nᴬ, {aᴸ}) := by
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
    · simp only [mk_fintype, Fintype.card_ofSubsingleton, Nat.cast_one, le_refl, implies_true]
    rw [mul_one]
    exact ξ.atoms_codom_small.le
  · refine (mk_biUnion_le_of_le #κ ?_).trans ?_
    · intro N _
      refine (mk_biUnion_le_of_le 1 ?_).trans ?_
      · simp only [mk_fintype, Fintype.card_ofSubsingleton, Nat.cast_one, le_refl, implies_true]
      · rw [mul_one, N.card_atoms]
    · exact mul_le_of_le κ_isRegular.aleph0_le ξ.nearLitters_codom_small.le le_rfl

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

def outsideRel (ξ : BaseAction) : Rel Atom Atom :=
  λ a₁ a₂ ↦ a₁ ∉ ξᴬ.dom ∧ ∃ h, a₂ = ξ.outsideMap ⟨a₁, h⟩

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
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
  rintro a ⟨ha, _, _, _, _, _, ha', _⟩
  contradiction

theorem outsideRel_codom (ξ : BaseAction) : Disjoint ξᴬ.codom ξ.outsideRel.codom := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
  rintro _ ⟨⟨a, hab⟩, b, _, hb', rfl⟩
  exact (outsideMap_litter ⟨b, hb'⟩).atom_not_mem _ ⟨a, hab⟩ rfl

theorem outsideRel_mem_iff_mem {ξ : BaseAction} (hξ : ∀ N ∈ ξᴺ.dom, Nᴬ \ Nᴸᴬ ⊆ ξᴬ.dom)
    {a₁ a₂ : Atom} {N₁ N₂ : NearLitter}
    (ha : ξ.outsideRel a₁ a₂) (hN : ξᴺ N₁ N₂) :
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
    ξ.outsideRel_dom ξ.outsideRel_codom (ξ.outsideRel_mem_iff_mem hξ)

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
  rw [outsideExtension_atoms, Rel.sup_dom, Set.mem_union, not_or] at ha'
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
  rw [doubleInsideExtension, inv_atoms, insideExtension_atoms, Rel.inv_dom, Rel.sup_codom]
  left
  exact this

theorem doubleInsideExtension_codom {ξ : BaseAction} (N : NearLitter) (hN : N ∈ ξᴺ.codom) :
    Nᴬ \ Nᴸᴬ ⊆ ξ.doubleInsideExtensionᴬ.codom :=
  ξ.insideExtension⁻¹.insideExtension_spec N hN

theorem niceExtension_aux {ξ : BaseAction} (N : NearLitter) (hN : N ∈ ξᴺ.codom) :
    Nᴬ \ Nᴸᴬ ⊆ (ξ.doubleInsideExtension.outsideExtension ξ.doubleInsideExtension_dom)⁻¹ᴬ.dom := by
  intro a ha
  rw [inv_atoms, outsideExtension_atoms, Rel.inv_dom, Rel.sup_codom]
  left
  exact doubleInsideExtension_codom N hN ha

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
    · rw [niceExtension, inv_atoms, Rel.inv_dom, outsideExtension_atoms, Rel.sup_codom]
      left
      rw [inv_atoms, Rel.inv_codom, outsideExtension_atoms, Rel.sup_dom]
      left
      exact ξ.doubleInsideExtension_dom N hN ha
    · rw [niceExtension, inv_atoms, Rel.inv_dom, outsideExtension_atoms, Rel.sup_codom]
      left
      rw [inv_atoms, Rel.inv_codom]
      exact outsideExtension_spec (ξ := ξ.doubleInsideExtension) N hN ha
  · rintro N hN a (ha | ha)
    · rw [niceExtension, inv_atoms, Rel.inv_codom, outsideExtension_atoms, Rel.sup_dom]
      left
      rw [inv_atoms, Rel.inv_dom, outsideExtension_atoms, Rel.sup_codom]
      left
      exact ξ.doubleInsideExtension_codom N hN ha
    · rw [niceExtension, inv_atoms, Rel.inv_codom]
      exact outsideExtension_spec
        (ξ := (ξ.doubleInsideExtension.outsideExtension ξ.doubleInsideExtension_dom)⁻¹) N hN ha

end BaseAction

end ConNF
