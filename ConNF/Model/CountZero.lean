import ConNF.Mathlib.PFun
import ConNF.Construction
import ConNF.FOA
import ConNF.Counting.CountSupportOrbit

open Cardinal Function MulAction Set Sum Quiver WithBot

open scoped Cardinal Pointwise symmDiff

universe u

namespace ConNF.MainInduction

variable [Params.{u}] [BasePositions]

local instance : Level := ⟨0⟩

theorem zeroModelData_subsingleton
    (i₁ j₁ : ModelDataLt)
    (i₂ : letI := i₁; PositionedTanglesLt) (j₂ : letI := j₁; PositionedTanglesLt)
    (i₃ : letI := i₁; TypedObjectsLt) (j₃ : letI := j₁; TypedObjectsLt)
    (i₄ : letI := i₁; PositionedObjectsLt) (j₄ : letI := j₁; PositionedObjectsLt) :
    (letI := i₁; letI := i₂; letI := i₃; letI := i₄
    {
      TSet := NewTSet
      Allowable := NewAllowable
      allowableToStructPerm := NewAllowable.toStructPerm
      allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
      has_support := by
        intro t
        obtain ⟨S, hS⟩ := t.prop
        exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
      toStructSet := ⟨NewTSet.toStructSet, NewTSet.toStructSet_injective⟩
      toStructSet_smul := NewTSet.toStructSet_smul
    } : ModelData (0 : Λ)) =
    (letI := j₁; letI := j₂; letI := j₃; letI := j₄
    {
      TSet := NewTSet
      Allowable := NewAllowable
      allowableToStructPerm := NewAllowable.toStructPerm
      allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
      has_support := by
        intro t
        obtain ⟨S, hS⟩ := t.prop
        exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
      toStructSet := ⟨NewTSet.toStructSet, NewTSet.toStructSet_injective⟩
      toStructSet_smul := NewTSet.toStructSet_smul
    }) := by
  have : i₁ = j₁
  · refine ModelDataLt.ext _ _ ?_
    funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  have : i₂ = j₂
  · refine PositionedTanglesLt.ext _ _ ?_
    funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  have : i₃ = j₃
  · funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  have : i₄ = j₄
  · funext β iβ
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp iβ.elim)
  cases this
  rfl

local instance : ModelDataLt :=
  ⟨fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim⟩
local instance : PositionedTanglesLt :=
  ⟨fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim⟩
local instance : TypedObjectsLt :=
  fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim
local instance : PositionedObjectsLt :=
  fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim

local instance zeroModelData : ModelData (0 : Λ) :=
  {
    TSet := NewTSet
    Allowable := NewAllowable
    allowableToStructPerm := NewAllowable.toStructPerm
    allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
    has_support := by
      intro t
      obtain ⟨S, hS⟩ := t.prop
      exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
    toStructSet := ⟨NewTSet.toStructSet, NewTSet.toStructSet_injective⟩
    toStructSet_smul := NewTSet.toStructSet_smul
  }

local instance zeroTypedObjects : TypedObjects (0 : Λ) :=
  {
    typedNearLitter := ⟨newTypedNearLitter, newTypedNearLitter_injective⟩
    smul_typedNearLitter := fun ρ N => NewAllowable.smul_newTypedNearLitter N ρ
  }

def zeroPath : ExtendedIndex 0 :=
  Hom.toPath (bot_lt_coe _)

theorem path_eq_zeroPath (A : ExtendedIndex 0) : A = zeroPath := by
  cases' A with β _ A h
  cases' A with γ _ A h'
  · rfl
  · change (_ : TypeIndex) < _ at h h'
    cases' β with β
    · cases lt_irrefl _ h
    have := h'.trans_le (le_of_path A)
    cases (Params.Λ_zero_le β).not_lt (coe_lt_coe.mp this)

theorem not_ltLevel (β : Λ) [i : LtLevel β] : False := by
  cases (Params.Λ_zero_le _).not_lt (coe_lt_coe.mp i.elim)

theorem eq_bot_of_ltLevel (β : TypeIndex) [LtLevel β] : β = ⊥ := by
  cases' β with β
  · rfl
  · cases not_ltLevel β

theorem eq_zero_of_leLevel (β : Λ) [i : LeLevel β] : β = 0 :=
  le_antisymm (coe_le_coe.mp i.elim) (Params.Λ_zero_le _)

theorem eq_bot_zero_of_lt (γ β : TypeIndex) [iβ : LeLevel β] [iγ : LeLevel γ] (h : γ < β) :
    γ = ⊥ ∧ β = 0 := by
  cases' β with β
  · change γ < ⊥ at h
    cases not_lt_bot h
  cases eq_zero_of_leLevel β
  cases' γ with γ
  · exact ⟨rfl, rfl⟩
  · cases (Params.Λ_zero_le γ).not_lt (coe_lt_coe.mp h)

def toSemiallowable (π : BasePerm) : Derivatives :=
  fun β _ => eq_bot_of_ltLevel β ▸ (show Allowable ⊥ from π)

theorem toSemiallowable_allowable (π : BasePerm) :
    (toSemiallowable π).IsAllowable := by
  intro β _ γ _ hβγ
  cases eq_bot_of_ltLevel β
  cases eq_bot_of_ltLevel γ

def toAllowable (π : BasePerm) : NewAllowable :=
  ⟨toSemiallowable π, toSemiallowable_allowable π⟩

def zeroDerivative : NewAllowable →* BasePerm :=
  ⟨⟨fun ρ => ρ.val ⊥,
    by simp only [NewAllowable.coe_one, Derivatives.one_apply]⟩,
    by simp only [NewAllowable.coe_mul, Derivatives.mul_apply, forall_const]⟩

instance {X : Type _} [MulAction BasePerm X] : MulAction (Allowable (0 : Λ)) X :=
  MulAction.compHom _ zeroDerivative

instance {X : Type _} [i : MulAction NewAllowable X] : MulAction (Allowable (0 : Λ)) X :=
  i

section FOA

local instance : FOAData where
  lowerModelData β _ := eq_zero_of_leLevel β ▸ zeroModelData
  lowerPositionedTangles β _ := (not_ltLevel β).elim
  lowerTypedObjects β _ := eq_zero_of_leLevel β ▸ zeroTypedObjects
  lowerPositionedObjects β _ := (not_ltLevel β).elim

local instance : FOAAssumptions where
  allowableCons {β _ γ _} hγβ :=
    have := eq_bot_zero_of_lt γ β hγβ
    this.1 ▸ this.2 ▸ zeroDerivative
  allowableCons_eq := by
    intro β _ γ _ hγβ
    obtain ⟨rfl, rfl⟩ := eq_bot_zero_of_lt γ β hγβ
    intro ρ
    simp only [Tree.comp_bot]
    rfl
  pos_lt_pos_atom {β} := (not_ltLevel β).elim
  pos_lt_pos_nearLitter {β} := (not_ltLevel β).elim
  smul_fuzz {β _ γ _ δ} := (not_ltLevel δ).elim
  allowable_of_smulFuzz := by
    intro β hβ ρs hρs
    cases eq_zero_of_leLevel β
    refine ⟨toAllowable (ρs ⊥ (bot_lt_coe _)), ?_⟩
    intro γ _ _
    cases eq_bot_of_ltLevel γ
    rfl

theorem zero_flexible {A : ExtendedIndex 0} {L : Litter} : Flexible A L := by
  cases path_eq_zeroPath A
  rintro (h | h)

def toStructNLAction (ξ : BaseNLAction) : StructNLAction 0 :=
  fun _ => ξ

theorem toStructNLAction_coherentDom (ξ : BaseNLAction) :
    (toStructNLAction ξ).CoherentDom := by
  constructor
  case mapFlexible =>
    intros
    exact zero_flexible
  case atom_bot_dom =>
    intro γ _ A ε _
    cases not_ltLevel ε
  case atom_dom =>
    intro γ _ A δ _
    cases not_ltLevel δ
  case nearLitter_dom =>
    intro γ _ A δ _
    cases not_ltLevel δ

theorem toStructNLAction_coherent (ξ : BaseNLAction) :
    (toStructNLAction ξ).Coherent := by
  constructor
  case toCoherentDom =>
    exact toStructNLAction_coherentDom ξ
  case coherent_coe =>
    intro γ _ A δ _
    cases not_ltLevel δ
  case coherent_bot =>
    intro γ _ A δ _
    cases not_ltLevel δ

/-- An instance of the freedom of action theorem for type zero. -/
theorem zero_foa (ξ : BaseNLAction) (hξ : ξ.Lawful) :
    ∃ π : BasePerm, ξ.Approximates π := by
  letI : LeLevel (0 : Λ) := ⟨WithBot.coe_le_coe.mpr (Params.Λ_zero_le _)⟩
  have := (toStructNLAction ξ).freedom_of_action ?_ (toStructNLAction_coherent ξ)
  · obtain ⟨ρ, hρ⟩ := this
    exact ⟨ρ.val ⊥, hρ zeroPath⟩
  · intro
    exact hξ

end FOA

def ZeroStrong (S : Support 0) : Prop :=
  ∀ a N₁ N₂, ⟨zeroPath, inr N₁⟩ ∈ S → ⟨zeroPath, inr N₂⟩ ∈ S → Support.Interferes a N₁ N₂ →
    ⟨zeroPath, inl a⟩ ∈ S

@[ext]
structure ZeroSpec : Type u where
  /-- The length of the support. -/
  max : κ
  /-- Positions in a support containing a near-litter. -/
  nearLitters : Set κ
  /-- Positions in a support containing an atom. -/
  atoms : Set κ
  /-- For each position in a support containing a near-litter,
  the set of all positions at which another close near-litter occurs. -/
  nearLitterSame : κ → Set κ
  /-- For each pair of near-litter positions,
  the set of all positions at which an atom in their symmetric difference occurs. -/
  symmDiff : κ → κ → Set κ
  /-- For each position in a support containing an atom,
  the set of all positions this atom occurs at. -/
  atomSame : κ → Set κ
  /-- For each position in a support containing an atom,
  the positions of near-litters that contain this atom. -/
  atomMem : κ → Set κ

instance : LE ZeroSpec where
  le σ τ :=
    σ.max = τ.max ∧
    σ.nearLitters ⊆ τ.nearLitters ∧
    σ.atoms ⊆ τ.atoms ∧
    σ.nearLitterSame ≤ τ.nearLitterSame ∧
    σ.symmDiff ≤ τ.symmDiff ∧
    σ.atomSame ≤ τ.atomSame ∧
    σ.atomMem ≤ τ.atomMem

instance : PartialOrder ZeroSpec where
  le_refl σ := ⟨rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩
  le_trans σ τ υ := by
    rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ ⟨h₁', h₂', h₃', h₄', h₅', h₆', h₇'⟩
    exact ⟨h₁.trans h₁', h₂.trans h₂', h₃.trans h₃', h₄.trans h₄',
      h₅.trans h₅', h₆.trans h₆', h₇.trans h₇'⟩
  le_antisymm σ τ := by
    rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ ⟨-, h₂', h₃', h₄', h₅', h₆', h₇'⟩
    exact ZeroSpec.ext _ _ h₁ (subset_antisymm h₂ h₂') (subset_antisymm h₃ h₃')
      (le_antisymm h₄ h₄') (le_antisymm h₅ h₅') (le_antisymm h₆ h₆') (le_antisymm h₇ h₇')

def ZeroSpec.decompose (σ : ZeroSpec) :
    κ × Set κ × Set κ × (κ → Set κ) × (κ → κ → Set κ) × (κ → Set κ) × (κ → Set κ) :=
  ⟨σ.max, σ.nearLitters, σ.atoms, σ.nearLitterSame, σ.symmDiff, σ.atomSame, σ.atomMem⟩

theorem ZeroSpec.decompose_injective : Function.Injective ZeroSpec.decompose := by
  rintro ⟨⟩ ⟨⟩ h
  cases h
  rfl

theorem mk_zeroSpec : #ZeroSpec < #μ := by
  refine (mk_le_of_injective ZeroSpec.decompose_injective).trans_lt ?_
  have hμ := Params.μ_isStrongLimit.isLimit.aleph0_le
  have hκ := Params.κ_lt_μ
  have hκ₁ := Params.μ_isStrongLimit.2 _ hκ
  have hκ₂ : (2 ^ #κ) ^ #κ < #μ
  · rwa [← Cardinal.power_mul, mul_eq_self Params.κ_isRegular.aleph0_le]
  have hκ₃ : ((2 ^ #κ) ^ #κ) ^ #κ < #μ
  · rwa [← Cardinal.power_mul, mul_eq_self Params.κ_isRegular.aleph0_le]
  simp only [mk_prod, lift_id, mk_set, mk_pi, prod_const, gt_iff_lt]
  exact mul_lt_of_lt hμ hκ (mul_lt_of_lt hμ hκ₁ (mul_lt_of_lt hμ hκ₁
    (mul_lt_of_lt hμ hκ₂ (mul_lt_of_lt hμ hκ₃ (mul_lt_of_lt hμ hκ₂ hκ₂)))))

def zeroSpec (S : Support 0) : ZeroSpec where
  max := S.max
  nearLitters := {i | ∃ hi N, S.f i hi = ⟨zeroPath, inr N⟩}
  atoms := {i | ∃ hi a, S.f i hi = ⟨zeroPath, inl a⟩}
  nearLitterSame i := {j | ∃ hi hj Ni Nj,
    S.f i hi = ⟨zeroPath, inr Ni⟩ ∧ S.f j hj = ⟨zeroPath, inr Nj⟩ ∧ Ni.1 = Nj.1}
  symmDiff i j := {k | ∃ hi hj hk Ni Nj a,
    S.f i hi = ⟨zeroPath, inr Ni⟩ ∧ S.f j hj = ⟨zeroPath, inr Nj⟩ ∧ S.f k hk = ⟨zeroPath, inl a⟩ ∧
    Ni.1 = Nj.1 ∧ a ∈ (Ni : Set Atom) ∆ Nj}
  atomSame i := {j | ∃ hi hj a,
    S.f i hi = ⟨zeroPath, inl a⟩ ∧ S.f j hj = ⟨zeroPath, inl a⟩}
  atomMem i := {j | ∃ hi hj a N,
    S.f i hi = ⟨zeroPath, inl a⟩ ∧ S.f j hj = ⟨zeroPath, inr N⟩ ∧ a ∈ N}

section Convert

variable {S T : Support (0 : Λ)}
  (hS : ZeroStrong S) (hT : ZeroStrong T) (hST : zeroSpec S = zeroSpec T)

def ConvertAtom (S T : Support 0) (aS aT : Atom) : Prop :=
  ∃ (i : κ) (hiS : i < S.max) (hiT : i < T.max),
    S.f i hiS = ⟨zeroPath, inl aS⟩ ∧ T.f i hiT = ⟨zeroPath, inl aT⟩

def ConvertNearLitter (S T : Support 0) (NS NT : NearLitter) : Prop :=
  ∃ (i : κ) (hiS : i < S.max) (hiT : i < T.max),
    S.f i hiS = ⟨zeroPath, inr NS⟩ ∧ T.f i hiT = ⟨zeroPath, inr NT⟩

theorem convertAtom_subsingleton (aS aT aT' : Atom)
    (h : ConvertAtom S T aS aT) (h' : ConvertAtom S T aS aT') : aT = aT' := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have := congr_arg ZeroSpec.atomSame hST
  dsimp only [zeroSpec] at this
  obtain ⟨_, _, a, ha₁, ha₂⟩ := (Set.ext_iff.mp (congr_fun this i) i').mp
    ⟨hiS₁, hiS₁', aS, hiS₂, hiS₂'⟩
  have h₁ := hiT₂.symm.trans ha₁
  have h₂ := hiT₂'.symm.trans ha₂
  simp only [Address.mk.injEq, inl.injEq, true_and] at h₁ h₂
  rw [h₁, h₂]

theorem convertNearLitter_fst (NS NS' NT NT' : NearLitter) (hN : NS.1 = NS'.1)
    (h : ConvertNearLitter S T NS NT) (h' : ConvertNearLitter S T NS' NT') : NT.1 = NT'.1 := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have := congr_arg ZeroSpec.nearLitterSame hST
  dsimp only [zeroSpec] at this
  obtain ⟨_, _, N₁, N₂, hN₁, hN₂, hN⟩ := (Set.ext_iff.mp (congr_fun this i) i').mp
    ⟨hiS₁, hiS₁', NS, NS', hiS₂, hiS₂', hN⟩
  have h₁ := hiT₂.symm.trans hN₁
  have h₂ := hiT₂'.symm.trans hN₂
  simp only [Address.mk.injEq, inl.injEq, true_and] at h₁ h₂
  cases h₁
  cases h₂
  exact hN

theorem convertNearLitter_fst' (NS NS' NT NT' : NearLitter) (hN : NT.1 = NT'.1)
    (h : ConvertNearLitter S T NS NT) (h' : ConvertNearLitter S T NS' NT') : NS.1 = NS'.1 := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have := congr_arg ZeroSpec.nearLitterSame hST
  dsimp only [zeroSpec] at this
  obtain ⟨_, _, N₁, N₂, hN₁, hN₂, hN⟩ := (Set.ext_iff.mp (congr_fun this i) i').mpr
    ⟨hiT₁, hiT₁', NT, NT', hiT₂, hiT₂', hN⟩
  have h₁ := hiS₂.symm.trans hN₁
  have h₂ := hiS₂'.symm.trans hN₂
  simp only [Address.mk.injEq, inl.injEq, true_and] at h₁ h₂
  cases h₁
  cases h₂
  exact hN

theorem convertNearLitter_subsingleton (NS NT NT' : NearLitter)
    (h : ConvertNearLitter S T NS NT) (h' : ConvertNearLitter S T NS NT') : NT = NT' := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have := congr_arg ZeroSpec.nearLitterSame hST
  dsimp only [zeroSpec] at this
  obtain ⟨_, _, N₁, N₂, hN₁, hN₂, hN⟩ := (Set.ext_iff.mp (congr_fun this i) i').mp
    ⟨hiS₁, hiS₁', NS, NS, hiS₂, hiS₂', rfl⟩
  have h₁ := hiT₂.symm.trans hN₁
  have h₂ := hiT₂'.symm.trans hN₂
  simp only [Address.mk.injEq, inl.injEq, true_and] at h₁ h₂
  cases h₁
  cases h₂
  have := congr_arg ZeroSpec.symmDiff hST
  dsimp only [zeroSpec] at this
  suffices : (NT : Set Atom) ∆ NT' = ∅
  · erw [symmDiff_eq_bot] at this
    exact NearLitter.ext this
  by_contra! hNT
  obtain ⟨a, ha⟩ := hNT
  obtain ⟨j, hj, hjT⟩ := hT a NT NT' ⟨i, hiT₁, hiT₂.symm⟩ ⟨i', hiT₁', hiT₂'.symm⟩
    (Support.Interferes.symmDiff hN ha)
  obtain ⟨_, _, _, N₁, N₂, b, h₁, h₂, _, h₄, h₅⟩ := (Set.ext_iff.mp (congr_fun₂ this i i') j).mpr
    ⟨hiT₁, hiT₁', hj, NT, NT', a, hiT₂, hiT₂', hjT.symm, hN, ha⟩
  have h₁ := hiS₂.symm.trans h₁
  have h₂ := hiS₂'.symm.trans h₂
  simp only [Address.mk.injEq, inl.injEq, true_and] at h₁ h₂
  cases h₁
  cases h₂
  simp only [symmDiff_self, bot_eq_empty, mem_empty_iff_false] at h₅

theorem convertAtom_dom_small :
    Small {a | ∃ a', ConvertAtom S T a a'} := by
  have : Small {i | i < S.max} := Cardinal.card_typein_lt (· < ·) S.max Params.κ_ord.symm
  refine (this.pFun_image
    (f := fun i => ⟨∃ a hi, S.f i hi = ⟨zeroPath, inl a⟩, fun h => h.choose⟩)).mono ?_
  rintro a ⟨b, i, hiS, hiT, hiS', _⟩
  have : ∃ a hi, S.f i hi = ⟨zeroPath, inl a⟩ := ⟨a, hiS, hiS'⟩
  refine ⟨i, hiS, this, ?_⟩
  have := this.choose_spec.choose_spec
  rw [hiS'] at this
  cases this
  rfl

theorem convertNearLitter_dom_small :
    Small {N | ∃ N', ConvertNearLitter S T N N'} := by
  have : Small {i | i < S.max} := Cardinal.card_typein_lt (· < ·) S.max Params.κ_ord.symm
  refine (this.pFun_image
    (f := fun i => ⟨∃N hi, S.f i hi = ⟨zeroPath, inr N⟩, fun h => h.choose⟩)).mono ?_
  rintro N ⟨N', i, hiS, hiT, hiS', _⟩
  have : ∃ N hi, S.f i hi = ⟨zeroPath, inr N⟩ := ⟨N, hiS, hiS'⟩
  refine ⟨i, hiS, this, ?_⟩
  have := this.choose_spec.choose_spec
  rw [hiS'] at this
  cases this
  rfl

noncomputable def convert : BaseNLAction :=
  {
    atomMap := PFun.ofGraph (ConvertAtom S T) (convertAtom_subsingleton hST)
    nearLitterMap := PFun.ofGraph (ConvertNearLitter S T) (convertNearLitter_subsingleton hT hST)
    atomMap_dom_small := convertAtom_dom_small
    nearLitterMap_dom_small := convertNearLitter_dom_small
  }

theorem convert_atomMap_eq {a b : Atom} (h : ConvertAtom S T a b) :
    ((convert hT hST).atomMap a).get ⟨b, h⟩ = b :=
  PFun.get_eq (hg := (convertAtom_subsingleton hST)) _ _ h

theorem convert_nearLitterMap_eq {N₁ N₂ : NearLitter}
    (h : ConvertNearLitter S T N₁ N₂) :
    ((convert hT hST).nearLitterMap N₁).get ⟨N₂, h⟩ = N₂ :=
  PFun.get_eq (hg := (convertNearLitter_subsingleton hT hST)) _ _ h

theorem convertAtom_injective {a b c : Atom}
    (ha : ConvertAtom S T a c) (hb : ConvertAtom S T b c) :
    a = b := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := ha
  obtain ⟨j, hjS₁, hjT₁, hjS₂, hjT₂⟩ := hb
  have := congr_arg ZeroSpec.atomSame hST
  dsimp only [zeroSpec] at this
  obtain ⟨_, _, d, hd₁, hd₂⟩ := (Set.ext_iff.mp (congr_fun this i) j).mpr
    ⟨hiT₁, hjT₁, c, hiT₂, hjT₂⟩
  have h₁ := hiS₂.symm.trans hd₁
  have h₂ := hjS₂.symm.trans hd₂
  simp only [Address.mk.injEq, inl.injEq, true_and] at h₁ h₂
  rw [h₁, h₂]

theorem convertAtom_eq {a a' : Atom} {N N' : NearLitter}
    (ha : ConvertAtom S T a a') (hN : ConvertNearLitter S T N N') :
    a' ∈ N' ↔ a ∈ N := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := ha
  obtain ⟨j, hjS₁, hjT₁, hjS₂, hjT₂⟩ := hN
  have := congr_arg ZeroSpec.atomMem hST
  dsimp only [zeroSpec] at this
  have := Set.ext_iff.mp (congr_fun this i) j
  simp only [exists_and_left, mem_setOf_eq] at this
  constructor
  · intro h
    obtain ⟨_, _, a'', ha'', N'', hN'', h⟩ := this.mpr ⟨hiT₁, hjT₁, a', hiT₂, N', hjT₂, h⟩
    have h₁ := ha''.symm.trans hiS₂
    have h₂ := hN''.symm.trans hjS₂
    simp only [Address.mk.injEq, inl.injEq, true_and, inr.injEq] at h₁ h₂
    cases h₁
    cases h₂
    exact h
  · intro h
    obtain ⟨_, _, a'', ha'', N'', hN'', h⟩ := this.mp ⟨hiS₁, hjS₁, a, hiS₂, N, hjS₂, h⟩
    have h₁ := ha''.symm.trans hiT₂
    have h₂ := hN''.symm.trans hjT₂
    simp only [Address.mk.injEq, inl.injEq, true_and, inr.injEq] at h₁ h₂
    cases h₁
    cases h₂
    exact h

theorem dom_of_interferes {a : Atom} {N₁ N₁' N₂ N₂' : NearLitter}
    (h : Support.Interferes a N₁ N₂)
    (hN₁ : ConvertNearLitter S T N₁ N₁') (hN₂ : ConvertNearLitter S T N₂ N₂') :
    ∃ a', ConvertAtom S T a a' := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, _⟩ := hN₁
  obtain ⟨j, hjS₁, hjT₁, hjS₂, _⟩ := hN₂
  obtain ⟨k, hk₁, hk₂⟩ := hS a N₁ N₂ ⟨i, hiS₁, hiS₂.symm⟩ ⟨j, hjS₁, hjS₂.symm⟩ h
  have := congr_arg ZeroSpec.atoms hST
  dsimp only [zeroSpec] at this
  obtain ⟨hk₃, a', hk₄⟩ := (Set.ext_iff.mp this k).mp ⟨hk₁, a, hk₂.symm⟩
  exact ⟨a', k, hk₁, hk₃, hk₂.symm, hk₄⟩

theorem ran_of_interferes {a' : Atom} {N₁ N₁' N₂ N₂' : NearLitter}
    (h : Support.Interferes a' N₁' N₂')
    (hN₁ : ConvertNearLitter S T N₁ N₁') (hN₂ : ConvertNearLitter S T N₂ N₂') :
    ∃ a, ConvertAtom S T a a' := by
  obtain ⟨i, hiS₁, hiT₁, _, hiT₂⟩ := hN₁
  obtain ⟨j, hjS₁, hjT₁, _, hjT₂⟩ := hN₂
  obtain ⟨k, hk₁, hk₂⟩ := hT a' N₁' N₂' ⟨i, hiT₁, hiT₂.symm⟩ ⟨j, hjT₁, hjT₂.symm⟩ h
  have := congr_arg ZeroSpec.atoms hST
  dsimp only [zeroSpec] at this
  obtain ⟨hk₃, a, hk₄⟩ := (Set.ext_iff.mp this k).mpr ⟨hk₁, a', hk₂.symm⟩
  exact ⟨a, k, hk₃, hk₁, hk₄, hk₂.symm⟩

theorem convert_lawful : (convert hT hST).Lawful := by
  constructor
  case atomMap_injective =>
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩ h
    rw [convert_atomMap_eq hT hST ha, convert_atomMap_eq hT hST hb] at h
    cases h
    exact convertAtom_injective hST ha hb
  case atom_mem_iff =>
    intro a ⟨a', ha⟩ N ⟨N', hN⟩
    rw [convert_atomMap_eq hT hST ha, convert_nearLitterMap_eq hT hST hN]
    exact convertAtom_eq hST ha hN
  case dom_of_mem_symmDiff =>
    intro a N₁ N₂ hN ⟨N₁', hN₁⟩ ⟨N₂', hN₂⟩ ha
    exact dom_of_interferes hS hST (Support.Interferes.symmDiff hN ha) hN₁ hN₂
  case ran_of_mem_symmDiff =>
    intro a' N₁ N₂ hN ⟨N₁', hN₁⟩ ⟨N₂', hN₂⟩ ha'
    rw [convert_nearLitterMap_eq hT hST hN₁, convert_nearLitterMap_eq hT hST hN₂] at ha'
    have hN' := convertNearLitter_fst hST N₁ N₂ N₁' N₂' hN hN₁ hN₂
    obtain ⟨a, ha⟩ := ran_of_interferes hT hST (Support.Interferes.symmDiff hN' ha') hN₁ hN₂
    refine ⟨a, ?_⟩
    rw [← convert_atomMap_eq hT hST ha]
    exact Part.get_mem _
  case dom_of_mem_inter =>
    intro a N₁ N₂ hN ⟨N₁', hN₁⟩ ⟨N₂', hN₂⟩ ha
    exact dom_of_interferes hS hST (Support.Interferes.inter hN ha) hN₁ hN₂
  case ran_of_mem_inter =>
    intro a' N₁ N₂ hN ⟨N₁', hN₁⟩ ⟨N₂', hN₂⟩ ha'
    rw [convert_nearLitterMap_eq hT hST hN₁, convert_nearLitterMap_eq hT hST hN₂] at ha'
    have hN' : N₁'.1 ≠ N₂'.1
    · contrapose! hN
      exact convertNearLitter_fst' hST N₁ N₂ N₁' N₂' hN hN₁ hN₂
    obtain ⟨a, ha⟩ := ran_of_interferes hT hST (Support.Interferes.inter hN' ha') hN₁ hN₂
    refine ⟨a, ?_⟩
    rw [← convert_atomMap_eq hT hST ha]
    exact Part.get_mem _

theorem exists_convertAllowable : ∃ ρ : Allowable (0 : Λ), ρ • S = T := by
  obtain ⟨π, hπ⟩ := zero_foa (convert hT hST) (convert_lawful hS hT hST)
  refine ⟨toAllowable π, ?_⟩
  refine Enumeration.ext' ?_ ?_
  · exact congr_arg ZeroSpec.max hST
  intro i hiS hiT
  rw [Enumeration.smul_f]
  set c := S.f i hiS with hc
  obtain ⟨A, x⟩ := c
  cases path_eq_zeroPath A
  obtain (a | N) := x
  · refine Address.ext _ _ (path_eq_zeroPath _).symm ?_
    change inl (π • a) = _
    have := congr_arg ZeroSpec.atoms hST
    dsimp only [zeroSpec] at this
    obtain ⟨_, a', hT'⟩ := (Set.ext_iff.mp this i).mp ⟨hiS, a, hc.symm⟩
    rw [hπ.map_atom a ⟨a', i, hiS, hiT, hc.symm, hT'⟩,
      convert_atomMap_eq hT hST ⟨i, hiS, hiT, hc.symm, hT'⟩, hT']
  · refine Address.ext _ _ (path_eq_zeroPath _).symm ?_
    change inr (π • N) = _
    have := congr_arg ZeroSpec.nearLitters hST
    dsimp only [zeroSpec] at this
    obtain ⟨_, N', hT'⟩ := (Set.ext_iff.mp this i).mp ⟨hiS, N, hc.symm⟩
    rw [hπ.map_nearLitter N ⟨N', i, hiS, hiT, hc.symm, hT'⟩,
      convert_nearLitterMap_eq hT hST ⟨i, hiS, hiT, hc.symm, hT'⟩, hT']

end Convert

def interference (S : Set (Address 0)) : Set Atom :=
  {a | ⟨zeroPath, inl a⟩ ∈ S} ∪
  {a | ∃ N₁ N₂, ⟨zeroPath, inr N₁⟩ ∈ S ∧ ⟨zeroPath, inr N₂⟩ ∈ S ∧ Support.Interferes a N₁ N₂}

def interference' (S : Set (Address 0)) : Set Atom :=
  (⋃ (a ∈ {a | ⟨zeroPath, inl a⟩ ∈ S}), {a}) ∪
  (⋃ (N₁ ∈ {N₁ | ⟨zeroPath, inr N₁⟩ ∈ S}) (N₂ ∈ {N₂ | ⟨zeroPath, inr N₂⟩ ∈ S})
    (a ∈ {a | Support.Interferes a N₁ N₂}), {a})

theorem interference_eq_interference' (S : Set (Address 0)) : interference S = interference' S := by
  rw [interference, interference']
  aesop

theorem interference_small (S : Set (Address 0)) (hS : Small S) : Small (interference S) := by
  rw [interference_eq_interference']
  refine Small.union ?_ ?_
  · refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine hS.preimage (f := fun a => ⟨zeroPath, inl a⟩) ?_
    intro a b h
    cases h
    rfl
  · refine Small.bUnion
        ?_ (fun N₁ _ => Small.bUnion
        ?_ (fun N₂ _ => Small.bUnion
        (Support.interferes_small N₁ N₂) (fun a _ => small_singleton _)))
    · refine hS.preimage (f := fun N => ⟨zeroPath, inr N⟩) ?_
      intro a b h
      cases h
      rfl
    · refine hS.preimage (f := fun N => ⟨zeroPath, inr N⟩) ?_
      intro a b h
      cases h
      rfl

def disjointNL' (S : Set (Address 0)) (N : NearLitter) : Set Atom :=
  N \ interference S

theorem disjointNL'_isNear (S : Set (Address 0)) (hS : Small S) (N : NearLitter) :
    IsNearLitter N.1 (disjointNL' S N) := by
  suffices : Small ((N : Set Atom) ∆ disjointNL' S N)
  · have h : Small _ := N.2.prop
    have := h.symmDiff this
    rw [symmDiff_assoc, ← symmDiff_assoc (N.snd : Set Atom)] at this
    erw [symmDiff_self] at this
    rw [bot_eq_empty, empty_symmDiff] at this
    exact this
  refine Small.union ?_ ?_
  · rw [disjointNL', sdiff_sdiff_right_self]
    exact (interference_small S hS).mono inter_subset_right
  · refine small_of_forall_not_mem ?_
    rintro x ⟨hx, hxN⟩
    simp only [disjointNL', mem_iInter, SetLike.mem_coe, and_imp] at hx
    exact hxN hx.1

theorem disjointNL'_eq (S : Set (Address 0)) (N₁ N₂ : NearLitter)
    (hN₁ : ⟨zeroPath, inr N₁⟩ ∈ S) (hN₂ : ⟨zeroPath, inr N₂⟩ ∈ S) (h : N₁.1 = N₂.1) :
    disjointNL' S N₁ = disjointNL' S N₂ := by
  rw [disjointNL', disjointNL']
  ext a
  constructor
  · rintro ⟨ha₁, ha₂⟩
    by_cases ha₃ : a ∈ N₂
    · exact ⟨ha₃, ha₂⟩
    refine (ha₂ ?_).elim
    exact (Or.inr ⟨N₁, N₂, hN₁, hN₂, Support.Interferes.symmDiff h (Or.inl ⟨ha₁, ha₃⟩)⟩)
  · rintro ⟨ha₁, ha₂⟩
    by_cases ha₃ : a ∈ N₁
    · exact ⟨ha₃, ha₂⟩
    refine (ha₂ ?_).elim
    exact (Or.inr ⟨N₁, N₂, hN₁, hN₂, Support.Interferes.symmDiff h (Or.inr ⟨ha₁, ha₃⟩)⟩)

def disjointNL (S : Set (Address 0)) (hS : Small S) (N : NearLitter) : NearLitter :=
  ⟨N.1, disjointNL' S N, disjointNL'_isNear S hS N⟩

theorem disjointNL_eq (S : Set (Address 0)) (hS : Small S) (N₁ N₂ : NearLitter)
    (hN₁ : ⟨zeroPath, inr N₁⟩ ∈ S) (hN₂ : ⟨zeroPath, inr N₂⟩ ∈ S) (h : N₁.1 = N₂.1) :
    disjointNL S hS N₁ = disjointNL S hS N₂ :=
  NearLitter.ext (disjointNL'_eq S N₁ N₂ hN₁ hN₂ h)

def disjointNLs (S : Set (Address 0)) (hS : Small S) : Set NearLitter :=
  {N' | ∃ N, ⟨zeroPath, inr N⟩ ∈ S ∧ N' = disjointNL S hS N}

def disjointNLs' (S : Set (Address 0)) (hS : Small S) : Set NearLitter :=
  ⋃ (N ∈ {N | ⟨zeroPath, inr N⟩ ∈ S}), {disjointNL S hS N}

theorem disjointNLs_eq_disjointNLs' (S : Set (Address 0)) (hS : Small S) :
    disjointNLs S hS = disjointNLs' S hS := by
  rw [disjointNLs, disjointNLs']
  aesop

theorem disjointNLs_small (S : Set (Address 0)) (hS : Small S) :
    Small (disjointNLs S hS) := by
  rw [disjointNLs_eq_disjointNLs', disjointNLs']
  refine Small.bUnion ?_ (fun _ _ => small_singleton _)
  refine hS.preimage (f := fun N => ⟨zeroPath, inr N⟩) ?_
  intro N₁ N₂ h
  cases h
  rfl

def disjointSupport (S : Set (Address 0)) (hS : Small S) : Set (Address 0) :=
  {c | ∃ a, c = ⟨zeroPath, inl a⟩ ∧ a ∈ interference S} ∪
  {c | ∃ N, c = ⟨zeroPath, inr N⟩ ∧ N ∈ disjointNLs S hS}

theorem disjointSupport_small (S : Set (Address 0)) (hS : Small S) :
    Small (disjointSupport S hS) := by
  refine Small.union ?_ ?_
  · have := interference_small S hS
    refine (this.image (f := fun a => ⟨zeroPath, inl a⟩)).mono ?_
    rintro c ⟨a, rfl, ha⟩
    exact ⟨a, ha, rfl⟩
  · have := disjointNLs_small S hS
    refine (this.image (f := fun N => ⟨zeroPath, inr N⟩)).mono ?_
    rintro c ⟨N, rfl, hN⟩
    exact ⟨N, hN, rfl⟩

@[simp]
theorem atom_mem_disjointSupport (S : Set (Address 0)) (hS : Small S) (a : Atom) :
    ⟨zeroPath, inl a⟩ ∈ disjointSupport S hS ↔ a ∈ interference S := by
  rw [disjointSupport]
  aesop

@[simp]
theorem nearLitter_mem_disjointSupport (S : Set (Address 0)) (hS : Small S) (N : NearLitter) :
    ⟨zeroPath, inr N⟩ ∈ disjointSupport S hS ↔ N ∈ disjointNLs S hS := by
  rw [disjointSupport]
  aesop

theorem disjointSupport_supports (S : Set (Address 0)) (hS : Small S)
    (c : Address (0 : Λ)) (hc : c ∈ S) :
    MulAction.Supports (Allowable (0 : Λ))
      (show Set (Address (0 : Λ)) from disjointSupport S hS) c := by
  intro ρ hρ
  obtain ⟨A, x⟩ := c
  simp only [Allowable.smul_address_eq_iff] at hρ ⊢
  cases path_eq_zeroPath A
  obtain (a | N) := x
  · change inl (_ • _) = _
    refine hρ (a := ⟨zeroPath, inl a⟩) ?_
    rw [atom_mem_disjointSupport]
    exact Or.inl hc
  change inr (_ • _) = inr _
  rw [inr.injEq]
  refine NearLitter.ext ?_
  rw [BasePerm.smul_nearLitter_coe]
  ext a : 1
  constructor
  · intro ha
    obtain ⟨a, ha, rfl⟩ := ha
    by_cases ha' : a ∈ interference S
    · have := hρ (a := ⟨zeroPath, inl a⟩) (by rwa [atom_mem_disjointSupport])
      simp only [smul_inl, inl.injEq] at this ⊢
      rwa [this]
    · have := hρ (a := ⟨zeroPath, inr (disjointNL S hS N)⟩) ?_
      · simp only [smul_inr, inr.injEq] at this
        have := congr_arg SetLike.coe this
        rw [BasePerm.smul_nearLitter_coe, smul_eq_iff_eq_inv_smul] at this
        have := (Set.ext_iff.mp this a).mp ⟨ha, ha'⟩
        rw [mem_smul_set_iff_inv_smul_mem, inv_inv] at this
        exact this.1
      · rw [nearLitter_mem_disjointSupport]
        exact ⟨N, hc, rfl⟩
  · intro ha
    rw [mem_smul_set_iff_inv_smul_mem]
    by_cases ha' : a ∈ interference S
    · have := hρ (a := ⟨zeroPath, inl _⟩) (by rwa [atom_mem_disjointSupport])
      simp only [smul_inl, inl.injEq] at this ⊢
      rwa [← this, inv_smul_smul]
    · have := hρ (a := ⟨zeroPath, inr (disjointNL S hS N)⟩) ?_
      · simp only [smul_inr, inr.injEq] at this
        have := congr_arg SetLike.coe this
        rw [BasePerm.smul_nearLitter_coe] at this
        have := (Set.ext_iff.mp this _).mpr ⟨ha, ha'⟩
        rw [mem_smul_set_iff_inv_smul_mem] at this
        exact this.1
      · rw [nearLitter_mem_disjointSupport]
        exact ⟨N, hc, rfl⟩

structure DisjointSupport (S : Set (Address 0)) : Prop where
  nearLitter (N₁ N₂ : NearLitter)
    (hN₁ : ⟨zeroPath, inr N₁⟩ ∈ S) (hN₂ : ⟨zeroPath, inr N₂⟩ ∈ S) :
    N₁ = N₂ ∨ (N₁ : Set Atom) ∩ N₂ = ∅
  atom (a : Atom) (N : NearLitter)
    (ha : ⟨zeroPath, inl a⟩ ∈ S) (hN : ⟨zeroPath, inr N⟩ ∈ S) :
    a ∉ N

theorem disjointSupport_disjointSupport (S : Set (Address 0)) (hS : Small S) :
    DisjointSupport (disjointSupport S hS) := by
  constructor
  · intro N₁ N₂ hN₁ hN₂
    rw [nearLitter_mem_disjointSupport] at hN₁ hN₂
    obtain ⟨N₁, hN₁, rfl⟩ := hN₁
    obtain ⟨N₂, hN₂, rfl⟩ := hN₂
    by_cases hN : N₁.1 = N₂.1
    · exact Or.inl (disjointNL_eq S hS N₁ N₂ hN₁ hN₂ hN)
    refine Or.inr ?_
    rw [Set.eq_empty_iff_forall_not_mem]
    rintro a ⟨⟨ha₁, ha₃⟩, ⟨ha₂, _⟩⟩
    refine ha₃ (Or.inr ⟨N₁, N₂, hN₁, hN₂, Support.Interferes.inter hN ⟨ha₁, ha₂⟩⟩)
  · intro a N ha hN haN
    rw [atom_mem_disjointSupport] at ha
    rw [nearLitter_mem_disjointSupport] at hN
    obtain ⟨N, _, rfl⟩ := hN
    cases haN.2 ha

theorem disjointSupport_zeroStrong (S : Support 0) (hS : DisjointSupport S) :
    ZeroStrong S := by
  intro a N₁ N₂ hN₁ hN₂ haN
  obtain (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) := haN
  · obtain (rfl | hN) := hS.nearLitter N₁ N₂ hN₁ hN₂
    · simp only [symmDiff_self, bot_eq_empty, mem_empty_iff_false] at h₂
    · have := NearLitter.inter_nonempty_of_fst_eq_fst h₁
      simp_all only [Set.not_nonempty_empty]
  · obtain (rfl | hN) := hS.nearLitter N₁ N₂ hN₁ hN₂
    · cases h₁ rfl
    · simp_all only [ne_eq, mem_empty_iff_false]

theorem zeroStrong_add (S : Support 0) (hS : DisjointSupport S) (a : Atom) :
    ZeroStrong (S + Enumeration.singleton ⟨zeroPath, inl a⟩) := by
  intro b N₁ N₂ hN₁ hN₂ hbN
  simp only [Enumeration.mem_add_iff, Enumeration.mem_singleton_iff, Address.mk.injEq, and_false,
    or_false, inl.injEq, true_and] at hN₁ hN₂ ⊢
  exact Or.inl (disjointSupport_zeroStrong S hS b N₁ N₂ hN₁ hN₂ hbN)

theorem nearLitter_le_max_add {S : Support 0} {a : Atom} {N : NearLitter} {i : κ}
    {hi : i < (S + Enumeration.singleton ⟨zeroPath, inl a⟩ : Support 0).max} :
    (S + Enumeration.singleton ⟨zeroPath, inl a⟩ : Support 0).f i hi = ⟨zeroPath, inr N⟩ →
    i < S.max := by
  intro hN
  by_contra h
  rw [Enumeration.add_f_right _ (le_of_not_lt h)] at hN
  cases hN

theorem zeroStrong_spec_le (S : Support 0) (hS : DisjointSupport S)
    (a : Atom) (b : Atom) (ha : ⟨zeroPath, inl a⟩ ∉ S)
    (hab : ∀ N, ⟨zeroPath, inr N⟩ ∈ S → (a ∈ N ↔ b ∈ N)) :
    zeroSpec (S + Enumeration.singleton ⟨zeroPath, inl a⟩) ≤
    zeroSpec (S + Enumeration.singleton ⟨zeroPath, inl b⟩) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [zeroSpec]
  · rintro i ⟨hi, N, hN⟩
    have hi' := nearLitter_le_max_add hN
    refine ⟨hi, N, ?_⟩
    rwa [Enumeration.add_f_left hi'] at hN ⊢
  · rintro i ⟨hi, c, hc⟩
    by_cases hi' : i < S.max
    · refine ⟨hi, c, ?_⟩
      rwa [Enumeration.add_f_left hi'] at hc ⊢
    · rw [Enumeration.add_f_right _ (le_of_not_lt hi')] at hc
      cases hc
      refine ⟨hi, b, ?_⟩
      rw [Enumeration.add_f_right _ (le_of_not_lt hi')]
      rfl
  · rintro i j ⟨hi, hj, Ni, Nj, hNi, hNj, h⟩
    have hi' := nearLitter_le_max_add hNi
    have hj' := nearLitter_le_max_add hNj
    refine ⟨hi, hj, Ni, Nj, ?_, ?_, h⟩
    · rwa [Enumeration.add_f_left hi'] at hNi ⊢
    · rwa [Enumeration.add_f_left hj'] at hNj ⊢
  · rintro i j k ⟨hi, hj, hk, Ni, Nj, c, hNi, hNj, hc, hN, hcN⟩
    have hi' := nearLitter_le_max_add hNi
    have hj' := nearLitter_le_max_add hNj
    rw [Enumeration.add_f_left hi'] at hNi
    rw [Enumeration.add_f_left hj'] at hNj
    by_cases hk' : k < S.max
    · refine ⟨hi, hj, hk, Ni, Nj, c, ?_⟩
      obtain (hcN | hcN) := hcN
      · exfalso
        refine hS.atom c Ni ?_ ?_ hcN.1
        · rw [Enumeration.add_f_left hk'] at hc
          exact ⟨k, hk', hc.symm⟩
        · exact ⟨i, hi', hNi.symm⟩
      · exfalso
        refine hS.atom c Nj ?_ ?_ hcN.1
        · rw [Enumeration.add_f_left hk'] at hc
          exact ⟨k, hk', hc.symm⟩
        · exact ⟨j, hj', hNj.symm⟩
    · rw [Enumeration.add_f_right _ (le_of_not_lt hk')] at hc
      cases hc
      refine ⟨hi, hj, hk, Ni, Nj, b, ?_, ?_, ?_, hN, ?_⟩
      · rwa [Enumeration.add_f_left hi']
      · rwa [Enumeration.add_f_left hj']
      · rw [Enumeration.add_f_right _ (le_of_not_lt hk')]
        rfl
      · obtain (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) := hcN
        · erw [hab Ni ⟨i, hi', hNi.symm⟩] at ha₁
          erw [hab Nj ⟨j, hj', hNj.symm⟩] at ha₂
          exact Or.inl ⟨ha₁, ha₂⟩
        · erw [hab Nj ⟨j, hj', hNj.symm⟩] at ha₁
          erw [hab Ni ⟨i, hi', hNi.symm⟩] at ha₂
          exact Or.inr ⟨ha₁, ha₂⟩
  · rintro i j ⟨hi, hj, c, hci, hcj⟩
    by_cases hi' : i < S.max
    · by_cases hj' : j < S.max
      · refine ⟨hi, hj, c, ?_⟩
        simp only [Enumeration.add_f_left hi', Enumeration.add_f_left hj'] at hci hcj ⊢
        exact ⟨hci, hcj⟩
      · rw [Enumeration.add_f_left hi'] at hci
        rw [Enumeration.add_f_right _ (le_of_not_lt hj'), ← hci, Enumeration.singleton_f] at hcj
        cases ha ⟨i, hi', hcj⟩
    · by_cases hj' : j < S.max
      · rw [Enumeration.add_f_right _ (le_of_not_lt hi')] at hci
        rw [Enumeration.add_f_left hj', ← hci, Enumeration.singleton_f] at hcj
        cases ha ⟨j, hj', hcj.symm⟩
      · refine ⟨hi, hj, b, ?_⟩
        simp only [Enumeration.add_f_right _ (le_of_not_lt hi'), Enumeration.singleton_f,
          Enumeration.add_f_right _ (le_of_not_lt hj'), and_self]
  · rintro i j ⟨hi, hj, c, N, hc, hN, hcN⟩
    have hj' := nearLitter_le_max_add hN
    rw [Enumeration.add_f_left hj'] at hN
    by_cases hi' : i < S.max
    · rw [Enumeration.add_f_left hi'] at hc
      cases hS.atom c N ⟨i, hi', hc.symm⟩ ⟨j, hj', hN.symm⟩ hcN
    · rw [Enumeration.add_f_right _ (le_of_not_lt hi')] at hc
      cases hc
      refine ⟨hi, hj, b, N, ?_, ?_, ?_⟩
      · rw [Enumeration.add_f_right _ (le_of_not_lt hi')]
        rfl
      · rw [Enumeration.add_f_left hj', hN]
      · rwa [← hab]
        exact ⟨j, hj', hN.symm⟩

theorem zeroStrong_spec_eq (S : Support 0) (hS : DisjointSupport S)
    (a : Atom) (b : Atom) (ha : ⟨zeroPath, inl a⟩ ∉ S) (hb : ⟨zeroPath, inl b⟩ ∉ S)
    (hab : ∀ N, ⟨zeroPath, inr N⟩ ∈ S → (a ∈ N ↔ b ∈ N)) :
    zeroSpec (S + Enumeration.singleton ⟨zeroPath, inl a⟩) =
    zeroSpec (S + Enumeration.singleton ⟨zeroPath, inl b⟩) := by
  refine le_antisymm ?_ ?_
  exact zeroStrong_spec_le S hS a b ha hab
  refine zeroStrong_spec_le S hS b a hb ?_
  intro N hN
  rw [hab N hN]

theorem exists_swap (S : Set (Address (0 : Λ))) (hS₁ : Small S) (hS₂ : DisjointSupport S)
    (a b : Atom) (ha : ⟨zeroPath, inl a⟩ ∉ S) (hb : ⟨zeroPath, inl b⟩ ∉ S)
    (hab : ∀ N, ⟨zeroPath, inr N⟩ ∈ S → (a ∈ N ↔ b ∈ N)) :
    ∃ ρ : Allowable (0 : Λ), (∀ c ∈ S, ρ • c = c) ∧ ρ • a = b := by
  obtain ⟨ρ, hρ⟩ := exists_convertAllowable
    (zeroStrong_add (Enumeration.ofSet S hS₁) (by rwa [Enumeration.ofSet_coe]) a)
    (zeroStrong_add (Enumeration.ofSet S hS₁) (by rwa [Enumeration.ofSet_coe]) b)
    (zeroStrong_spec_eq (Enumeration.ofSet S hS₁) (by rwa [Enumeration.ofSet_coe]) a b
      (by rwa [Enumeration.mem_ofSet_iff]) (by rwa [Enumeration.mem_ofSet_iff])
      (by simp_rw [Enumeration.mem_ofSet_iff]; exact hab))
  refine ⟨ρ, ?_, ?_⟩
  · rintro c hc
    obtain ⟨i, hi, rfl⟩ := (Enumeration.mem_ofSet_iff S hS₁ c).mpr hc
    have := support_f_congr hρ i (hi.trans_le (κ_le_self_add _ _))
    simp only [Enumeration.smul_add] at this
    rw [Enumeration.add_f_left hi, Enumeration.add_f_left (by exact hi)] at this
    exact this
  · have := support_f_congr hρ (_ + 0) (add_lt_add_left κ_zero_lt_one _)
    simp only [Enumeration.smul_add] at this
    erw [Enumeration.add_f_right_add (by exact κ_zero_lt_one),
      Enumeration.add_f_right_add (by exact κ_zero_lt_one)] at this
    simp only [coe_zero, Enumeration.smul_f, Enumeration.singleton_f] at this
    cases this
    rfl

/-! In the following lemmas, `e` is the `⊥`-extension of a `0`-set. -/

theorem mem_iff_mem_of_nearLitter_mem_disjointSupport
    (S : Set (Address (0 : Λ))) (hS₁ : Small S) (hS₂ : DisjointSupport S)
    (e : Set Atom) (heS : MulAction.Supports (Allowable (0 : Λ)) S e)
    (N : NearLitter) (hN : ⟨zeroPath, inr N⟩ ∈ S)
    (a b : Atom) (ha : a ∈ N) (hb : b ∈ N) : a ∈ e ↔ b ∈ e := by
  have := exists_swap S hS₁ hS₂ a b ?_ ?_ ?_
  · obtain ⟨ρ, hρ, rfl⟩ := this
    have := Set.ext_iff.mp (heS ρ hρ) (ρ • a)
    rw [smul_mem_smul_set_iff] at this
    exact this
  · intro ha'
    exact hS₂.atom a N ha' hN ha
  · intro hb'
    exact hS₂.atom b N hb' hN hb
  · intro N' hN'
    obtain (rfl | hNN') := hS₂.nearLitter N N' hN hN'
    · simp only [ha, hb]
    · rw [Set.eq_empty_iff_forall_not_mem] at hNN'
      constructor
      · intro h
        cases hNN' a ⟨ha, h⟩
      · intro h
        cases hNN' b ⟨hb, h⟩

theorem mem_iff_mem_of_not_nearLitter_mem_disjointSupport
    (S : Set (Address (0 : Λ))) (hS₁ : Small S) (hS₂ : DisjointSupport S)
    (e : Set Atom) (heS : MulAction.Supports (Allowable (0 : Λ)) S e)
    (a b : Atom) (haS : ⟨zeroPath, inl a⟩ ∉ S) (hbS : ⟨zeroPath, inl b⟩ ∉ S)
    (ha : ∀ N, ⟨zeroPath, inr N⟩ ∈ S → a ∉ N) (hb : ∀ N, ⟨zeroPath, inr N⟩ ∈ S → b ∉ N) :
    a ∈ e ↔ b ∈ e := by
  have := exists_swap S hS₁ hS₂ a b haS hbS ?_
  · obtain ⟨ρ, hρ, rfl⟩ := this
    have := Set.ext_iff.mp (heS ρ hρ) (ρ • a)
    rw [smul_mem_smul_set_iff] at this
    exact this
  · intro N hN
    constructor
    · intro ha'
      cases ha N hN ha'
    · intro hb'
      cases hb N hN hb'

def infoIn (S : Support 0) (e : Set Atom) : Set κ :=
  {i | ∃ hi, (∃ a, S.f i hi = ⟨zeroPath, inl a⟩ ∧ a ∈ e) ∨
    (∃ N, S.f i hi = ⟨zeroPath, inr N⟩ ∧ (N : Set Atom) ⊆ e)}

def infoOut (S : Support 0) (e : Set Atom) : Prop :=
  ∀ a, ⟨zeroPath, inl a⟩ ∉ S → (∀ N, ⟨zeroPath, inr N⟩ ∈ S → a ∉ N) → a ∈ e

theorem atom_mem_infoIn_iff {S : Support 0} {e : Set Atom}
    {i : κ} {hi : i < S.max} {a : Atom} (ha : ⟨zeroPath, inl a⟩ = S.f i hi) :
    i ∈ infoIn S e ↔ a ∈ e := by
  rw [infoIn]
  aesop

theorem nearLitter_mem_infoIn_iff {S : Support 0} {e : Set Atom}
    {i : κ} {hi : i < S.max} {N : NearLitter} (hN : ⟨zeroPath, inr N⟩ = S.f i hi) :
    i ∈ infoIn S e ↔ (N : Set Atom) ⊆ e := by
  rw [infoIn]
  aesop

theorem nearLitter_mem_infoIn_iff' {S : Support (0 : Λ)} (hS : DisjointSupport S.carrier)
    {e : Set Atom} (he : MulAction.Supports (Allowable (0 : Λ)) S.carrier e)
    {i : κ} {hi : i < S.max} {N : NearLitter} (hN : ⟨zeroPath, inr N⟩ = S.f i hi) :
    i ∈ infoIn S e ↔ ∃ a ∈ N, a ∈ e := by
  rw [nearLitter_mem_infoIn_iff hN]
  constructor
  · intro hN'
    obtain ⟨a, ha⟩ := N.nonempty
    exact ⟨a, ha, hN' ha⟩
  · rintro ⟨a, haN, hae⟩ b hbN
    rw [mem_iff_mem_of_nearLitter_mem_disjointSupport
      S.carrier S.small hS e he N ⟨i, hi, hN⟩ a b haN hbN] at hae
    exact hae

theorem mk_outside (S : Support (0 : Λ)) :
    #({a | ⟨zeroPath, inl a⟩ ∈ S} ∪
      ⋃ (N ∈ {N : NearLitter | ⟨zeroPath, inr N⟩ ∈ S}), N : Set Atom) < #μ := by
  refine (Cardinal.mk_union_le _ _).trans_lt ?_
  refine add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
  · refine (S.small.preimage (f := fun a => ⟨zeroPath, inl a⟩) ?_).trans Params.κ_lt_μ
    intro a₁ a₂ h
    cases h
    rfl
  · refine (Cardinal.mk_bUnion_le' _ _).trans_lt ?_
    refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
    · refine (S.small.preimage (f := fun N => ⟨zeroPath, inr N⟩) ?_).trans Params.κ_lt_μ
      intro N₁ N₂ h
      cases h
      rfl
    · simp only [coe_zero, coe_setOf, mem_setOf_eq, SetLike.coe_sort_coe, mk_nearLitter'']
      exact (ciSup_le' (fun _ => le_rfl)).trans_lt Params.κ_lt_μ

theorem exists_atom_outside (S : Support (0 : Λ)) :
    ∃ a, ⟨zeroPath, inl a⟩ ∉ S ∧ (∀ N, ⟨zeroPath, inr N⟩ ∈ S → a ∉ N) := by
  by_contra h
  have : ∀ a, True → a ∈
      {a | ⟨zeroPath, inl a⟩ ∈ S} ∪ ⋃ (N ∈ {N : NearLitter | ⟨zeroPath, inr N⟩ ∈ S}), N
  · intro a _
    simp only [coe_zero, mem_setOf_eq, mem_union, mem_iUnion, SetLike.mem_coe, exists_prop]
    push_neg at h
    by_cases ha : ⟨zeroPath, inl a⟩ ∈ S
    · exact Or.inl ha
    · exact Or.inr (h a ha)
  have := mk_subtype_le_of_subset this
  erw [Cardinal.mk_univ] at this
  have := this.trans_lt (mk_outside S)
  simp only [mk_atom, lt_self_iff_false] at this

theorem infoOut_iff {S : Support (0 : Λ)} (hS : DisjointSupport S.carrier)
    {e : Set Atom} (he : MulAction.Supports (Allowable (0 : Λ)) S.carrier e) :
    infoOut S e ↔
      ∃ a, ⟨zeroPath, inl a⟩ ∉ S ∧ (∀ N, ⟨zeroPath, inr N⟩ ∈ S → a ∉ N) ∧ a ∈ e := by
  constructor
  · intro h
    obtain ⟨a, ha₁, ha₂⟩ := exists_atom_outside S
    exact ⟨a, ha₁, ha₂, h a ha₁ ha₂⟩
  · rintro ⟨a, ha₁, ha₂, hae⟩ b hb₁ hb₂
    rw [mem_iff_mem_of_not_nearLitter_mem_disjointSupport
      S.carrier S.small hS e he a b ha₁ hb₁ ha₂ hb₂] at hae
    exact hae

theorem info_injective' (S : Support (0 : Λ)) (hS : DisjointSupport S.carrier) (e₁ e₂ : Set Atom)
    (h₁ : MulAction.Supports (Allowable (0 : Λ)) S.carrier e₁)
    (h₂ : MulAction.Supports (Allowable (0 : Λ)) S.carrier e₂)
    (hei : infoIn S e₁ = infoIn S e₂)
    (heo : infoOut S e₁ ↔ infoOut S e₂) :
    e₁ = e₂ := by
  ext a : 1
  by_cases ha : ⟨zeroPath, inl a⟩ ∈ S
  · obtain ⟨i, hi, ha⟩ := ha
    have := Set.ext_iff.mp hei i
    rw [atom_mem_infoIn_iff ha, atom_mem_infoIn_iff ha] at this
    exact this
  by_cases ha' : ∃ N, ⟨zeroPath, inr N⟩ ∈ S ∧ a ∈ N
  · obtain ⟨N, ⟨i, hi, hN⟩, haN⟩ := ha'
    have := Set.ext_iff.mp hei i
    constructor
    · intro hae
      rw [nearLitter_mem_infoIn_iff' hS h₁ hN, nearLitter_mem_infoIn_iff hN] at this
      exact this.mp ⟨a, haN, hae⟩ haN
    · intro hae
      rw [nearLitter_mem_infoIn_iff hN, nearLitter_mem_infoIn_iff' hS h₂ hN] at this
      exact this.mpr ⟨a, haN, hae⟩ haN
  push_neg at ha'
  · constructor
    · intro hae
      rw [infoOut_iff hS h₁, infoOut] at heo
      exact heo.mp ⟨a, ha, ha', hae⟩ a ha ha'
    · intro hae
      rw [infoOut, infoOut_iff hS h₂] at heo
      exact heo.mpr ⟨a, ha, ha', hae⟩ a ha ha'

def info (S : Support (0 : Λ))
    (e : {e : Set Atom // MulAction.Supports (Allowable (0 : Λ)) S.carrier e}) : Set κ × Prop :=
  (infoIn S e, infoOut S e)

theorem info_injective (S : Support (0 : Λ)) (hS : DisjointSupport S.carrier) :
    Function.Injective (info S) := by
  intro e₁ e₂ h
  simp only [info, coe_zero, Prod.mk.injEq, eq_iff_iff] at h
  exact Subtype.coe_injective (info_injective' S hS e₁ e₂ e₁.prop e₂.prop h.1 h.2)

def zeroStrong (S : Set (Address 0)) : Set (Address 0) :=
  S ∪
  {c | ∃ a N₁ N₂, c = ⟨zeroPath, inl a⟩ ∧ ⟨zeroPath, inr N₁⟩ ∈ S ∧
    ⟨zeroPath, inr N₂⟩ ∈ S ∧ Support.Interferes a N₁ N₂}

theorem zeroStrong_small {S : Set (Address 0)} (hS : Small S) : Small (zeroStrong S) := by
  refine Small.union hS ?_
  refine ((interference_small S hS).image (f := fun a => ⟨zeroPath, inl a⟩)).mono ?_
  rintro _ ⟨a, N₁, N₂, rfl, hc⟩
  exact ⟨a, Or.inr ⟨N₁, N₂, hc⟩, rfl⟩

theorem zeroStrong_zeroStrong (S : Support 0) :
    ZeroStrong (Enumeration.ofSet (zeroStrong _) (zeroStrong_small S.small)) := by
  intro a N₁ N₂ hN₁ hN₂ ha
  simp only [zeroStrong, exists_and_left, Enumeration.mem_ofSet_iff, mem_union, mem_setOf_eq,
    Address.mk.injEq, and_false, false_and, exists_const, or_false, inl.injEq, true_and,
    exists_eq_left'] at hN₁ hN₂ ⊢
  exact Or.inr ⟨N₁, hN₁, N₂, hN₂, ha⟩

theorem subset_zeroStrong (S : Support 0) :
    S.carrier ⊆ Enumeration.ofSet (zeroStrong _) (zeroStrong_small S.small) := by
  simp only [zeroStrong, exists_and_left, Enumeration.ofSet_coe, subset_union_left]

theorem exists_hom_zeroStrong (S : Support 0) :
    Nonempty (SupportHom S (Enumeration.ofSet (zeroStrong _) (zeroStrong_small S.small))) := by
  have := subset_zeroStrong S
  choose I hI₁ hI₂ using this
  refine ⟨⟨fun i => if h : i < S.max then I ⟨i, h, rfl⟩ else 0, ?_, ?_⟩⟩
  · intro i hi
    simp only [dif_pos hi]
    exact hI₁ _
  · intro i hi
    simp only [dif_pos hi]
    exact hI₂ _

structure WeakZeroSpec : Type u where
  max : κ
  f : κ → κ
  σ : ZeroSpec

def WeakZeroSpec.Specifies (W : WeakZeroSpec) (S : Support 0) : Prop :=
  ∃ (T : Support 0) (F : SupportHom S T),
    ZeroStrong T ∧ W.max = S.max ∧ W.f = F.f ∧ W.σ = zeroSpec T

theorem hasWeakZeroSpec (S : Support 0) : ∃ W : WeakZeroSpec, W.Specifies S := by
  obtain ⟨F⟩ := exists_hom_zeroStrong S
  refine ⟨⟨S.max, F.f, zeroSpec (Enumeration.ofSet (zeroStrong _) (zeroStrong_small S.small))⟩, ?_⟩
  exact ⟨(Enumeration.ofSet (zeroStrong _) (zeroStrong_small S.small)), F,
    zeroStrong_zeroStrong S, rfl, rfl, rfl⟩

theorem orbit_eq_of_weakSpec_eq (S T : Support (0 : Λ)) (W : WeakZeroSpec)
    (hS : W.Specifies S) (hT : W.Specifies T) :
    SupportOrbit.mk S = SupportOrbit.mk T := by
  obtain ⟨S', FS, hS', hWS, hFS, hSσ⟩ := hS
  obtain ⟨T', FT, hT', hWT, hFT, hTσ⟩ := hT
  obtain ⟨ρ, hρ⟩ := exists_convertAllowable hS' hT' (hSσ.symm.trans hTσ)
  suffices : ρ • S = T
  · symm
    rw [← SupportOrbit.mem_def, SupportOrbit.mem_mk_iff]
    exact ⟨ρ, this⟩
  refine Enumeration.ext' (hWS.symm.trans hWT) ?_
  intro i hS hT
  have := support_f_congr hρ (W.f i) (hFS ▸ FS.hf i hS)
  rw [Enumeration.smul_f] at this ⊢
  rw [FS.f_eq i hS, FT.f_eq i hT]
  simp only [← hFS, ← hFT]
  exact this

noncomputable def weakZeroSpec (o : SupportOrbit (0 : Λ)) : WeakZeroSpec :=
  (hasWeakZeroSpec o.out).choose

noncomputable def weakZeroSpec_specifies (o : SupportOrbit (0 : Λ)) :
    (weakZeroSpec o).Specifies o.out :=
  (hasWeakZeroSpec o.out).choose_spec

theorem weakZeroSpec_injective : Function.Injective weakZeroSpec := by
  intro o₁ o₂ h
  have := orbit_eq_of_weakSpec_eq o₁.out o₂.out _
    (weakZeroSpec_specifies o₁) (h ▸ weakZeroSpec_specifies o₂)
  rw [SupportOrbit.eq_mk_of_mem (SupportOrbit.out_mem o₁),
    SupportOrbit.eq_mk_of_mem (SupportOrbit.out_mem o₂), this]

theorem mk_supportOrbit_zero_le' : #(SupportOrbit 0) ≤ #WeakZeroSpec :=
  ⟨⟨weakZeroSpec, weakZeroSpec_injective⟩⟩

def WeakZeroSpec.decompose (W : WeakZeroSpec) :
    κ × (κ → κ) × ZeroSpec :=
  (W.max, W.f, W.σ)

theorem WeakZeroSpec.decompose_injective : Function.Injective WeakZeroSpec.decompose := by
  rintro ⟨m₁, f₁, σ₁⟩ ⟨m₂, f₂, σ₂⟩ h
  cases h
  rfl

theorem mk_supportOrbit_zero_le : #(SupportOrbit 0) < #μ := by
  refine mk_supportOrbit_zero_le'.trans_lt ?_
  refine (mk_le_of_injective WeakZeroSpec.decompose_injective).trans_lt ?_
  simp only [mk_prod, lift_id, mk_pi, prod_const]
  refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le Params.κ_lt_μ
    (mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ mk_zeroSpec)
  rw [Cardinal.power_self_eq Params.κ_isRegular.aleph0_le]
  exact Params.μ_isStrongLimit.2 #κ Params.κ_lt_μ

def zeroExtension' {members : Extensions} : ExtensionalSet.Preference members → Set Atom
  | ExtensionalSet.Preference.base atoms _ => atoms
  | ExtensionalSet.Preference.proper γ _ _ => (not_ltLevel γ).elim

def zeroExtension (t : NewTSet) : Set Atom :=
  zeroExtension' t.val.pref

theorem zeroExtension_injective : Function.Injective zeroExtension := by
  rintro ⟨⟨m₁, p₁⟩, ht₁⟩ ⟨⟨m₂, p₂⟩, ht₂⟩ h
  refine Subtype.coe_injective ?_
  have : m₁ = m₂
  · funext γ hγ
    cases not_ltLevel γ
  cases this
  simp only [ExtensionalSet.mk.injEq, heq_eq_eq, true_and]
  cases p₁
  case proper β _ _ _ =>
    cases not_ltLevel β
  case base atoms _ =>
    cases p₂
    case proper β _ _ _ =>
      cases not_ltLevel β
    case base atoms _ =>
      cases h
      rfl

theorem zeroExtension_smul (t : NewTSet) (ρ : Allowable (0 : Λ)) :
    zeroExtension (ρ • t) = ρ • zeroExtension t := by
  obtain ⟨⟨m, p⟩, ht⟩ := t
  cases p
  case proper β _ _ _ =>
    cases not_ltLevel β
  case base atoms _ =>
    rfl

theorem supports_zeroExtension (S : Support (0 : Λ)) (t : NewTSet)
    (h : Supports (Allowable (0 : Λ)) S.carrier t) :
    Supports (Allowable (0 : Λ)) S.carrier (zeroExtension t) := by
  intro ρ hρ
  rw [← zeroExtension_smul]
  exact congr_arg zeroExtension (h ρ hρ)

theorem mk_supports_disjoint (S : Support (0 : Λ)) (hS : DisjointSupport S.carrier) :
    #{e : Set Atom | MulAction.Supports (Allowable (0 : Λ)) S.carrier e} ≤ 2 ^ #κ := by
  refine (mk_le_of_injective (info_injective S hS)).trans ?_
  simp only [mk_prod, mk_set, lift_id', mk_fintype, Fintype.card_prop, Nat.cast_ofNat, lift_ofNat]
  refine mul_le_of_le le_rfl ?_ ?_
  · refine self_le_power 2 ?_
    exact Cardinal.one_le_aleph0.trans Params.κ_isRegular.aleph0_le
  · exact Params.κ_isRegular.aleph0_le.trans (cantor #κ).le

theorem mk_supports' (S : Support (0 : Λ)) :
    #{e : Set Atom | MulAction.Supports (Allowable (0 : Λ)) S.carrier e} ≤ 2 ^ #κ := by
  have := mk_supports_disjoint
    (Enumeration.ofSet (disjointSupport S.carrier S.small)
      (disjointSupport_small S.carrier S.small)) ?_
  swap
  · rw [Enumeration.ofSet_coe]
    exact disjointSupport_disjointSupport _ _
  refine le_trans ?_ this
  refine mk_subtype_le_of_subset ?_
  intro e he ρ hρ
  refine he ρ ?_
  intro c hc
  refine disjointSupport_supports S.carrier S.small c hc ρ ?_
  intro d hd
  rw [Enumeration.ofSet_coe] at hρ
  exact hρ hd

theorem mk_supports (S : Support (0 : Λ)) :
    #{t : NewTSet | MulAction.Supports (Allowable (0 : Λ)) S.carrier t} ≤ 2 ^ #κ := by
  refine le_trans ?_ (mk_supports' S)
  refine mk_le_of_injective (f := fun t => ⟨zeroExtension t, ?_⟩) ?_
  · exact supports_zeroExtension S t t.prop
  · intro t₁ t₂ h
    exact Subtype.coe_injective (zeroExtension_injective (congr_arg Subtype.val h))

noncomputable def codeSurjection
    (x : (o : SupportOrbit (0 : Λ)) ×
      {t : NewTSet | MulAction.Supports (Allowable (0 : Λ)) o.out.carrier t}) :
    CodingFunction 0 :=
  CodingFunction.code x.1.out x.2 x.2.prop

theorem codeSurjection_surjective : Function.Surjective codeSurjection := by
  intro χ
  obtain ⟨S, hS⟩ := χ.dom_nonempty
  have := (SupportOrbit.mk S).out_mem
  rw [SupportOrbit.mem_mk_iff] at this
  obtain ⟨ρ, hρ⟩ := this
  dsimp only at hρ
  have hS' : (SupportOrbit.mk S).out ∈ χ.decode.Dom
  · have := χ.smul_mem ρ hS
    rwa [hρ] at this
  refine ⟨⟨SupportOrbit.mk S, (χ.decode _).get hS', χ.supports_decode _ _⟩, ?_⟩
  simp only [codeSurjection]
  exact (CodingFunction.eq_code hS').symm

theorem mk_codingFunction_zero_le : #(CodingFunction 0) < #μ := by
  refine (mk_le_of_surjective codeSurjection_surjective).trans_lt ?_
  simp only [coe_zero, coe_setOf, mk_sigma]
  refine (sum_le_sum _ (fun _ => 2 ^ #κ) ?_).trans_lt ?_
  · intro o
    exact mk_supports o.out
  simp only [sum_const, lift_id]
  refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le mk_supportOrbit_zero_le ?_
  exact Params.μ_isStrongLimit.2 _ Params.κ_lt_μ

end ConNF.MainInduction
