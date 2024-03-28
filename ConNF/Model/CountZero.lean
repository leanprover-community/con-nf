import ConNF.Mathlib.PFun
import ConNF.NewTangle
import ConNF.FOA
import ConNF.Counting.CodingFunction
import ConNF.Counting.SupportOrbit

open Cardinal Function MulAction Set Sum Quiver WithBot

open scoped Cardinal symmDiff

universe u

namespace ConNF.Construction

variable [Params.{u}] [BasePositions]

local instance : Level := ⟨0⟩

theorem zeroTangleData_subsingleton
    (i₁ j₁ : TangleDataLt)
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
      toPretangle := ⟨NewTSet.toPretangle, NewTSet.toPretangle_injective⟩
      toPretangle_smul := NewTSet.toPretangle_smul
    } : TangleData (0 : Λ)) =
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
      toPretangle := ⟨NewTSet.toPretangle, NewTSet.toPretangle_injective⟩
      toPretangle_smul := NewTSet.toPretangle_smul
    }) := by
  have : i₁ = j₁
  · refine TangleDataLt.ext _ _ ?_
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

local instance : TangleDataLt :=
  ⟨fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim⟩
local instance : PositionedTanglesLt :=
  ⟨fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim⟩
local instance : TypedObjectsLt :=
  fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim
local instance : PositionedObjectsLt :=
  fun β i => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp i.elim)).elim

local instance zeroTangleData : TangleData (0 : Λ) :=
  {
    TSet := NewTSet
    Allowable := NewAllowable
    allowableToStructPerm := NewAllowable.toStructPerm
    allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
    has_support := by
      intro t
      obtain ⟨S, hS⟩ := t.prop
      exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
    toPretangle := ⟨NewTSet.toPretangle, NewTSet.toPretangle_injective⟩
    toPretangle_smul := NewTSet.toPretangle_smul
  }

local instance zeroTypedObjects : TypedObjects (0 : Λ) :=
  {
    typedAtom := ⟨newTypedAtom, newTypedAtom_injective⟩
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
    · simp only [not_lt_none] at h
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
  · simp only [not_lt_none] at h
  cases eq_zero_of_leLevel β
  cases' γ with γ
  · exact ⟨rfl, rfl⟩
  · cases (Params.Λ_zero_le γ).not_lt (coe_lt_coe.mp h)

def toSemiallowable (π : NearLitterPerm) : SemiallowablePerm :=
  fun β _ => eq_bot_of_ltLevel β ▸ (show Allowable ⊥ from π)

theorem toSemiallowable_allowable (π : NearLitterPerm) :
    (toSemiallowable π).IsAllowable := by
  intro β _ γ _ hβγ
  cases eq_bot_of_ltLevel β
  cases eq_bot_of_ltLevel γ

def toAllowable (π : NearLitterPerm) : NewAllowable :=
  ⟨toSemiallowable π, toSemiallowable_allowable π⟩

def zeroDerivative : NewAllowable →* NearLitterPerm :=
  ⟨⟨fun ρ => ρ.val ⊥,
    by simp only [NewAllowable.coe_one, SemiallowablePerm.one_apply]⟩,
    by simp only [NewAllowable.coe_mul, SemiallowablePerm.mul_apply, forall_const]⟩

section FOA

local instance : FOAData where
  lowerTangleData β _ := eq_zero_of_leLevel β ▸ zeroTangleData
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

def toStructBehaviour (ξ : NearLitterBehaviour) : StructBehaviour 0 :=
  fun _ => ξ

theorem toStructBehaviour_coherentDom (ξ : NearLitterBehaviour) :
    (toStructBehaviour ξ).CoherentDom := by
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

theorem toStructBehaviour_coherent (ξ : NearLitterBehaviour) :
    (toStructBehaviour ξ).Coherent := by
  constructor
  case toCoherentDom =>
    exact toStructBehaviour_coherentDom ξ
  case coherent_coe =>
    intro γ _ A δ _
    cases not_ltLevel δ
  case coherent_bot =>
    intro γ _ A δ _
    cases not_ltLevel δ

/-- An instance of the freedom of action theorem for type zero. -/
theorem zero_foa (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    ∃ π : NearLitterPerm, ξ.Approximates π := by
  have := (toStructBehaviour ξ).freedom_of_action ?_ (toStructBehaviour_coherent ξ)
  · obtain ⟨ρ, hρ⟩ := this
    exact ⟨ρ.val ⊥, hρ zeroPath⟩
  · intro
    exact hξ

end FOA

def ZeroStrong (S : Support 0) : Prop :=
  ∀ a N₁ N₂, ⟨zeroPath, inr N₁⟩ ∈ S → ⟨zeroPath, inr N₂⟩ ∈ S → Support.Interferes a N₁ N₂ →
    ⟨zeroPath, inl a⟩ ∈ S

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

noncomputable def convert : NearLitterBehaviour :=
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

theorem mk_supportOrbit_zero_le : #(SupportOrbit 0) < #μ := sorry

theorem mk_codingFunction_zero_le : #(CodingFunction 0) < #μ := sorry

end ConNF.Construction
