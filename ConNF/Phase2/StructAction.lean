import ConNF.Phase2.Flexible
import ConNF.Phase2.NearLitterAction

#align_import phase2.struct_action

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Structural actions
-/


/-- A `β`-structural action is a product that assigns a near-litter action to each `β`-extended
index. -/
def StructAction (β : TypeIndex) :=
  ExtendedIndex β → NearLitterAction

namespace StructAction

def Lawful {β : TypeIndex} (φ : StructAction β) : Prop :=
  ∀ B, (φ B).Lawful

/-- This structural action maps flexible litters to flexible litters. -/
def MapFlexible {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iio α} (φ : StructAction β) :
    Prop :=
  ∀ (L : Litter) (B hL), Flexible α L B → Flexible α (((φ B).litterMap L).get hL).1 B

section Precise

def Precise {β : TypeIndex} (φ : StructAction β) : Prop :=
  ∀ B, (φ B).Precise

variable {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iio α} (φ : StructAction β)

noncomputable def complete (hφ : φ.Lawful) : StructApprox β := fun B => (φ B).complete (hφ B) B

theorem complete_apply (hφ : φ.Lawful) (B : ExtendedIndex β) :
    φ.complete hφ B = (φ B).complete (hφ B) B :=
  rfl

theorem smul_atom_eq {hφ : φ.Lawful} {π : StructPerm β} (hπ : (φ.complete hφ).ExactlyApproximates π)
    {a : Atom} {B : ExtendedIndex β} (ha : ((φ B).atomMap a).Dom) :
    StructPerm.derivative B π • a = ((φ B).atomMap a).get ha :=
  by
  have := (φ B).smul_atom_eq (hπ B) ha
  rw [StructPerm.of_bot_smul] at this
  exact this

theorem smul_toNearLitter_eq_of_precise {hφ : φ.Lawful} (hφp : φ.Precise) {π : StructPerm β}
    (hπ : (φ.complete hφ).ExactlyApproximates π) {L : Litter} {B : ExtendedIndex β}
    (hL : ((φ B).litterMap L).Dom)
    (hπL : StructPerm.derivative B π • L = (((φ B).litterMap L).get hL).1) :
    StructPerm.derivative B π • L.toNearLitter = ((φ B).litterMap L).get hL :=
  by
  have := (φ B).smul_toNearLitter_eq_of_preciseAt (hπ B) hL (hφp B hL) _
  · rw [StructPerm.of_bot_smul] at this
    exact this
  · rw [StructPerm.of_bot_smul]
    exact hπL

theorem smul_nearLitter_eq_of_precise {hφ : φ.Lawful} (hφp : φ.Precise) {π : StructPerm β}
    (hπ : (φ.complete hφ).ExactlyApproximates π) {N : NearLitter} {B : ExtendedIndex β}
    (hN : ((φ B).litterMap N.1).Dom)
    (hπL : StructPerm.derivative B π • N.1 = (((φ B).litterMap N.1).get hN).1) :
    ((StructPerm.derivative B π • N : NearLitter) : Set Atom) =
      ((φ B).litterMap N.1).get hN ∆ (StructPerm.derivative B π • litterSet N.1 ∆ N) :=
  by
  have := (φ B).smul_nearLitter_eq_of_preciseAt (hπ B) hN (hφp B hN) _
  · rw [StructPerm.of_bot_smul] at this
    exact this
  · rw [StructPerm.of_bot_smul]
    exact hπL

end Precise

variable {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iio α}

/-- A structural action *supports* a tangle if it defines an image for everything
in the reduction of its designated support. -/
structure Supports (φ : StructAction β) (t : Tangle β) : Prop where
  atom_mem : ∀ a B, (inl a, B) ∈ reducedSupport α t → ((φ B).atomMap a).Dom
  litter_mem :
    ∀ (L : Litter) (B), (inr L.toNearLitter, B) ∈ reducedSupport α t → ((φ B).litterMap L).Dom

/-- Two structural actions are *compatible* for a tangle if they both support the
tangle and agree on the reduction of its designated support. -/
structure Compatible (φ ψ : StructAction β) (t : Tangle β) : Prop where
  φSupports : φ.Supports t
  ψSupports : ψ.Supports t
  atomMap :
    ∀ a B ha,
      ((φ B).atomMap a).get (φ_supports.atom_mem a B ha) =
        ((ψ B).atomMap a).get (ψ_supports.atom_mem a B ha)
  litterMap :
    ∀ L B hL,
      ((φ B).litterMap L).get (φ_supports.litter_mem L B hL) =
        ((ψ B).litterMap L).get (ψ_supports.litter_mem L B hL)

/-- The action of a structural action on support conditions. -/
noncomputable def supportConditionMapOrElse (φ : StructAction β) :
    SupportCondition β → SupportCondition β
  | (inl a, B) => (inl ((φ B).atomMapOrElse a), B)
  | (inr N, B) => (inr ((φ B).nearLitterMapOrElse N), B)

def CoherentCoe (φ : StructAction β) (hφ : φ.Lawful) (t : Tangle β) : Prop :=
  ∀ ⦃π : Allowable β⦄ (hπ : (φ.complete hφ).ExactlyApproximates π.toStructPerm) (γ : Iic α)
    (δ ε : Iio α) (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε) (C : Path (β : TypeIndex) γ)
    (t' : Tangle δ) (hL)
    (hc₁ :
      ∃ d : SupportCondition β,
        d ∈ (designatedSupport t).carrier ∧
          (inr (fMap (coe_ne_coe.mpr (coe_ne' hδε)) t').toNearLitter,
              (C.cons (coe_lt hε)).cons (bot_lt_coe _)) ≤[α]
            d)
    (hc₂ :
      ∀ c : SupportCondition δ,
        c ∈ (designatedSupport t').carrier →
          (π • show SupportCondition β from (c.fst, (C.cons (coe_lt hδ)).comp c.snd)) =
            φ.supportConditionMapOrElse (c.fst, (C.cons (coe_lt hδ)).comp c.snd)),
    fMap (Subtype.coe_injective.Ne (Iio.coe_injective.Ne hδε))
        (show Tangle δ from
          (show Allowable δ from
              allowableDerivative (γ : IicBot α) δ (coe_lt_coe.mpr hδ)
                (Allowable.derivative
                  (show Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from C) π)) •
            t') =
      (((φ ((C.cons (coe_lt hε)).cons (bot_lt_coe _))).litterMap
              (fMap (Subtype.coe_injective.Ne (Iio.coe_injective.Ne hδε)) t')).get
          hL).fst

def CoherentBot (φ : StructAction β) (hφ : φ.Lawful) : Prop :=
  ∀ ⦃π : Allowable β⦄ (hπ : (φ.complete hφ).ExactlyApproximates π.toStructPerm) (γ : Iic α)
    (ε : Iio α) (hε : (ε : Λ) < γ) (C : Path (β : TypeIndex) γ) (a : Tangle ⊥) (hL)
    (hc :
      StructPerm.derivative (C.cons (bot_lt_coe _)) π.toStructPerm • a =
        (φ (C.cons (bot_lt_coe _))).atomMapOrElse a),
    fMap
        (show ((⊥ : IioBot α) : TypeIndex) ≠ (ε : IioBot α) from
          Subtype.coe_injective.Ne IioBot.bot_ne_coe)
        ((show Allowable (⊥ : IioBot α) from
            (Allowable.derivative
                (show Path ((β : IicBot α) : TypeIndex) (⊥ : IicBot α) from
                  C.cons (bot_lt_coe _)))
              π) •
          a) =
      (((φ ((C.cons (coe_lt hε)).cons (bot_lt_coe _))).litterMap
              (fMap (show (⊥ : TypeIndex) ≠ (ε : Λ) from bot_ne_coe) a)).get
          hL).fst

@[mk_iff]
structure Coherent (φ : StructAction β) (hφ : φ.Lawful) (t : Tangle β) : Prop where
  coe : φ.CoherentCoe hφ t
  bot : φ.CoherentBot hφ

theorem smul_litter_eq_of_supports (φ : StructAction β) (hφ : φ.Lawful) {π : Allowable β}
    (hπ : (φ.complete hφ).ExactlyApproximates π.toStructPerm) (t : Tangle β) (hφc : φ.Coherent hφ t)
    (hφs : φ.Supports t) (d : SupportCondition β) (hd : d ∈ designatedSupport t)
    (B : ExtendedIndex β) (L : Litter)
    (ih :
      ∀ e : SupportCondition β,
        e <[α] (inr L.toNearLitter, B) → π • e = φ.supportConditionMapOrElse e)
    (hc : (inr L.toNearLitter, B) ≤[α] d) :
    StructPerm.derivative B π.toStructPerm • L =
      (((φ B).litterMap L).get
          (hφs.litter_mem L B ⟨⟨d, hd, reflTransGen_nearLitter hc⟩, Reduced.mk_litter _ _⟩)).fst :=
  by
  by_cases hflex : inflexible α L B
  · rw [inflexible_iff] at hflex
    obtain ⟨γ, δ, ε, hδ, hε, hδε, C, t', rfl, rfl⟩ | ⟨γ, ε, hε, C, a, rfl, rfl⟩ := hflex
    · have hc₂ := fun c hc =>
        ih _ (Relation.TransGen.single <| constrains.fMap hδ hε hδε C t' c hc)
      have :=
        smul_fMap (δ : Iio_index α) ε _ _ (Iio.coe_injective.ne hδε)
          (allowable.derivative
            (show Path ((β : Iic_index α) : type_index) (γ : Iic_index α) from C) π)
          t'
      rw [← allowable.derivative_cons_apply, allowable.derivative_smul, ←
        StructPerm.derivative_bot_smul, ← StructPerm.derivative_cons] at this
      exact this.trans (hφc.coe hπ γ δ ε hδ hε hδε C t' _ ⟨d, hd, hc⟩ hc₂)
    · have hc : (_, _) = (_, _) := ih _ (Relation.TransGen.single <| constrains.fMap_bot hε C a)
      simp only [smul_inl, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff] at hc
      rw [← hφc.bot hπ γ ε hε C a _ hc]
      have :=
        smul_fMap (⊥ : Iio_index α) ε _ _ (by intro h <;> cases h)
          (allowable.derivative
            (show Path ((β : Iic_index α) : type_index) (γ : Iic_index α) from C) π)
          a
      rw [← allowable.derivative_cons_apply, allowable.derivative_smul, ←
        StructPerm.derivative_bot_smul, ← StructPerm.derivative_cons, ←
        allowable.derivative_cons_apply] at this
      exact this
  · have := hφs.litter_mem L B ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩
    rw [← StructPerm.of_bot_smul, ← (hπ B).map_litter _ (Or.inl (Or.inl ⟨this, hflex⟩))]
    refine' ((φ B).complete_smul_litter_eq L).trans _
    rw [near_litter_action.flexible_litter_perm_apply_eq, (φ B).roughLitterMapOrElse_of_dom]
    exact this
    exact hflex

theorem smul_supportCondition_eq (φ : StructAction β) (hφ : φ.Lawful) (hφp : φ.Precise)
    {π : Allowable β} (hπ : (φ.complete hφ).ExactlyApproximates π.toStructPerm) (t : Tangle β)
    (hwc : φ.Coherent hφ t) (hws : φ.Supports t) (c d : SupportCondition β) (hc : c ≤[α] d)
    (hd : d ∈ designatedSupport t) : π • c = φ.supportConditionMapOrElse c :=
  by
  revert d
  refine' (constrains_wf α β).TransGen.induction c _
  rintro c ih d hc hd
  obtain ⟨a | N, B⟩ := c
  · refine' Prod.ext _ rfl
    change inl _ = inl _
    refine' congr_arg inl _
    rw [φ.smul_atom_eq hπ (hws.atom_mem a B ⟨⟨d, hd, hc⟩, reduced.mk_atom a B⟩),
      near_litter_action.atom_map_or_else_of_dom]
  refine' Prod.ext _ rfl
  change inr _ = inr _
  refine' congr_arg inr (SetLike.coe_injective _)
  have ih' := fun e he => ih e (Relation.TransGen.single he) d (Relation.ReflTransGen.head he hc) hd
  rw [φ.smul_near_litter_eq_of_precise hφp hπ (hws.litter_mem N.1 B _) _]
  · simp only [near_litter_action.near_litter_map_or_else, near_litter.coe_mk, Subtype.coe_mk]
    rw [(φ B).litterMapOrElse_of_dom (hws.litter_mem N.1 B _)]
    congr 1
    ext a : 1
    rw [mem_smul_set, mem_image]
    constructor
    · rintro ⟨b, hb₁, hb₂⟩
      have : (_, _) = (_, _) := ih' _ (constrains.symm_diff N _ hb₁ B)
      simp only [smul_inl, smul_inv_smul, Prod.mk.inj_iff] at this
      rw [this.1] at hb₂
      exact ⟨b, hb₁, hb₂⟩
    · rintro ⟨b, hb₁, hb₂⟩
      have : (_, _) = (_, _) := ih' _ (constrains.symm_diff N _ hb₁ B)
      simp only [smul_inl, smul_inv_smul, Prod.mk.inj_iff] at this
      rw [← this.1] at hb₂
      exact ⟨b, hb₁, hb₂⟩
    · exact ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩
  refine' φ.smul_litter_eq_of_supports hφ hπ t hwc hws d hd B N.1 _ (refl_trans_gen_near_litter hc)
  exact fun e he =>
    ih e (trans_gen_near_litter he) d
      (Relation.ReflTransGen.trans he.to_reflTransGen (refl_trans_gen_near_litter hc)) hd

theorem smul_eq_smul_tangle (φ ψ : StructAction β) (hφ : φ.Lawful) (hψ : ψ.Lawful) (hφp : φ.Precise)
    (hψp : ψ.Precise) (t : Tangle β) (h : Compatible φ ψ t) (hφc : φ.Coherent hφ t)
    (hψc : ψ.Coherent hψ t) {πφ πψ : Allowable β}
    (hπφ : (φ.complete hφ).ExactlyApproximates πφ.toStructPerm)
    (hπψ : (ψ.complete hψ).ExactlyApproximates πψ.toStructPerm) : πφ • t = πψ • t :=
  by
  rw [smul_eq_iff_eq_inv_smul, smul_smul]
  symm
  refine' (designated_support t).Supports _ _
  intro c hc
  rw [mul_smul, inv_smul_eq_iff]
  symm
  rw [smul_support_condition_eq φ hφ hφp hπφ t hφc h.φ_supports c c Relation.ReflTransGen.refl hc]
  rw [smul_support_condition_eq ψ hψ hψp hπψ t hψc h.ψ_supports c c Relation.ReflTransGen.refl hc]
  obtain ⟨a | N, B⟩ := c
  · simp only [support_condition_map_or_else, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff]
    rw [(φ B).atomMapOrElse_of_dom, (ψ B).atomMapOrElse_of_dom]
    refine' h.atom_map a B _
    exact ⟨⟨_, hc, Relation.ReflTransGen.refl⟩, reduced.mk_atom _ _⟩
  · simp only [support_condition_map_or_else, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff,
      near_litter_action.near_litter_map_or_else]
    refine' SetLike.coe_injective _
    simp only [near_litter.coe_mk, Subtype.coe_mk]
    congr 1
    · rw [(φ B).litterMapOrElse_of_dom, (ψ B).litterMapOrElse_of_dom, h.litter_map N.1 B _]
      exact ⟨⟨_, hc, refl_trans_gen_near_litter Relation.ReflTransGen.refl⟩, reduced.mk_litter _ _⟩
    · ext a : 1
      rw [mem_image, mem_image]
      constructor <;> rintro ⟨b, hb₁, hb₂⟩ <;> refine' ⟨b, hb₁, _⟩ <;>
        rw [← hb₂, (φ B).atomMapOrElse_of_dom, (ψ B).atomMapOrElse_of_dom]
      · refine' (h.atom_map b B _).symm
        exact
          ⟨⟨_, hc, Relation.ReflTransGen.single (constrains.symm_diff N b hb₁ B)⟩,
            reduced.mk_atom _ _⟩
      · refine' h.atom_map b B _
        exact
          ⟨⟨_, hc, Relation.ReflTransGen.single (constrains.symm_diff N b hb₁ B)⟩,
            reduced.mk_atom _ _⟩

instance {β : TypeIndex} : PartialOrder (StructAction β)
    where
  le φ ψ := ∀ B, φ B ≤ ψ B
  le_refl φ B := le_rfl
  le_trans φ ψ χ h₁ h₂ B := (h₁ B).trans (h₂ B)
  le_antisymm φ ψ h₁ h₂ := funext fun B => le_antisymm (h₁ B) (h₂ B)

theorem Lawful.le {β : TypeIndex} {φ ψ : StructAction β} (h : φ.Lawful) (hψ : ψ ≤ φ) : ψ.Lawful :=
  fun B => (h B).le (hψ B)

def comp {β γ : TypeIndex} (φ : StructAction β) (A : Path β γ) : StructAction γ := fun B =>
  { atomMap := (φ (A.comp B)).atomMap
    litterMap := (φ (A.comp B)).litterMap
    atomMap_dom_small :=
      by
      refine' small.image_subset id Function.injective_id (φ (A.comp B)).atomMap_dom_small _
      simp only [id.def, image_id']
    litterMap_dom_small :=
      by
      refine' small.image_subset id Function.injective_id (φ (A.comp B)).litterMap_dom_small _
      simp only [id.def, image_id'] }

@[simp]
theorem comp_apply {β γ : TypeIndex} {φ : StructAction β} {A : Path β γ} {B : ExtendedIndex γ} :
    φ.comp A B = φ (A.comp B) := by ext : 1 <;> rfl

theorem comp_comp {β γ δ : TypeIndex} {φ : StructAction β} {A : Path β γ} {B : Path γ δ} :
    (φ.comp A).comp B = φ.comp (A.comp B) := by
  ext : 2
  simp only [comp_apply, path.comp_assoc]
  simp only [comp_apply, path.comp_assoc]

theorem le_comp {β γ : TypeIndex} {φ ψ : StructAction β} (h : φ ≤ ψ) (A : Path β γ) :
    φ.comp A ≤ ψ.comp A := fun B => h (A.comp B)

theorem Lawful.comp {β γ : TypeIndex} {φ : StructAction β} (h : φ.Lawful) (A : Path β γ) :
    Lawful (φ.comp A) := fun B =>
  { atomMap_injective := (h (A.comp B)).atomMap_injective
    litterMap_injective := (h (A.comp B)).litterMap_injective
    atom_mem := (h (A.comp B)).atom_mem }

end StructAction

end ConNF
