import ConNF.Setup.CoherentData

/-!
# Codes

In this file, we define codes and clouds.

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level]

class TypedNearLitters (α : Λ) [ModelData α] [Position (Tangle α)] where
  typed : NearLitter → TSet α
  typed_injective : Function.Injective typed
  pos_le_pos_of_typed (N : NearLitter) (t : Tangle α) : t.set = typed N → pos N ≤ pos t
  smul_typed (ρ : AllPerm α) (N : NearLitter) : ρ • typed N = typed (ρᵁ ↘. • N)

export TypedNearLitters (typed)

class LtData where
  [data : (β : TypeIndex) → [LtLevel β] → ModelData β]
  [positions : (β : TypeIndex) → [LtLevel β] → Position (Tangle β)]
  [typedNearLitters : (β : Λ) → [LtLevel β] → TypedNearLitters β]

instance [LtData] : (β : TypeIndex) → [LtLevel β] → ModelData β :=
  LtData.data

instance [LtData] : (β : TypeIndex) → [LtLevel β] → Position (Tangle β) :=
  LtData.positions

instance [LtData] : (β : Λ) → [LtLevel β] → TypedNearLitters β :=
  LtData.typedNearLitters

variable [LtData]

structure Code : Type u where
  β : TypeIndex
  [hβ : LtLevel β]
  s : Set (TSet β)
  hs : s.Nonempty

instance (c : Code) : LtLevel c.β :=
  c.hβ

theorem cloud_aux (β : TypeIndex) [LtLevel β] (γ : Λ) [LtLevel γ] (hβγ : β ≠ γ)
    (s : Set (TSet β)) (hs : s.Nonempty) :
    (typed '' {N | ∃ t : Tangle β, t.set ∈ s ∧ Nᴸ = fuzz hβγ t} : Set (TSet γ)).Nonempty := by
  obtain ⟨x, hx⟩ := hs
  rw [Set.image_nonempty]
  obtain ⟨S, hS⟩ := exists_support x
  exact ⟨(fuzz hβγ ⟨x, S, hS⟩)ᴺ, ⟨x, S, hS⟩, hx, rfl⟩

inductive Cloud : Rel Code Code
  | mk (β : TypeIndex) [LtLevel β] (γ : Λ) [LtLevel γ] (hβγ : β ≠ γ)
      (s : Set (TSet β)) (hs : s.Nonempty) :
      Cloud
        ⟨β, s, hs⟩
        ⟨γ, typed '' {N | ∃ t : Tangle β, t.set ∈ s ∧ Nᴸ = fuzz hβγ t}, cloud_aux β γ hβγ s hs⟩

theorem eq_coe_of_cloud {c d : Code} (h : Cloud c d) :
    ∃ (γ : Λ) (_ : LtLevel γ) (s : Set (TSet γ)) (hs : s.Nonempty), d = ⟨γ, s, hs⟩ := by
  obtain ⟨⟩ := h
  exact ⟨_, _, _, _, rfl⟩

theorem cloud_mk_iff (c : Code) (γ : Λ) [LtLevel γ] (s : Set (TSet γ)) (hs : s.Nonempty) :
    Cloud c ⟨γ, s, hs⟩ ↔ ∃ hβγ : c.β ≠ γ,
      s = typed '' {N | ∃ t : Tangle c.β, t.set ∈ c.s ∧ Nᴸ = fuzz hβγ t} := by
  constructor
  · rintro ⟨⟩
    exact ⟨_, rfl⟩
  · rintro ⟨hβγ, rfl⟩
    exact .mk c.β γ hβγ c.s c.hs

theorem subset_of_cloud {β : TypeIndex} {γ : Λ} [LtLevel β] [LtLevel γ]
    {hβγ : β ≠ γ} {s₁ s₂ : Set (TSet β)}
    (h : {N : NearLitter | ∃ t : Tangle β, t.set ∈ s₁ ∧ Nᴸ = fuzz hβγ t} =
      {N | ∃ t : Tangle β, t.set ∈ s₂ ∧ Nᴸ = fuzz hβγ t}) :
    s₁ ⊆ s₂ := by
  intro x hx
  obtain ⟨S, hS⟩ := exists_support x
  have : (fuzz hβγ ⟨x, S, hS⟩)ᴺ ∈
      {N : NearLitter | ∃ t : Tangle β, t.set ∈ s₁ ∧ Nᴸ = fuzz hβγ t} :=
    ⟨⟨x, S, hS⟩, hx, rfl⟩
  rw [h] at this
  obtain ⟨t, ht, htN⟩ := this
  cases fuzz_injective htN
  exact ht

theorem cloud_injective : Cloud.Injective := by
  constructor
  rintro ⟨β, s, hs⟩ ⟨γ, t, ht⟩ d h₁ h₂
  obtain ⟨δ, _, u, hu, rfl⟩ := eq_coe_of_cloud h₁
  rw [cloud_mk_iff] at h₁ h₂
  obtain ⟨hβδ, rfl⟩ := h₁
  obtain ⟨hγδ, h⟩ := h₂
  have h' := TypedNearLitters.typed_injective.image_injective h
  have : β = γ := by
    rw [Set.image_nonempty] at hu
    obtain ⟨x, hx⟩ := hu
    have hy := hx
    rw [h'] at hy
    obtain ⟨t₁, -, hN₁⟩ := hx
    obtain ⟨t₂, -, hN₂⟩ := hy
    exact fuzz_β_eq (hN₁.symm.trans hN₂)
  cases this
  simp only [Code.mk.injEq, heq_eq_eq, true_and]
  apply subset_antisymm
  · exact subset_of_cloud h'
  · exact subset_of_cloud h'.symm

def Code.positions (c : Code) : Set μ :=
  pos '' {t : Tangle c.β | t.set ∈ c.s}

theorem Code.positions_nonempty (c : Code) : c.positions.Nonempty := by
  obtain ⟨x, hx⟩ := c.hs
  obtain ⟨S, hS⟩ := exists_support x
  exact ⟨_, ⟨x, S, hS⟩, hx, rfl⟩

theorem Code.positions_lt_of_cloud {c d : Code} (h : Cloud c d) :
    ∀ ν₂ ∈ d.positions, ∃ ν₁ ∈ c.positions, ν₁ < ν₂ := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨β, γ, hβγ, s, hs⟩ := h
  obtain ⟨N, ⟨v, hv, hvN⟩, hu⟩ := ht
  refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
  apply (pos_fuzz hβγ v).trans_le
  rw [← hvN]
  apply (NearLitter.pos_litter_lt_pos N).le.trans
  exact TypedNearLitters.pos_le_pos_of_typed N t hu.symm

def Code.pos (c : Code) : μ :=
  WellFounded.min (inferInstanceAs (WellFoundedLT μ)).wf
    c.positions c.positions_nonempty

theorem Code.cloud_subrelation : Subrelation Cloud (InvImage (· < ·) pos) := by
  intro c d h
  have := positions_lt_of_cloud h d.pos (WellFounded.min_mem _ _ _)
  obtain ⟨ν, hν₁, hν₂⟩ := this
  rw [InvImage]
  have := WellFounded.not_lt_min (inferInstanceAs (WellFoundedLT μ)).wf
    c.positions c.positions_nonempty hν₁
  rw [← not_le]
  contrapose! this
  exact hν₂.trans_le this

theorem cloud_wf : WellFounded Cloud := by
  apply Code.cloud_subrelation.wf
  apply InvImage.wf
  exact (inferInstanceAs (WellFoundedLT μ)).wf

theorem eq_of_cloud {c : Code} {γ : TypeIndex} [LtLevel γ]
    {s t : Set (TSet γ)} {hs : s.Nonempty} {ht : t.Nonempty}
    (hcs : Cloud c ⟨γ, s, hs⟩) (hct : Cloud c ⟨γ, t, ht⟩) :
    s = t := by
  cases hcs
  cases hct
  rfl

mutual
  @[mk_iff]
  inductive Code.Even : Code → Prop
    | mk (c : Code) : (∀ d, Cloud d c → d.Odd) → c.Even

  @[mk_iff]
  inductive Code.Odd : Code → Prop
    | mk (c d : Code) : Cloud d c → d.Even → c.Odd
end

theorem not_even_and_odd (c : Code) : ¬(c.Even ∧ c.Odd) := by
  induction c using cloud_wf.induction
  case h c ih =>
    intro hc
    obtain ⟨⟨_, hc⟩, ⟨_, d, hdc, hd⟩⟩ := hc
    exact ih d hdc ⟨hd, hc d hdc⟩

theorem even_or_odd (c : Code) : c.Even ∨ c.Odd := by
  induction c using cloud_wf.induction
  case h c ih =>
    by_cases h' : ∀ d, Cloud d c → d.Odd
    · left
      exact .mk c h'
    · right
      push_neg at h'
      obtain ⟨d, hd₁, hd₂⟩ := h'
      obtain (hd | hd) := ih d hd₁
      · exact .mk c d hd₁ hd
      · cases hd₂ hd

@[simp]
theorem not_even (c : Code) : ¬c.Even ↔ c.Odd := by
  have := even_or_odd c
  have := not_even_and_odd c
  tauto

@[simp]
theorem not_odd (c : Code) : ¬c.Odd ↔ c.Even := by
  have := not_even c
  tauto

inductive Represents : Rel Code Code
  | refl (c : Code) : c.Even → Represents c c
  | cloud (c d : Code) : c.Even → Cloud c d → Represents c d

theorem represents_injective : Represents.Injective := by
  constructor
  rintro c₁ c₂ d (⟨_, hc₁⟩ | ⟨_, _, hc₁, hc₁d⟩) (⟨_, hc₂⟩ | ⟨_, _, hc₂, hc₂d⟩)
  · rfl
  · cases not_even_and_odd c₁ ⟨hc₁, c₁, c₂, hc₂d, hc₂⟩
  · cases not_even_and_odd c₂ ⟨hc₂, c₂, c₁, hc₁d, hc₁⟩
  · exact cloud_injective.injective hc₁d hc₂d

theorem represents_surjective : Represents.Surjective := by
  constructor
  intro c
  obtain (hc | ⟨_, d, hdc, hd⟩) := even_or_odd c
  · exact ⟨c, .refl c hc⟩
  · exact ⟨d, .cloud d c hd hdc⟩

theorem represents_cofunctional : Represents.Cofunctional :=
  ⟨represents_injective, represents_surjective⟩

theorem eq_of_represents {c : Code} {γ : TypeIndex} [LtLevel γ]
    {s t : Set (TSet γ)} {hs : s.Nonempty} {ht : t.Nonempty}
    (hcs : Represents c ⟨γ, s, hs⟩) (hct : Represents c ⟨γ, t, ht⟩) :
    s = t := by
  obtain (⟨_, hc⟩ | ⟨_, _, hc, hcs⟩) := hcs <;>
  obtain (⟨_, _⟩ | ⟨_, _, _, hct⟩) := hct
  · rfl
  · obtain ⟨_, γ, hβγ, _, _⟩ := hct
    cases hβγ rfl
  · obtain ⟨_, γ, hβγ, _, _⟩ := hcs
    cases hβγ rfl
  · exact eq_of_cloud hcs hct

theorem exists_represents {c : Code} (hc : c.Even) (γ : Λ) [LtLevel γ] :
    ∃ (s : Set (TSet γ)) (hs : s.Nonempty), Represents c ⟨γ, s, hs⟩ := by
  by_cases hβγ : c.β = γ
  · obtain ⟨β, s, hs⟩ := c
    cases hβγ
    exact ⟨s, hs, .refl ⟨γ, s, hs⟩ hc⟩
  · exact ⟨_, _, .cloud c _ hc (.mk c.β γ hβγ c.s c.hs)⟩

def Code.members (c : Code) (β : TypeIndex) [LtLevel β] : Set (TSet β) :=
  {x | ∃ (s : Set (TSet β)) (hs : s.Nonempty), x ∈ s ∧ Represents c ⟨β, s, hs⟩}

theorem Code.members_eq_of_represents {c : Code} {β : TypeIndex} [LtLevel β]
    {s : Set (TSet β)} {hs : s.Nonempty} (hc : Represents c ⟨β, s, hs⟩) :
    c.members β = s := by
  apply subset_antisymm
  · rintro x ⟨t, ht, hxt, hct⟩
    cases eq_of_represents hc hct
    exact hxt
  · intro x hx
    exact ⟨s, hs, hx, hc⟩

theorem Code.members_nonempty {c : Code} (hc : c.Even) (β : Λ) [LtLevel β] :
    (c.members β).Nonempty := by
  obtain ⟨s, ⟨x, hx⟩, hc⟩ := exists_represents hc β
  exact ⟨x, s, ⟨x, hx⟩, hx, hc⟩

theorem Code.ext {c d : Code} (hc : c.Even) (hd : d.Even) (β : Λ) [LtLevel β]
    (h : c.members β = d.members β) : c = d := by
  obtain ⟨x, s, hs, hxs, hcs⟩ := members_nonempty hc β
  obtain ⟨y, t, ht, hyt, hdt⟩ := members_nonempty hd β
  have hs' := members_eq_of_represents hcs
  have ht' := members_eq_of_represents hdt
  rw [hs', ht'] at h
  cases h
  exact represents_cofunctional.injective hcs hdt

theorem Code.eq_of_isMin (c : Code) (hα : IsMin α) :
    ∃ s hs, c = ⟨⊥, s, hs⟩ := by
  obtain ⟨β, s, hs⟩ := c
  cases β using WithBot.recBotCoe
  case bot => exact ⟨s, hs, rfl⟩
  case coe β hβ => cases hα.not_lt (WithBot.coe_lt_coe.mp hβ.elim)

theorem Code.bot_even (s : Set (TSet ⊥)) (hs : s.Nonempty) :
    (Code.mk ⊥ s hs).Even := by
  constructor
  rintro _ ⟨⟩

theorem Code.members_bot (s : Set (TSet ⊥)) (hs : s.Nonempty) :
    (Code.mk ⊥ s hs).members ⊥ = s := by
  ext x : 1
  constructor
  · rintro ⟨t, ht, hxt, ⟨⟩ | ⟨_, _, _, _, _⟩⟩
    exact hxt
  · intro hx
    exact ⟨s, hs, hx, .refl _ (bot_even s hs)⟩

theorem Code.ext' {c d : Code} (hc : c.Even) (hd : d.Even)
    (h : ∀ (β : TypeIndex) [LtLevel β], c.members β = d.members β) :
    c = d := by
  by_cases hα : IsMin α
  · obtain ⟨s, hs, rfl⟩ := c.eq_of_isMin hα
    obtain ⟨t, ht, rfl⟩ := d.eq_of_isMin hα
    have := h ⊥
    rw [members_bot, members_bot] at this
    cases this
    rfl
  · rw [not_isMin_iff] at hα
    obtain ⟨β, hβ⟩ := hα
    have : LtLevel β := ⟨WithBot.coe_lt_coe.mpr hβ⟩
    apply ext hc hd β
    exact h β

end ConNF
