import ConNF.NewTangle
import ConNF.Counting.Hypotheses

open Cardinal Function MulAction Set Sum Quiver WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] [BasePositions] [Level]
  [TangleDataLt] [PositionedTanglesLt] [TypedObjectsLt] [PositionedObjectsLt]

def Semitangle.toPretangle (t : Semitangle)
  (lower : ∀ (β : TypeIndex) [LtLevel β], Tangle β → Pretangle β) : Pretangle α :=
  Pretangle.ofCoe.symm
    (fun β hβ => match β with
      | ⊥ => {a | ∃ s : Set Atom, ∃ h, t.pref = Preference.base s h ∧ a ∈ s}
      | (β : Λ) => letI : LtLevel β := ⟨hβ⟩; {p | ∃ s ∈ t.members β, lower β s = p})

def NewTangle.toPretangle (t : NewTangle)
  (lower : ∀ (β : TypeIndex) [LtLevel β], Tangle β → Pretangle β) : Pretangle α :=
  t.t.toPretangle lower

theorem Semitangle.toPretangle_smul (ρ : NewAllowable) (t : Semitangle)
    (lower : ∀ (β : TypeIndex) [LtLevel β], Tangle β → Pretangle β)
    (h : ∀ (β : TypeIndex) [LtLevel β] (ρ' : Allowable β) (t' : Tangle β),
      ρ' • lower β t' = lower β (ρ' • t')) :
    ρ • t.toPretangle lower = (ρ • t).toPretangle lower := by
  rw [← Pretangle.ofCoe_inj, toPretangle, toPretangle]
  rw [Equiv.apply_symm_apply]
  ext β hβ : 2
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    rw [← NewAllowable.coe_smul]
    erw [StructPerm.ofCoe_smul]
    rw [Equiv.apply_symm_apply]
    dsimp only
    ext a : 1
    rw [mem_smul_set_iff_inv_smul_mem]
    constructor
    · rintro ⟨s, h, hpref, ha⟩
      refine ⟨Tree.comp (Hom.toPath hβ) (SemiallowablePerm.toStructPerm ρ.val) • s, ?_, ?_, ?_⟩
      · intro γ _
        have := NewAllowable.smul_cloud (β := ⊥) (γ := γ) ρ s bot_ne_coe
        rw [h] at this
        exact this.symm
      · obtain ⟨exts, pref | pref⟩ := t
        · cases hpref
          rfl
        · cases hpref
      · rw [mem_smul_set_iff_inv_smul_mem]
        exact ha
    · rintro ⟨s, h, hpref, ha⟩
      refine ⟨(Tree.comp (Hom.toPath hβ) (SemiallowablePerm.toStructPerm ρ.val))⁻¹ • s, ?_, ?_, ?_⟩
      · intro γ _
        have := NewAllowable.smul_cloud (β := ⊥) (γ := γ)
          ρ ((Tree.comp (Hom.toPath hβ) (SemiallowablePerm.toStructPerm ρ.val))⁻¹ • s) bot_ne_coe
        rw [SemiallowablePerm.comp_toPath_toStructPerm] at this
        erw [smul_inv_smul] at this
        rw [h, NewAllowable.members_smul'] at this
        erw [smul_left_cancel_iff] at this
        exact this
      · obtain ⟨exts, pref | pref⟩ := t
        · cases hpref
          simp only [Tree.comp_bot, Tree.toBot_inv_smul, Preference.base.injEq]
          erw [smul_inv_smul]
        · cases hpref
      · simp only [Tree.comp_bot, Tree.toBot_inv_smul, smul_mem_smul_set_iff]
        exact ha
  · intro β hβ
    have : LtLevel β := ⟨hβ⟩
    rw [← NewAllowable.coe_smul]
    erw [StructPerm.ofCoe_smul]
    rw [Equiv.apply_symm_apply]
    dsimp only
    ext s : 1
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨ρ.val β • s, smul_mem_smul_set hs, ?_⟩
      rw [← h, SemiallowablePerm.comp_toPath_toStructPerm]
      rfl
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
      rw [← h, SemiallowablePerm.comp_toPath_toStructPerm]
      rfl

theorem NewTangle.toPretangle_smul (ρ : NewAllowable) (t : NewTangle)
    (lower : ∀ (β : TypeIndex) [LtLevel β], Tangle β → Pretangle β)
    (h : ∀ (β : TypeIndex) [LtLevel β] (ρ' : Allowable β) (t' : Tangle β),
      ρ' • lower β t' = lower β (ρ' • t')) :
    ρ • t.toPretangle lower = (ρ • t).toPretangle lower :=
  t.t.toPretangle_smul ρ lower h

end ConNF
