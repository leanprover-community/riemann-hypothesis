import Mathlib
import GroundTheory.LocalFields.ConductorReciprocity

noncomputable section

open ValuativeRel

namespace GroundTheory.LocalField

section Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]

def conductor : ℕ :=
  sInf {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}

theorem conductor_le_iff [IsSepClosure K Ω] (n : ℕ) :
    conductor L ≤ n ↔ unitFiltrationUnits K n ≤ (normUnits K L).range := by
  have hne : {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}.Nonempty :=
    exists_unitFiltrationUnits_le (isOpen_range_normUnits_and_finiteIndex L).1
  constructor
  · intro h
    exact (unitFiltrationUnits_antitone h).trans (Nat.sInf_mem hne)
  · intro h
    exact Nat.sInf_le h

end Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

section Conductor

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem exists_int_eq_of_forall_upperRamificationGroup_ne {v : ℝ}
    (h : ∀ w, v < w → upperRamificationGroup K L w ≠ upperRamificationGroup K L v) :
    ∃ m : ℤ, v = m := by
  by_contra hv
  simp only [not_exists] at hv
  have hlt : v < ⌈v⌉ := lt_of_le_of_ne (Int.le_ceil v) (hv ⌈v⌉)
  apply h _ hlt
  rw [upperRamificationGroup_eq_ceil L v, upperRamificationGroup_eq_ceil L (⌈v⌉ : ℝ), Int.ceil_intCast]

theorem unitFiltrationUnits_le_range_normUnits_iff (n : ℕ) :
    unitFiltrationUnits K n ≤ (normUnits K L).range ↔ upperRamificationGroup K L n = ⊥ := by
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap L n, Subgroup.map_eq_bot_iff,
    ker_restrictAb_localArtinMap]

theorem upperRamificationGroup_natCast_eq_bot_iff (n : ℕ) :
    upperRamificationGroup K L n = ⊥ ↔ conductor L ≤ n := by
  rw [conductor_le_iff, unitFiltrationUnits_le_range_normUnits_iff]

theorem upperRamificationGroup_eq_bot_iff (hL : L ≠ ⊥) (v : ℝ) :
    upperRamificationGroup K L v = ⊥ ↔ (conductor L : ℝ) - 1 < v := by
  rcases le_or_gt v (-1) with hv | hv
  · have htop : upperRamificationGroup K L v = ⊤ := by
      rw [upperRamificationGroup_of_nonpos (by linarith), lowerRamificationGroupReal_eq_top hv]
    have hG : (⊤ : Subgroup (L ≃ₐ[K] L)) ≠ ⊥ := by
      have h1 : Module.finrank K L ≠ 1 := fun h => hL (IntermediateField.finrank_eq_one_iff.1 h)
      have h2 : 1 < Nat.card (L ≃ₐ[K] L) := by
        rw [IsGalois.card_aut_eq_finrank]
        have := Module.finrank_pos (R := K) (M := L)
        omega
      have : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 h2
      exact top_ne_bot
    rw [htop]
    simp only [hG, false_iff, not_lt]
    have := (conductor L).cast_nonneg (α := ℝ)
    linarith
  · have hc : 0 ≤ ⌈v⌉ := Int.le_ceil_iff.2 (by push_cast; linarith)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hc
    rw [upperRamificationGroup_eq_ceil L v, hk, Int.cast_natCast, upperRamificationGroup_natCast_eq_bot_iff,
      ← Nat.cast_le (α := ℤ), ← hk, Int.le_ceil_iff]
    push_cast
    rfl

theorem isGreatest_conductor_sub_one (hL : L ≠ ⊥) :
    IsGreatest {v : ℝ | upperRamificationGroup K L v ≠ ⊥} ((conductor L : ℝ) - 1) := by
  refine ⟨?_, fun v hv => ?_⟩
  · show upperRamificationGroup K L _ ≠ ⊥
    rw [Ne, upperRamificationGroup_eq_bot_iff L hL]
    exact lt_irrefl _
  · have hv' : ¬ ((conductor L : ℝ) - 1 < v) := fun h => hv ((upperRamificationGroup_eq_bot_iff L hL v).2 h)
    exact not_lt.1 hv'

end Conductor

section Ab

variable (K Ω) in

def upperRamificationGroupAb (v : ℝ) :
    Subgroup (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  ⨅ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
    (upperRamificationGroup K L v).comap (restrictAb L (le_maximalAbelianExtension L))



end Ab

end GroundTheory.LocalField
