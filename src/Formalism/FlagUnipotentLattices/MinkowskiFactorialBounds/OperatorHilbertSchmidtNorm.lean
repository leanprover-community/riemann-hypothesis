import Formalism.FlagUnipotentLattices.CuspidalityThreshold
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.NearFarVolumeBounds

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix

namespace Formalism.HermitianLatticeCounting.P




theorem probability_zero : PZero := by
  intro N ep X h0 hX
  ext a b
  apply hX
  unfold q0 at h0
  rcases Nat.min_eq_zero_iff.mp h0 with h | h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp at ha hb
    rw [ha, hb]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp at ha hb
    rw [ha, hb]



theorem volume_level : VolLevel := by
  intro C n f rd g b volG volK hn hf hrd hg hb hvK hG hK
  obtain ⟨hY2, -, -, -, hgY, -⟩ := ydat_facts hn hf hrd hg hb
  have hY0 : 0 < Ydat n f rd g b := by linarith
  have e : Ydat n f rd g b ^ ((C + 2) * (n : ℝ) ^ 2 * f)
      = Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) * Ydat n f rd g b ^ (2 * n ^ 2 * f) := by
    rw [← Real.rpow_natCast (Ydat n f rd g b) (2 * n ^ 2 * f), ← Real.rpow_add hY0]
    congr 1; push_cast; ring
  rw [e, div_eq_mul_inv]
  have h1 : volK⁻¹ ≤ Ydat n f rd g b ^ (2 * n ^ 2 * f) :=
    hK.trans (pow_le_pow_left₀ (by linarith) hgY _)
  have h2 : 0 ≤ volK⁻¹ := by positivity
  have h3 : 0 ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) := (Real.rpow_pos_of_pos hY0 _).le
  calc volG * volK⁻¹ ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) * volK⁻¹ := by gcongr
    _ ≤ _ := by gcongr



end Formalism.HermitianLatticeCounting.P
