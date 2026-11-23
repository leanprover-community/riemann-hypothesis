module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichPreserves

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix ReciprocityTheory.ChartRestriction.G.SA

theorem HypPairExists.proof : HypPairExists.Statement := by
  intro E _ σ hσ h2 N J hJ hdet e he0 hee

  have hw : ∃ j, ∑ i, e i * J i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : e ᵥ* J = 0 := by
      ext j
      simpa [vecMul, dotProduct] using h j
    apply he0
    calc e = e ᵥ* (J * J⁻¹) := by rw [mul_nonsing_inv J hdet, vecMul_one]
      _ = (e ᵥ* J) ᵥ* J⁻¹ := by rw [vecMul_vecMul]
      _ = 0 := by rw [h0, zero_vecMul]
  obtain ⟨j, hj⟩ := hw
  have hsingle : hf σ J e (Pi.single j 1) = ∑ i, e i * J i j := by
    simp only [hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp

  obtain ⟨a, hea⟩ : ∃ a : Fin N → E, hf σ J e a = 1 :=
    ⟨σ (∑ i, e i * J i j)⁻¹ • Pi.single j 1, by
      rw [hf_smul_right, hsingle, hσ, inv_mul_cancel₀ hj]⟩
  have hae : hf σ J a e = 1 := by
    rw [← hf_symm hσ hJ, hea, map_one]
  have haa : σ (hf σ J a a) = hf σ J a a := hf_symm hσ hJ a a
  set t : E := -(hf σ J a a) / 2 with ht_def
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have ht : t + σ t = -(hf σ J a a) := by
    rw [ht_def, map_div₀, map_neg, haa, hσ2]
    field_simp
    ring
  refine ⟨a + t • e, ?_, ?_⟩
  · rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
      hf_smul_right, hea, hae, hee]
    linear_combination ht
  · rw [hf_add_right, hf_smul_right, hea, hee, mul_zero, add_zero]

end StrongApprox

end GroundTheory.Heights₂.Heights
