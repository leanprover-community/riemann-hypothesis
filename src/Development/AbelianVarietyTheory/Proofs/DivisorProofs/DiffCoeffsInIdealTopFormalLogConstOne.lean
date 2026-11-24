module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem dIn_top_formalLog_map : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q]
    (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 →
      DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  intro B Q _ _ _ _ σ g hg α i
  classical
  obtain ⟨u, hu⟩ : IsUnit g := isUnit_iff_constantCoeff.mpr (by rw [hg]; exact isUnit_one)
  set φ := algebraMap B Q
  have hG : constantCoeff (map φ g) = 1 := by simp [hg]
  have hd : pderiv (R := Q) i (formalLog (map φ g)) = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
    have h1 := mul_pderiv_formalLog hG i
    rw [pderiv_map] at h1
    have h2 : map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    calc pderiv (R := Q) i (formalLog (map φ g))
        = (map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g) * pderiv (R := Q) i (formalLog (map φ g)) := by
          rw [h2, one_mul]
      _ = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
          rw [mul_assoc, h1, map_mul]
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · refine ⟨coeff (α - Finsupp.single i 1) ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g),
      Submodule.mem_top, ?_⟩
    rw [natCast_mul_coeff_of_pderiv_eq hd hα, coeff_map]

end GlobalTheory.QLog
