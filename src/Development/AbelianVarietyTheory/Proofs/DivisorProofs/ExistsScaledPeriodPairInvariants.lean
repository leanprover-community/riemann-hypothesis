module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_scaled_periodPair : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, c * z ∈ L'.lattice ↔ z ∈ L.lattice) ∧ L'.g₂ = (c ^ 4)⁻¹ * L.g₂ ∧
      L'.g₃ = (c ^ 6)⁻¹ * L.g₃ ∧
      (∀ z, L'.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z) ∧
      (latticeCurve L').j = (latticeCurve L).j := by
  intro L c hc
  have hH : IsHomothetic c L (scalePeriods L c hc) := isHomothetic_scalePeriods L c hc
  have h2 : (scalePeriods L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, hH.G_eq]; ring
  have h3 : (scalePeriods L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, hH.G_eq]; ring
  refine ⟨scalePeriods L c hc, hH, h2, h3, hH.derivWeierstrassP_mul, ?_⟩
  have hi : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have hD : (scalePeriods L c hc).g₂ ^ 3 - 27 * (scalePeriods L c hc).g₃ ^ 2 =
      (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h2, h3]; ring
  have hn : (scalePeriods L c hc).g₂ ^ 3 = (c ^ 12)⁻¹ * L.g₂ ^ 3 := by rw [h2]; ring
  rw [latticeCurve_j_eq, latticeCurve_j_eq, hD, hn, mul_left_comm, mul_div_mul_left _ _ hi]

end GlobalTheory.CMModel
