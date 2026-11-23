module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.PtTie

theorem depth_sum_le_PN : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → (WeightAlgebra.DF w : ℝ) * (Real.log (WeightAlgebra.DF w) + 2.2) + (c2 D w * Real.log D.host.QS + cHalf w * Real.log D.host.q + cHalf w * Real.log D.host.d) + ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤ WeightAlgebra.PN D large₂ * w.size := by
  intro D large₂ j w _ hlog
  obtain ⟨-, -, hM, hG, hc, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log (WeightAlgebra.DF w : ℝ) := Real.log_natCast_nonneg _
  have hs : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have e : ((WeightAlgebra.DF w : ℕ) : ℝ) = ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by
      simp [WeightAlgebra.DF, WeightAlgebra.degP, Nat.cast_sum]
    have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
    unfold WeightFamilies.Wt.size
    linarith
  have hg2 : ∀ i, (2 : ℝ) ≤ D.host.g i := fun i => by exact_mod_cast (D.host.g_prime i).two_le
  have hterm : ∀ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log (D.host.g i) := fun i =>
    mul_le_mul_of_nonneg_right (div_le_self hD (by linarith [hg2 i])) (Real.log_natCast_nonneg _)
  have hsum : ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rw [Fin.sum_univ_two, Real.log_mul (by linarith [hg2 0]) (by linarith [hg2 1])]
    linarith [hterm 0, hterm 1]
  have hP : 0 ≤ WeightAlgebra.PN D large₂ := by
    unfold WeightAlgebra.PN WeightAlgebra.lamStar
    linarith
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hs hP)
  have h1 := mul_le_mul_of_nonneg_left hlog hD
  unfold WeightAlgebra.PN WeightAlgebra.lamStar
  nlinarith

end GlobalTheory.PtTie
