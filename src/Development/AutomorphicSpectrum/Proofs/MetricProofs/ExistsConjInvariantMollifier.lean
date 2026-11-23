module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier : ∀ n : ℕ, ∃ ρ : ReciprocityTheory.AnForm.A.Mollifier n, ∀ v, ρ.toFun (star v) = ρ.toFun v := by
  intro n
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hmp : MeasureTheory.MeasurePreserving (fun v : Fin n → ℂ => star v) :=
    MeasureTheory.volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)
  have hme : MeasurableEmbedding (fun v : Fin n → ℂ => star v) :=
    (starLinearEquiv ℝ (A := Fin n → ℂ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v : Fin n → ℂ => star v) :=
    contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)
  have hI : MeasureTheory.Integrable ρ.toFun :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [ρ.integral_eq_one]; norm_num)
  have hcomp : ∫ w : Fin n → ℂ, ρ.toFun (star w) = 1 := by
    rw [hmp.integral_comp hme ρ.toFun, ρ.integral_eq_one]
  have hI2 : MeasureTheory.Integrable (fun w : Fin n → ℂ => ρ.toFun (star w)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hcomp]; norm_num)
  refine ⟨⟨fun v => (ρ.toFun v + ρ.toFun (star v)) / 2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (ρ.contDiff.add (ρ.contDiff.comp hsm)).div_const 2
  · intro w
    exact div_nonneg (add_nonneg (ρ.nonneg _) (ρ.nonneg _)) two_pos.le
  · intro w hw
    by_contra h
    have h1 : ρ.toFun w = 0 := by
      by_contra h'
      exact h (ρ.support_subset h')
    have h2 : ρ.toFun (star w) = 0 := by
      by_contra h'
      have hb := ρ.support_subset h'
      rw [Metric.mem_ball, dist_zero_right, norm_star] at hb
      exact h (by rw [Metric.mem_ball, dist_zero_right]; exact hb)
    exact hw (by simp [h1, h2])
  · show ∫ w : Fin n → ℂ, (ρ.toFun w + ρ.toFun (star w)) / 2 = 1
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hI hI2, ρ.integral_eq_one, hcomp]
    norm_num
  · intro c w hc
    show (ρ.toFun (c • w) + ρ.toFun (star (c • w))) / 2 = (ρ.toFun w + ρ.toFun (star w)) / 2
    rw [star_smul, ρ.circle_inv c w hc, ρ.circle_inv (star c) (star w) (by rw [norm_star]; exact hc)]
  · intro v
    show (ρ.toFun (star v) + ρ.toFun (star (star v))) / 2 = (ρ.toFun v + ρ.toFun (star v)) / 2
    rw [star_star, add_comm]
