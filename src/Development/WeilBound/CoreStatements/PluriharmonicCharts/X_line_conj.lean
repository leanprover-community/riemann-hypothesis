module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_line_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  intro K _ ι _ A hA
  have hne : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ∀ k, ∃ i, (fun p => starRingEnd ℂ (z p)) ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa using hi⟩
  refine ⟨⟨A.a, fun z => Real.sqrt (A.h z * A.h fun p => starRingEnd ℂ (z p)), ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · intro z hz
    exact Real.sqrt_pos.2 (mul_pos (A.pos z hz) (A.pos _ (hne z hz)))
  · intro c z hc
    have h1 := A.smul (fun k => starRingEnd ℂ (c k)) (fun p => starRingEnd ℂ (z p)) (fun k => by simpa using hc k)
    simp only [RCLike.norm_conj] at h1
    simp only [map_mul]
    rw [h1, A.smul c z hc]
    have h0 : 0 ≤ ∏ k, ‖c k‖ ^ A.a k := Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    rw [mul_mul_mul_comm, Real.sqrt_mul (mul_nonneg h0 h0), Real.sqrt_mul_self h0]
  · have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => fun p => starRingEnd ℂ (z p)) := by
      refine contDiff_pi.2 fun p => ?_
      exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) p)
    refine ContDiffOn.sqrt (ContDiffOn.mul hA (hA.comp hc.contDiffOn fun z hz => hne z hz)) ?_
    intro z hz
    exact (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).ne'
  · intro z
    simp only [Complex.conj_conj, mul_comm]
  · intro z hz
    show Real.log (Real.sqrt _) = _
    rw [Real.log_sqrt (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).le,
      Real.log_mul (A.pos z hz).ne' (A.pos _ (hne z hz)).ne']
