module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isGramPair_of_isMetricFr : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  intro F _ σ X ι _ m k E H H' hH hH' τ
  have hA (y : CxPts X.str σ) := (E.nonempty (under y)).choose_spec
  refine ⟨fun y => ⟨(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y _ (hA y) τ).1,
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H' hH' y _ (hA y) τ).1⟩, fun y => ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y _ (hA y)] with z hz
  have hP := (Fr.mem_iff hz).1 (hA z) τ
  have hT := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) _ z (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)
  refine ⟨_, _, _, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ hz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ (hA z)] with w h1 h2
  exact ⟨hH.trans w _ h1 _ h2 τ, hH'.trans w _ h1 _ h2 τ⟩

end GlobalTheory.ChernCalc
