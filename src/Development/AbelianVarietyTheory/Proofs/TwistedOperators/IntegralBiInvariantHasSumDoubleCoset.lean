module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MainThm
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

open scoped Pointwise

namespace GlobalTheory

theorem integral_biInvariant_hasSum_doubleCoset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (m : Measure G) [m.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) →
  ∀ (ι : Type) [Countable ι] (x : ι → G),
    Pairwise (Function.onFun Disjoint fun i => DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
  ∀ F : G → ℂ, (∀ g, ∀ j ∈ J, ∀ j' ∈ J, F (j * g * j') = F g) →
    (∀ g, F g ≠ 0 → ∃ i, g ∈ DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
    Summable (fun i => m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) * ‖F (x i)‖) →
    Integrable F m ∧
    HasSum (fun i => (m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) : ℂ) * F (x i)) (∫ g, F g ∂m) ∧
    HasSum (fun c : DoubleCoset.Quotient (J : Set G) (J : Set G) =>
      (m.real (DoubleCoset.doubleCoset c.out (J : Set G) (J : Set G)) : ℂ) * F c.out) (∫ g, F g ∂m) := by
  first
  | exact @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | (apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm ..)

end GlobalTheory
