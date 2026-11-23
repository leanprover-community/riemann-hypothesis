module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
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

@[expose] public section

open PositivityTheory.Rg.BcB.G8

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarProd

theorem haarSplit : HaarSplit := by
  intro G A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ α _ e
  have : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let β₀ : Measure B := Measure.haar
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map e) (α.prod β₀)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) (α.prod β₀)
  refine ⟨Measure.haarScalarFactor (μ.map e) (α.prod β₀) • β₀, ?_, ?_⟩
  · exact Measure.IsHaarMeasure.nnreal_smul _ hpos.ne'
  · rw [Measure.prod_smul_right]
    exact hc

end GlobalTheory.CompanionTheory.HaarProd
