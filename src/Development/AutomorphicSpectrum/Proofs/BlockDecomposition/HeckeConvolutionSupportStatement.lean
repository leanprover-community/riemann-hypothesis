module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
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
import Mathlib.Tactic.NormNum.Prime
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical


theorem _root_.GlobalTheory.T.hecke_convolution_support : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
  IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧ ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | exact GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | (intros; apply GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke <;> assumption)
