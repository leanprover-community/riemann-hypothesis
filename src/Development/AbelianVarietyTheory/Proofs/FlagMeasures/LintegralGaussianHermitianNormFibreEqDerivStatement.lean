module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralGaussianHermitianNormFibreEqDeriv
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.lintegral_gaussian_hermitianNormFibre_eq_deriv : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β d : ℝ), IsDxDq fib → β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Sp P Q | qf y ≤ t}, gaussSp y) d β → ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib β) = ENNReal.ofReal (2 ^ (P + Q) * d) := by
  first | exact @GlobalTheory.GaussFibre.gauss_fibre | exact GlobalTheory.GaussFibre.gauss_fibre | (intros; apply GlobalTheory.GaussFibre.gauss_fibre <;> assumption)
