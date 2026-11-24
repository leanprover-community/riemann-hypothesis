module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianNormFibreDilation
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.lintegral_hermitianNormFibre_dilation : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib → β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ → ∫⁻ y, φ y ∂(fib (t * β)) = ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  first | exact @GlobalTheory.FibreScaling.lintegral_fibre_scale | exact GlobalTheory.FibreScaling.lintegral_fibre_scale | (intros; apply GlobalTheory.FibreScaling.lintegral_fibre_scale <;> assumption)
