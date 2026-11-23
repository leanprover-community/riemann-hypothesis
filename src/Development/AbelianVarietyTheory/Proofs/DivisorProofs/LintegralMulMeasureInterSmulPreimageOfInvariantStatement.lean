module

public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariant
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

@[expose] public section

open MeasureTheory
open scoped ENNReal Pointwise


theorem _root_.GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  first | exact @GlobalTheory.lintegral_mul_measure_inter_smul_preimage | exact GlobalTheory.lintegral_mul_measure_inter_smul_preimage | (intros; apply GlobalTheory.lintegral_mul_measure_inter_smul_preimage <;> assumption)
