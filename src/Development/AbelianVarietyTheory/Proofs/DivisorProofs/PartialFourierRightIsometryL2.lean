module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2Norm
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEv.L2RightPartial

theorem partR_lintegral_sq_eq_const_mul_of_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR (κ := κ) A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR (κ := κ) A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ A hmem hA μ hμ
  exact GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA (κ := κ) A hA hmem μ hμ

end GlobalTheory.DoublingEv.L2RightPartial

end
