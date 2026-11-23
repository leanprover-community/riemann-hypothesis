module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralProdEqZeroOfInner
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

theorem _root_.GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' : ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  first | exact @GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner | exact GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner | (intros; apply GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner <;> assumption)
