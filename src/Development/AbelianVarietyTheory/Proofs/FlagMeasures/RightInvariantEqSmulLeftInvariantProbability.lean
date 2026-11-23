module

public import Mathlib.MeasureTheory.Group.Arithmetic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem right_inv_eq_smul_left_inv :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  intro G _ _ _ K μ ν _ _ hμK hνK hμ1 hμinv hνinv
  ext A hA

  have hS : MeasurableSet {p : G × G | p.1 * p.2 ∈ A} := measurable_mul hA
  have hμae : ∀ᵐ g ∂μ, g ∈ K := by
    rw [ae_iff]
    exact hμK
  have hνae : ∀ᵐ g ∂ν, g ∈ K := by
    rw [ae_iff]
    exact hνK
  have h1 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν Set.univ * μ A := by
    rw [Measure.prod_apply hS]
    have hc : ∀ᵐ h ∂ν, μ (Prod.mk h ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = μ A := by
      filter_upwards [hνae] with h hh
      show μ ((fun g => h * g) ⁻¹' A) = μ A
      rw [← Measure.map_apply (measurable_const_mul h) hA, hμinv h hh]
    rw [lintegral_congr_ae hc, lintegral_const, mul_comm]
  have h2 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν A := by
    rw [Measure.prod_apply_symm hS]
    have hc : ∀ᵐ g ∂μ, ν ((fun h => (h, g)) ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = ν A := by
      filter_upwards [hμae] with g hg
      show ν ((fun h => h * g) ⁻¹' A) = ν A
      rw [← Measure.map_apply (measurable_mul_const g) hA, hνinv g hg]
    rw [lintegral_congr_ae hc, lintegral_const, hμ1, mul_one]
  rw [Measure.smul_apply, smul_eq_mul, ← h1, h2]

end GlobalTheory.IwConst
