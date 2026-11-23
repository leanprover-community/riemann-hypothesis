module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgExh.Dec.N.S

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

def Fub2 : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∃ (μN μM : Measure (Formalism.REAL.UJ ε)), SFinite μN ∧ SFinite μM ∧ μM (flagM ε (W A))ᶜ = 0 ∧
      (∀ a : Formalism.REAL.UJ ε, a ∈ flagM ε (W A) → (∀ m ∈ flagM ε (W A), m * a = a * m) → μM.map (· * a) = μM) ∧
      (∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
        (∀ g, ∀ k ∈ Formalism.REAL.KG ε, F (g * k) = F g) →
        ∫⁻ g, F g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN) ∧
      ∀ ν : Measure (PSub ε A), ν.IsHaarMeasure → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
          ∫⁻ x, F x ∂(muPar ε A ν) = c * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN

end CompanionTheory.RgExh.Dec.N.S

namespace GlobalTheory.CompanionTheory.RgFubOf

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

theorem fubini_of_parabolic_multiple : Fub2 → Fub := by
  intro h n ε A hA
  obtain ⟨μN, μM, hN, hM, h0, hinv, hκ, hH⟩ := h n ε A hA
  refine ⟨μN, μM, hN, hM, h0, hinv, hκ, ?_⟩
  rintro μ ⟨ν, rfl, hν⟩ E hE hnull
  have := hN
  have := hM
  obtain ⟨c, -, -, hc⟩ := hH ν hν
  have hF := hc (E.indicator 1) (measurable_one.indicator hE)
  refine (lintegral_indicator_one (μ := muPar ε A ν) hE).symm.trans (hF.trans ?_)
  have hae : ∀ᵐ p ∂(μN.prod μM), p.1 * p.2 ∉ E := measure_eq_zero_iff_ae_notMem.1 hnull
  have hzero : (fun u => ∫⁻ m, modA A m * E.indicator 1 (u * m) ∂μM) =ᵐ[μN] 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hae] with u hu
    have hslice : (fun m => modA A m * E.indicator 1 (u * m)) =ᵐ[μM] 0 := by
      filter_upwards [hu] with m hm
      simp [Set.indicator_of_notMem hm]
    rw [lintegral_congr_ae hslice]
    simp
  rw [lintegral_congr_ae hzero]
  simp

end GlobalTheory.CompanionTheory.RgFubOf
