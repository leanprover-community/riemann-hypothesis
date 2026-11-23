module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib.Analysis.InnerProductSpace.Laplacian
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

namespace ReciprocityTheory.AnForm.A

open MeasureTheory
open scoped Laplacian

noncomputable section

def ddcDens (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * Δ u z

def ddcCoordDens {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  (2 / Real.pi) * ReciprocityTheory.AnForm.levi u z (Pi.single j 1)

def GreenParamFiberStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u → ∀ p : E,
    Integrable (fun z : ℂ => Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z = 2 * Real.pi * u (0, p)

def GreenParamStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
        ((volume : Measure ℂ).prod μ) ∧
      ∫ q : ℂ × E, Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1 ∂((volume : Measure ℂ).prod μ)
        = 2 * Real.pi * ∫ p : E, u (0, p) ∂μ

def GreenCoordStatement : Prop :=
  ∀ (D : ℕ) (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∧
      ∫ z : Fin (D + 1) → ℂ, Real.log ‖z j‖ * ddcCoordDens j u z =
        ∫ w : Fin D → ℂ, u (Fin.insertNth j 0 w)

def GreenMixedStatement : Prop :=
  ∀ (D : ℕ) (j a b : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    (a, b) ≠ (j, j) →
    Integrable (fun z : Fin (D + 1) → ℂ => (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) ∧
      ∫ z : Fin (D + 1) → ℂ, (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b = 0

end

end ReciprocityTheory.AnForm.A
