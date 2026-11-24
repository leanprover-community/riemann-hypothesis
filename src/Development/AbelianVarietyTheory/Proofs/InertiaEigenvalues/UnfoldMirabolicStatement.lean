module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
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

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped ENNReal NNReal ComplexConjugate

theorem _root_.GlobalTheory.T.unfold_mirabolic_alt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (𝓕 𝓕₀ : Set (GA E a)), IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕 μ → IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ → ∀ (w : GA E a → ℝ≥0), Measurable w → (∀ γ ∈ mirU E a (a - 1), ∀ g, w (ratGL E a γ * g) = w g) → (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), w (blkU y * g) = w g) → (∀ f, Good ψ (a - 1) f → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕₀, ‖whit ψ (a - 1) f g‖ₑ ^ 2 * w g ∂μ) ∧ ∀ f f', Good ψ (a - 1) f → Good ψ (a - 1) f' → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧ IntegrableOn (fun g => whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ)) 𝓕₀ μ ∧ ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕₀, whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ) ∂μ := by
  first | exact @GlobalTheory.MirTower.unfold_mirabolic | exact GlobalTheory.MirTower.unfold_mirabolic | (intros; apply GlobalTheory.MirTower.unfold_mirabolic <;> assumption)
