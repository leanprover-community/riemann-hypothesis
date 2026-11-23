module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlane
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.mobius_action_upper_half_plane : ∀ (F : Type) [Field F] [NumberField F], ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (τ : InfinitePlace F → ℂ), (∀ w, 0 < (τ w).im) → (∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im = (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 ∧ 0 < (mob ρ γ τ w).im) ∧ (∀ γ γ' : SL(2, F), mob ρ (γ * γ') τ = mob ρ γ (mob ρ γ' τ)) ∧ (∀ b : F, mob ρ (nMat b) τ = fun w => τ w + (ρ w b : ℝ)) ∧ (∀ a : Fˣ, mob ρ (mMat a) τ = fun w => ((ρ w (a : F) : ℝ) : ℂ) ^ 2 * τ w) ∧ mob ρ wMat τ = fun w => -(τ w)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Mobius.main | exact GlobalTheory.CompanionTheory.SW.Core.Mobius.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Mobius.main <;> assumption)
