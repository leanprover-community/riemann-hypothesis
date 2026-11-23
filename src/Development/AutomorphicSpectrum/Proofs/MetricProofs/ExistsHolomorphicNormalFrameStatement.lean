module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrame
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

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.log_sine_mobius_transform : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | exact GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame <;> assumption)
