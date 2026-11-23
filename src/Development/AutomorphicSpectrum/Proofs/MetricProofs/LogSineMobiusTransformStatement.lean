module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransform
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.log_det_gram_subharmonic : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | exact GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le <;> assumption)
