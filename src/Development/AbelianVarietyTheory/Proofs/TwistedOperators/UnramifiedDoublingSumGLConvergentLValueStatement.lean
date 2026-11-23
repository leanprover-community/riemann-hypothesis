module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.unramified_doubling_sum_GL_convergent_L_value : GlobalTheory.Published.UnramifiedDoublingGL →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (α : Fin N → ℂˣ) (ρ : ℝ), (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) →
  ∀ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ →
  ∀ s : ℂ, ρ - 1 / 2 < s.re →
    Summable (fun e : {e : Fin N → ℤ // Antitone e} => ‖(μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e))‖) ∧
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} => (μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e)))
      (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) N s) := by
  first | exact @GlobalTheory.DoublingSeries.unramified_doubling_sum | exact GlobalTheory.DoublingSeries.unramified_doubling_sum | (intros; apply GlobalTheory.DoublingSeries.unramified_doubling_sum <;> assumption)
