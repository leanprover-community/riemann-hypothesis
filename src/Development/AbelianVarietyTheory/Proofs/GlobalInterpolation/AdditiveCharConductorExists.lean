module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfNormSubOneLt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConductorAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsTer
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

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CharConductor

theorem eq_one_of_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterationConvergence.main
  | exact _root_.GlobalTheory.IterationConvergence.main
  | (apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)

theorem exists_exponent_of_valued {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | (apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)

theorem exists_conductor_exponent : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion

end GlobalTheory.CharConductor
