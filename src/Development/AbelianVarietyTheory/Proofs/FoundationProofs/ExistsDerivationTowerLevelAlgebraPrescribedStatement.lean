module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribed
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

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module (integralClosure (O0 p) Ω) M] (μ ν : M), (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0 → ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0 → ∃ D : (integralClosure (O0 p) Ω) → M, IsDerOn (levelAlg T n) D ∧ D (zS T n) = μ ∧ D (qS T n) = ν := by
  first | exact @GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | exact GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | (intros; apply GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg <;> assumption)
