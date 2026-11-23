module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminant
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

open Set Filter Topology

theorem _root_.GlobalTheory.T.holomorphic_group_law_germ : ∀ (n g : ℕ) (b₀ : Fin n → ℂ) (μ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ μ (b₀, 0, 0) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), μ (p.1, p.2, 0) = p.2 ∧ μ (p.1, 0, p.2) = p.2) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1)) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0), μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) → ∃ L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧ HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), L (p.1, μ p) = L (p.1, p.2.1) + L (p.1, p.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law <;> assumption)
