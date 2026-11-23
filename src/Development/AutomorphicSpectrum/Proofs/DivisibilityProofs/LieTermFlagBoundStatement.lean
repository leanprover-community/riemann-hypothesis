module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LieTermFlagBound
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.lie_term_flag_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → ∀ (τ : Ψ) (σ : Ψ ⊕ Ψ) (k : ℕ), 2 ≤ k → k ≤ N → |k * degFl (pLie j (k - 1) σ * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp | exact GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp <;> assumption)
