module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.WeilBound.CoreStatements.FlagImmersions.TestPolynomialShiftValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem testPoly_facts : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) ∧ 0 < testDeg Ψ N j ∧ (N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = 0 ∧ Tot τ (testPoly j : RP Ψ N) = ((dimX Ψ N j : ℝ) + 1) * ((N - j : ℕ) : ℝ) * testDeg Ψ N j) ∧ (¬ N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j) ∧ Tot τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j)) := by
  exact @RootFieldNumerics.test_polynomial_shift_values

end GlobalTheory.CompanionTheory.Ar.Top
