module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLift
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

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

theorem _root_.GlobalTheory.T.frobenius_power_solution_lift : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow | exact GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow | (intros; apply GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow <;> assumption)
