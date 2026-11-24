module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotent
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.nat_of_simple_lowering_nilpotent : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → (j : ℕ) = i + 1 → (∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) → ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | exact GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | (intros; apply GlobalTheory.CompanionTheory.PresRho.natural_of_primitive <;> assumption)
