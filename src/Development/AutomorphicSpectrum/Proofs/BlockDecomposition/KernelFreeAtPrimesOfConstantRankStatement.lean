module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRank
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.kernel_free_at_primes_of_constant_rank : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) → Module.Projective R (LinearMap.ker d) → (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) → ∀ (p : Ideal R) [p.IsPrime], Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.Finite (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.finrank (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  exact @GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free
