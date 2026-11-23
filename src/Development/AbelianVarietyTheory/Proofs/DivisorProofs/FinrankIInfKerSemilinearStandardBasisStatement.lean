module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinearStandardBasis
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

open Module

theorem _root_.GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V] [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V), (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ → ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V), (∀ i v, a' i (f v) = f (a i v)) → finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) = finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  first | exact @GlobalTheory.BadCount.finrank_iInf_ker_semilinear | exact GlobalTheory.BadCount.finrank_iInf_ker_semilinear | (intros; apply GlobalTheory.BadCount.finrank_iInf_ker_semilinear <;> assumption)
