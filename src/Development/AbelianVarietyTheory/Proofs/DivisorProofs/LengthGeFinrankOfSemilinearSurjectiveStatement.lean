module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.WittVector.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.length_ge_finrank_of_semilinear_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U] [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U), Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) → ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) → (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧ ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  first | exact @GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | exact GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | (intros; apply GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj <;> assumption)
