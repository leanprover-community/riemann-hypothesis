module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitApproximationAdicCompletion
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


theorem _root_.GlobalTheory.T.exists_unit_approximation_adic_completion : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M] [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N] (φ : M →ₐ[A] N), (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) → (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) → ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧ ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  first | exact @GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | exact GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | (intros; apply GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal <;> assumption)
