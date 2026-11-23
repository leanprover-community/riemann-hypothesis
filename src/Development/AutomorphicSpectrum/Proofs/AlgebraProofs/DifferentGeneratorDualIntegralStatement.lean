module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
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

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem _root_.GlobalTheory.T.different_generator_dual_integral : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E] [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → algebraMap A K d ≠ 0 ∧ (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧ ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A, ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | exact GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt <;> assumption)
