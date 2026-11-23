module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule : ∀ (A₀ R K₀ L : Type) [CommRing A₀] [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
  [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R] [Algebra K₀ L] [Algebra A₀ L]
  [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L] [FiniteDimensional K₀ L] [IsGalois K₀ L]
  (N : ℕ), 0 < N →
  (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → ¬ Ideal.map (algebraMap A₀ R) (Q.comap (algebraMap A₀ R)) ≤ Q ^ 2) →
  (∀ c : ClassGroup A₀, ∃ d, c = d ^ N) →
  ∀ w : L, w ≠ 0 → (∀ σ : L ≃ₐ[K₀] L, ∃ u : L, u ≠ 0 ∧ σ w = w * u ^ N) →
  ∃ (f : K₀) (J : Submodule R L), f ≠ 0 ∧ J ^ N = Submodule.span R {w / algebraMap K₀ L f} := by
  first | exact @GlobalTheory.DivisorDescent.descent_submodule | exact GlobalTheory.DivisorDescent.descent_submodule | (intros; apply GlobalTheory.DivisorDescent.descent_submodule <;> assumption)
