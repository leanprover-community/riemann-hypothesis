module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Mathlib.RingTheory.Ideal.Height
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationAStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTopFormPoleOrderHeightOnePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrimeStatement
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
public import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem heightOne_eq_span_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∃ t : A, Irreducible t ∧ p = Ideal.span {t} := by
  intro k F _ _ _ d u hu A hA p hp hh
  subst hA
  haveI := hp
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (Set.range u)) :=
    hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
  refine ⟨g, ?_, hg⟩
  have hne : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot_of_height_eq_one hh (by rw [hg]; simp)
  rw [hg] at hp
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

theorem mem_traceDual_localization_iff_forall_regularForm : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ p hp hh z
  obtain ⟨t, ht, hpt⟩ := heightOne_eq_span_irreducible k F d u hu A hA p hp hh
  have h2 : ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 :=
    fun Q hQ hov => GlobalTheory.T.height_eq_one_of_liesOver_height_one k F K A B hB p hp hh Q hQ hov
  have h3 := fun Q hQ hov => GlobalTheory.T.exists_uniformizer_ramification_of_height_one k F K d u hu A hA B hB p hp t ht hpt Q hQ (h2 Q hQ hov) hov
  rw [GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt k F K d u hu A hA B hB p hp hh t ht hpt h2 h3 z]
  constructor
  · intro hl Q hQ hov
    obtain ⟨s, e, he, hs, hun, htd⟩ := h3 Q hQ hov
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mpr
      (hl Q hQ hov s e he hs hun htd)
  · intro hr Q hQ hov s e he hs hun htd
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mp (hr Q hQ hov)

end GlobalTheory
