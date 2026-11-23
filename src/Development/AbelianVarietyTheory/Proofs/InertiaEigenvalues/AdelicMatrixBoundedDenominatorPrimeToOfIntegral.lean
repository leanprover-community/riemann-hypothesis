module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
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

open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

theorem bnd_of_integral_over_prime : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  intro E _ _ p hp n A hA
  let S : Set (HeightOneSpectrum (𝓞 E)) := {Q | ∃ i j, ¬ Valued.v ((A i j) Q) ≤ 1}
  have hS : S.Finite := by
    have hsub : S ⊆ ⋃ i, ⋃ j, {Q | ¬ (A i j) Q ∈ Q.adicCompletionIntegers E} := by
      rintro Q ⟨i, j, h⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨i, j, fun hm => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm)⟩
    refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub
    exact Filter.eventually_cofinite.mp (A i j).2
  refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
  · have hpQ : (p : 𝓞 E) ∉ Q.asIdeal := by
      obtain ⟨i', j', h⟩ := hQ
      exact fun hm => h (hA Q hm i' j')
    exact exists_coprime_natCast_mul_v_le_one p hp Q hpQ _
  · by_contra h
    exact hQ ⟨i, j, h⟩

end GlobalTheory.StdAtPrime
