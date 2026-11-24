module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneModularFormValueGaloisTransportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosureStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem sum_prod_pow_div_pow {ι S : Type} [Fintype ι] [Fintype S] (m μ : S → ℕ) (x : S → ι → ℂ)
    (ω : ℂ) :
    (∑ i, ∏ s, x s i ^ μ s) / ω ^ (∑ s, μ s * m s) = ∑ i, ∏ s, (x s i / ω ^ m s) ^ μ s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm]

theorem transport_power_sums : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  intro g ι S _ _ act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hfam hq h4 h6 μ
  obtain ⟨-, -, -, -, hpow, -, hprod, -⟩ := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act
  obtain ⟨-, -, -, -, qpow, qfin⟩ := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hM : IsFam act (((∑ s, μ s * m s : ℕ) : ℤ)) fun i τ => ∏ s, f s i τ ^ μ s := by
    have := hprod S Finset.univ (fun s => (μ s : ℤ) * (m s : ℤ)) (fun s i τ => f s i τ ^ μ s)
      (fun s _ => hpow (m s) (f s) (μ s) (hfam s))
    push_cast
    exact this
  have hQ : QConj g N (fun τ => ∑ i, ∏ s, f s i τ ^ μ s) fun τ => ∑ i, ∏ s, f' s i τ ^ μ s :=
    (qfin ι Finset.univ (fun i τ => ∏ s, f s i τ ^ μ s) (fun i τ => ∏ s, f' s i τ ^ μ s)
      fun i _ => (qfin S Finset.univ (fun s τ => f s i τ ^ μ s) (fun s τ => f' s i τ ^ μ s)
        fun s _ => qpow _ _ (μ s) (hq s i)).2).1
  have key := GlobalTheory.T.levelOne_modularForm_value_galois_transport g (∑ s, μ s * m s) N _ _ τ₀ τ₁ ω₀ ω₁ hN
    (fun γ => (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hM γ).1) hQ h4 h6
  rw [sum_prod_pow_div_pow m μ (fun s i => f s i τ₀), sum_prod_pow_div_pow m μ (fun s i => f' s i τ₁)] at key

  simpa only [map_sum, map_prod, map_pow] using key

end GlobalTheory.QFam
