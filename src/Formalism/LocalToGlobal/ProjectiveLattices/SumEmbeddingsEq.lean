module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

noncomputable section

namespace Formalism.L2.Pj.DatLin

open NumberField ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E]

theorem sum_embeddings_eq (z : E) :
    (((Algebra.trace ℚ E z : ℚ) : ℂ)) = ∑ σ : E →+* ℂ, σ z := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

theorem trace_eq_sum_psi (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ ∈ Ψ, 2 * (τ z).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, sum_embeddings_eq, ← Finset.sum_add_sum_compl Ψ]

  have hc : ∑ σ ∈ Ψᶜ, σ z = ∑ τ ∈ Ψ, conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_compl] at hσ ⊢
      rw [hΨ, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
      exact hσ
    · intro τ hτ
      simp only [Finset.mem_compl]
      exact (hΨ τ).mp hτ
    · intro σ _; exact star_star σ
    · intro τ _; exact star_star τ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hc, ← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Complex.add_conj]

theorem sesq_repr [StarRing E] {V : Type} [AddCommGroup V] [Module E V] {ι : Type} [Fintype ι]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis ι E V) (x y : V) :
    h x y = ∑ i, ∑ j, star (b.repr x i) * h (b i) (b j) * b.repr y j := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
  starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Formalism.L2.Pj.DatLin
