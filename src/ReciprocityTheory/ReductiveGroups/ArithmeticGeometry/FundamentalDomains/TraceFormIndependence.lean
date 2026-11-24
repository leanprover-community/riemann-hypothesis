module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma add_conj' (w : ℂ) : w + conj w = 2 * (w.re : ℂ) := by
  apply Complex.ext <;> simp <;> ring

lemma trace_re (X : Data E r) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have hall : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
    have h' : (algebraMap ℚ ℂ) (Algebra.trace ℚ E z) = ((Algebra.trace ℚ E z : ℚ) : ℂ) :=
      eq_ratCast _ _
    rw [← h', h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => RingHom.ext fun x => by simp
  have hconj : ∑ σ ∈ X.Ψᶜ, σ z = ∑ σ ∈ X.Ψ, conj (σ z) := by
    apply Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ)
    · intro σ hσ
      simp only [Finset.mem_compl] at hσ ⊢
      rw [X.cmType, hcc]
      exact hσ
    · intro σ hσ
      simp only [Finset.mem_compl] at hσ ⊢
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact hcc σ
    · intro σ _
      exact hcc σ
    · intro σ _
      simp [ComplexEmbedding.conjugate_coe_eq]
  push_cast
  rw [hall, ← Finset.sum_add_sum_compl X.Ψ, hconj, ← Finset.sum_add_distrib,
    ← Finset.sum_coe_sort X.Ψ]
  exact Finset.sum_congr rfl fun τ _ => add_conj' _

end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
