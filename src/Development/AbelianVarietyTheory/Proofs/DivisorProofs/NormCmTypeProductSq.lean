module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Mathlib.RingTheory.Norm.Transitivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem cm_type_normSq_prod_eq_abs_norm (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (d : E) :
    ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  have h1 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ∏ τ : E →+* ℂ, τ d := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ d
    rw [eq_ratCast] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcompl : ∏ τ ∈ Ψᶜ, τ d = ∏ τ ∈ Ψ, (starRingEnd ℂ) (τ d) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      rw [hΨ, hcc]; exact hτ
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      exact (hΨ τ).mp hτ
    · intro τ _; exact hcc τ
    · intro τ _; exact hcc τ
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have hsub : ∏ τ : Ψ, τ.1 d = ∏ τ ∈ Ψ, τ d := Finset.prod_coe_sort Ψ (fun τ => τ d)
  set P := ∏ τ ∈ Ψ, τ d with hP
  have h2 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ((Complex.normSq P : ℝ) : ℂ) := by
    rw [h1, ← Finset.prod_mul_prod_compl Ψ, hcompl, ← map_prod, Complex.mul_conj]
  have h3 : ((Algebra.norm ℚ d : ℚ) : ℝ) = Complex.normSq P := by
    have := h2
    rw [show ((Algebra.norm ℚ d : ℚ) : ℂ) = (((Algebra.norm ℚ d : ℚ) : ℝ) : ℂ) by push_cast; rfl] at this
    exact_mod_cast this
  rw [hsub, h3, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

end GlobalTheory
