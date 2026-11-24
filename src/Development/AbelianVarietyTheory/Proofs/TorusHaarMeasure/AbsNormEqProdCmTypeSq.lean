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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem abs_norm_eq_prod_cmType_sq :
    (∀ (r : ℕ) (X : Data E r) (z : E), ((|Algebra.norm ℚ z| : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2) := by
  classical
  intro r X z

  have hall : ((Algebra.norm ℚ z : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ z := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), Algebra.norm_eq_prod_embeddings ℚ ℂ z]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl)

  have hcompl : ∏ σ ∈ X.Ψᶜ, σ z = ∏ τ ∈ X.Ψ, (starRingEnd ℂ) (τ z) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have h := X.cmType (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at h
      exact h.mpr (Finset.mem_compl.mp hσ)
    · intro τ hτ
      exact Finset.mem_compl.mpr ((X.cmType τ).mp hτ)
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro τ _
      exact ComplexEmbedding.involutive_conjugate E τ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hC : ((Algebra.norm ℚ z : ℚ) : ℂ) = ((∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, ← Finset.prod_mul_prod_compl X.Ψ, hcompl, ← Finset.prod_mul_distrib,
      Finset.prod_coe_sort X.Ψ (fun τ => ‖τ z‖ ^ 2), Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [RCLike.mul_conj]
    push_cast
    rfl
  have hR : ((Algebra.norm ℚ z : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_ratCast]
    exact hC
  have hnn : (0 : ℚ) ≤ Algebra.norm ℚ z := by
    have h0 : (0 : ℝ) ≤ ((Algebra.norm ℚ z : ℚ) : ℝ) := by
      rw [hR]
      positivity
    exact_mod_cast h0
  rw [abs_of_nonneg hnn, hR]

end GlobalTheory
