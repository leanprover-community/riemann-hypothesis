module

public import GroundTheory.GlobalFields.TateThesis.TraceDualLattice
public import GroundTheory.GlobalFields.TateThesis.LatticePoisson
public import GroundTheory.GlobalFields.TateThesis.TraceLatticeEuclidean
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace FourierTransform SchwartzMap nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem idealLattice_summable_norm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : 𝓢(mixedSpace K, ℂ))
    (a : mixedSpace K) : Summable fun α : idealLattice K I => ‖f (α + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add (idealLattice K I) f a

theorem traceDualIdeal_summable_norm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    Summable fun β : idealLattice K (traceDualIdeal K I) =>
      ‖mixedFourier K f β * 𝐞 (mixedTraceForm K β a)‖ := by
  have h := summable_norm_comp_add (idealLattice K (traceDualIdeal K I)) (mixedFourierSchwartz K f) 0
  simpa [norm_mul, Circle.norm_coe, mixedFourierSchwartz_apply] using h

theorem idealLattice_poisson_summation (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    ∑' α : idealLattice K I, f (α + a) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)|)⁻¹ •
        ∑' β : idealLattice K (traceDualIdeal K I),
          mixedFourier K f β * 𝐞 (mixedTraceForm K β a) := by
  set L := euclideanIdealLattice K I
  set F : 𝓢(euclidean.mixedSpace K, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm f
  have hF : (F : euclidean.mixedSpace K → ℂ) = f ∘ (mixedToEuclidean K).symm := rfl
  have h := lattice_poisson_summation L F (mixedToEuclidean K a)

  let eL : idealLattice K I ≃ L :=
    { toFun := fun α => ⟨mixedToEuclidean K α, by
        rw [mem_euclideanIdealLattice, ContinuousLinearEquiv.symm_apply_apply]; exact α.2⟩
      invFun := fun ℓ => ⟨(mixedToEuclidean K).symm ℓ, ℓ.2⟩
      left_inv := fun α => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun ℓ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }

  let eD : idealLattice K (traceDualIdeal K I) ≃ dualLattice L :=
    { toFun := fun β => ⟨mixedToEuclideanConj K β, by
        rw [dualLattice_euclideanIdealLattice, mem_euclideanConjIdealLattice,
          ContinuousLinearEquiv.symm_apply_apply]; exact β.2⟩
      invFun := fun μ => ⟨(mixedToEuclideanConj K).symm μ, by
        have hμ : (μ : euclidean.mixedSpace K) ∈ euclideanConjIdealLattice K (traceDualIdeal K I) := by
          rw [← dualLattice_euclideanIdealLattice]
          exact μ.2
        exact hμ⟩
      left_inv := fun β => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun μ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  have hlhs : ∑' ℓ : L, F (ℓ + mixedToEuclidean K a) = ∑' α : idealLattice K I, f (α + a) := by
    rw [← Equiv.tsum_eq eL]
    refine tsum_congr fun α => ?_
    change f ((mixedToEuclidean K).symm (mixedToEuclidean K α + mixedToEuclidean K a)) = _
    rw [← map_add (f := _), ContinuousLinearEquiv.symm_apply_apply]
  have hrhs : ∑' μ : dualLattice L, 𝓕 (F : euclidean.mixedSpace K → ℂ) μ *
      𝐞 ⟪(μ : euclidean.mixedSpace K), mixedToEuclidean K a⟫ =
      ∑' β : idealLattice K (traceDualIdeal K I),
        mixedFourier K f β * 𝐞 (mixedTraceForm K β a) := by
    rw [← Equiv.tsum_eq eD]
    refine tsum_congr fun β => ?_
    change 𝓕 (F : euclidean.mixedSpace K → ℂ) (mixedToEuclideanConj K β) *
      𝐞 ⟪mixedToEuclideanConj K β, mixedToEuclidean K a⟫ = _
    rw [hF, ← mixedFourier_eq, inner_mixedToEuclideanConj_mixedToEuclidean]
  rw [hlhs, hrhs, covolume_euclideanIdealLattice] at h
  exact h

end

end GroundTheory.Global
