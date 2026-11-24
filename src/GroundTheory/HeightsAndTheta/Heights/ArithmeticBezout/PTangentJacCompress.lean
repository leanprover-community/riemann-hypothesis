module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentJacCompress
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

theorem det_starProjection_compress {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] F) (T : Submodule ℂ E) :
    (T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection)).det =
      (LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype)).det := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : E →L[ℂ] E,
      Q = T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection) := ⟨_, rfl⟩
  rw [← hQdef]
  have hQx : ∀ x : E, Q x =
      T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) := by
    intro x; subst hQdef; simp
  have hQT : T ≤ T.comap (Q : E →ₗ[ℂ] E) := by
    intro x hx
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr hx, sub_self, add_zero]
    exact T.starProjection_apply_mem _
  have hres : (Q : E →ₗ[ℂ] E).restrict hQT =
      LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) := by
    ext1 x
    apply ext_inner_right ℂ
    intro z
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, Submodule.coe_inner,
      LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr x.2, sub_self, add_zero,
      Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr z.2,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hquot : T.mapQ T (Q : E →ₗ[ℂ] E) hQT = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp, ContinuousLinearMap.coe_coe]
    rw [Submodule.Quotient.eq, hQx]
    have h : T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) - x =
        T.starProjection (A.adjoint (A (T.starProjection x))) - T.starProjection x := by abel
    rw [h]
    exact T.sub_mem (T.starProjection_apply_mem _) (T.starProjection_apply_mem _)
  rw [ContinuousLinearMap.det, LinearMap.det_eq_det_mul_det T _ hQT, hres, hquot, LinearMap.det_id,
    mul_one]

theorem TangentJacCompress.proof : TangentJacCompress.Statement := by
  intro n m π T
  unfold tangentJac
  have h := LinearMap.normDet_sq (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype)
  exact h.trans (det_starProjection_compress (LinearMap.toContinuousLinearMap (linProjₗ π)) T).symm

end

end GroundTheory.Heights₂.Heights
