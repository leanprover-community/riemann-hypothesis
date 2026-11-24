module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace SmoothVectorsIntertwiner

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def rmulₗ (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun M := Matrix.of.symm (Matrix.of M * B)
  map_add' x y := by
    funext i j k
    simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i j k
    simp [Matrix.mul_apply, Finset.mul_sum]

def lmulₗ (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun M := Matrix.of.symm (B * Matrix.of M)
  map_add' x y := by
    funext i j k
    simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i j k
    simp [Matrix.mul_apply, Finset.mul_sum]

def rmulL (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap (rmulₗ B)

def lmulL (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap (lmulₗ B)

theorem rmulL_apply (B : Matrix (Fin a) (Fin a) (ι → ℂ)) (M : LieI ι a) :
    rmulL B M = Matrix.of.symm (Matrix.of M * B) := rfl

theorem lmulL_apply (B : Matrix (Fin a) (Fin a) (ι → ℂ)) (M : LieI ι a) :
    lmulL B M = Matrix.of.symm (B * Matrix.of M) := rfl

theorem isOpen_U : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := by
  have hc : Continuous fun M : LieI ι a => (Matrix.of M).det :=
    Continuous.matrix_det continuous_id
  have e : {M : LieI ι a | IsUnit (Matrix.of M)} =
      (fun M : LieI ι a => (Matrix.of M).det) ⁻¹' {x | IsUnit x} := by
    ext M
    simp [Matrix.isUnit_iff_isUnit_det]
  rw [e]
  exact Units.isOpen.preimage hc

omit [Fintype ι] in
theorem one_mem_U : oneI ι a ∈ {M : LieI ι a | IsUnit (Matrix.of M)} := by
  change IsUnit (Matrix.of (Matrix.of.symm 1))
  rw [Equiv.apply_symm_apply]
  exact isUnit_one

theorem orb_rmul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (g : GL (Fin a) (ι → ℂ)) (v : X)
    (M : LieI ι a) : orb ρ (ρ g v) M = orb ρ v (rmulL g.val M) := by
  rw [rmulL_apply]
  unfold orb
  have hiff : IsUnit (Matrix.of (Matrix.of.symm (Matrix.of M * g.val))) ↔ IsUnit (Matrix.of M) := by
    rw [Equiv.apply_symm_apply]
    exact Units.isUnit_mul_units _ g
  by_cases hM : IsUnit (Matrix.of M)
  · rw [dif_pos hM, dif_pos (hiff.mpr hM), ← ContinuousLinearMap.mul_apply, ← map_mul]
    congr 2
    ext1
    simp only [IsUnit.unit_spec, Units.val_mul, Equiv.apply_symm_apply]
  · rw [dite_eq_right hM, dite_eq_right (mt hiff.mp hM)]

theorem orb_lmul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) (M : LieI ι a)
    (hM : IsUnit (Matrix.of M)) (N : LieI ι a) :
    orb ρ v (lmulL (Matrix.of M) N) = ρ hM.unit (orb ρ v N) := by
  rw [lmulL_apply]
  unfold orb
  have hiff : IsUnit (Matrix.of (Matrix.of.symm (Matrix.of M * Matrix.of N))) ↔
      IsUnit (Matrix.of N) := by
    rw [Equiv.apply_symm_apply, ← hM.unit_spec]
    exact Units.isUnit_units_mul _ _
  by_cases hN : IsUnit (Matrix.of N)
  · rw [dif_pos hN, dif_pos (hiff.mpr hN), ← ContinuousLinearMap.mul_apply, ← map_mul ρ]
    congr 2
    ext1
    simp only [IsUnit.unit_spec, Units.val_mul, Equiv.apply_symm_apply]
  · rw [dite_eq_right hN, dite_eq_right (mt hiff.mp hN), map_zero]

omit [Fintype ι] in
theorem orbit_map_intertwiner_comm (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (T : X →L[ℂ] X)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) (v : X) :
    orb ρ (T v) = fun M => T (orb ρ v M) := by
  funext M
  unfold orb
  split_ifs with h
  · exact (hT _ _).symm
  · exact (map_zero T).symm

theorem smooth_vector_intertwiner_apply (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (T : X →L[ℂ] X)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) (v : X) (hv : SmV ρ v) : SmV ρ (T v) := by
  unfold SmV at *
  rw [orbit_map_intertwiner_comm ρ T hT v]
  exact (T.restrictScalars ℝ).contDiff.comp_contDiffOn hv

end SmoothVectorsIntertwiner

open SmoothVectorsIntertwiner in
theorem smooth_vectors_stable_intertwiner : S2 := by
  intro ι _ a X _ _ _ ρ _
  have hU : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := isOpen_U
  have orb_zero : orb ρ (0 : X) = fun _ => 0 := by
    funext M
    unfold orb
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SmV
    rw [orb_zero]
    exact contDiffOn_const
  · intro v w hv hw
    have e : orb ρ (v + w) = fun M => orb ρ v M + orb ρ w M := by
      funext M
      unfold orb
      split_ifs <;> simp
    unfold SmV at *
    rw [e]
    exact hv.add hw
  · intro c v hv
    have h := smooth_vector_intertwiner_apply ρ (c • ContinuousLinearMap.id ℂ X) (fun g x => by simp) v hv
    simpa using h
  · intro g v hv
    unfold SmV at *
    rw [show orb ρ (ρ g v) = fun M => orb ρ v (rmulL g.val M) from
      funext fun M => orb_rmul ρ g v M]
    refine hv.comp (rmulL g.val).contDiff.contDiffOn ?_
    intro M hM
    simp only [Set.mem_setOf_eq, rmulL_apply, Equiv.apply_symm_apply] at hM ⊢
    exact (Units.isUnit_mul_units _ g).mpr hM
  · exact fun T hT v hv => smooth_vector_intertwiner_apply ρ T hT v hv
  · intro v hv
    have hd : ∀ N ∈ {M : LieI ι a | IsUnit (Matrix.of M)}, DifferentiableAt ℝ (orb ρ v) N :=
      fun N hN => (hv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hN)
    refine ⟨fderiv ℝ (orb ρ v) (oneI ι a), (hd _ one_mem_U).hasFDerivAt, fun Z => ?_⟩
    have key : ∀ N (hN : IsUnit (Matrix.of N)),
        ρ hN.unit (fderiv ℝ (orb ρ v) (oneI ι a) Z) =
          fderiv ℝ (orb ρ v) N (rmulL (Matrix.of Z) N) := by
      intro N hN
      have hL : lmulL (Matrix.of N) (oneI ι a) = N := by
        rw [lmulL_apply, oneI, Equiv.apply_symm_apply, mul_one, Equiv.symm_apply_apply]
      have h0 : HasFDerivAt (orb ρ v) (fderiv ℝ (orb ρ v) N) (lmulL (Matrix.of N) (oneI ι a)) := by
        rw [hL]
        exact (hd N hN).hasFDerivAt
      have h1 : HasFDerivAt (fun M => orb ρ v (lmulL (Matrix.of N) M))
          ((fderiv ℝ (orb ρ v) N).comp (lmulL (Matrix.of N))) (oneI ι a) :=
        h0.comp (oneI ι a) (lmulL (Matrix.of N)).hasFDerivAt
      have h2 : HasFDerivAt (fun M => ρ hN.unit (orb ρ v M))
          (((ρ hN.unit).restrictScalars ℝ).comp (fderiv ℝ (orb ρ v) (oneI ι a))) (oneI ι a) :=
        ((ρ hN.unit).restrictScalars ℝ).hasFDerivAt.comp (oneI ι a) (hd _ one_mem_U).hasFDerivAt
      have e : (fun M => orb ρ v (lmulL (Matrix.of N) M)) = fun M => ρ hN.unit (orb ρ v M) :=
        funext fun M => orb_lmul ρ v N hN M
      rw [e] at h1
      have h3 := congrArg (fun D => D Z) (h2.unique h1)
      simpa [lmulL_apply, rmulL_apply] using h3
    unfold SmV
    have hc : ContDiffOn ℝ ∞ (fun N => fderiv ℝ (orb ρ v) N (rmulL (Matrix.of Z) N))
        {M : LieI ι a | IsUnit (Matrix.of M)} :=
      (hv.fderiv_of_isOpen hU (by simp)).clm_apply (rmulL (Matrix.of Z)).contDiff.contDiffOn
    refine hc.congr fun N hN => ?_
    have hw : ∀ w : X, orb ρ w N = ρ (show IsUnit (Matrix.of N) from hN).unit w := by
      intro w
      unfold orb
      exact dif_pos hN
    rw [hw]
    exact key N hN

end PositivityTheory.jumpWindows

end
