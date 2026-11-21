import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin

noncomputable section
open NumberField MeasureTheory Matrix Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutGrowth.ApproxId GlobalTheory.GLFin
open scoped ContDiff

namespace GlobalTheory.GLFin.Inhab
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [IsTotallyComplex E] in

theorem contDiffOn_invL : ContDiffOn ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  intro x hx
  have hu : IsUnit (S x) := hx
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (S x) := by simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  have h2 := (T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)).contDiffWithinAt (s := invSet E a)
  refine h2.congr (fun y _ => ?_) ?_ <;> exact congrArg toL (Matrix.nonsing_inv_eq_ringInverse _)
end

theorem cP : Continuous (fun g : GA E a => GeneralLinearGroup.map (pInf E) g) := by
  have h : Continuous (pInf E) := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  exact Continuous.units_map _ (continuous_id.matrix_map h)

omit [IsTotallyComplex E] in

theorem cQ : Continuous (fun g : GA E a => GeneralLinearGroup.map (pFin E) g) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

theorem cF : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

omit [IsTotallyComplex E] in

theorem cd1 (m : ℝ) (L : Lie E a →L[ℝ] Lie E a) : ContDiff ℝ ∞ fun x => bumpR E a m (L x) :=
  (contDiff_bumpR m).comp L.contDiff




end GlobalTheory.GLFin.Inhab
end
