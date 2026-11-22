module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem repr_map_baseChange {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (s : WCb l →ₗ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T)
    (y : WCb l ⊗[ℤ_[l]] T) (i : Fin d) :
    (b.baseChange (WCb l)).repr (TensorProduct.map s r y) i =
      ∑ n, algebraMap ℤ_[l] (WCb l) (LinearMap.toMatrix b b r i n) * s ((b.baseChange (WCb l)).repr y n) := by
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul,
      ← congrFun (LinearMap.toMatrix_mulVec_repr b b r t) i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.Basis.baseChange_repr_tmul, map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  | add y z hy hz =>
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hy, hz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [map_add (f := _), Finsupp.add_apply, mul_add]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

end GlobalTheory.BSP
