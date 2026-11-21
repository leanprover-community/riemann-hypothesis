import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementK
import Formalism.GaussJetBounds.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

namespace TwoKernelNormBounds



theorem hasSubst_lin {K : Type} [Field K] {n m : Type} [Fintype n] [Fintype m] (A : n → m → K) :
    MvPowerSeries.HasSubst
      (fun i => (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x : MvPowerSeries m K)) := by
  first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by simp)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by simp [IsNilpotent.zero])
    | exact ⟨fun i => by simp [IsNilpotent.zero], by simp [Filter.cofinite_eq_bot]⟩

theorem linSub_sqSum {K : Type} [Field K] {n m : Type} [Fintype n] [Fintype m] (A : n → m → K)
    (c : n → K) :
    linSub A (sqSum c) =
      ∑ i, MvPowerSeries.C (c i) * (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) ^ 2 := by
  have ha := hasSubst_lin A
  unfold linSub sqSum
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  congr 1
  have h := (MvPowerSeries.substAlgHom ha).commutes (c i)
  simpa [MvPowerSeries.coe_substAlgHom, MvPowerSeries.algebraMap_apply] using h

end TwoKernelNormBounds

open TwoKernelNormBounds




end Formalism.L2.Th1.G
