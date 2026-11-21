import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
import Formalism.GaussJetBounds.GaussJetProofs.MfactEqProdUniv
import Formalism.GaussJetBounds.GaussJetProofs.OneRow
import Formalism.GaussJetBounds.GaussJetProofs.FirstRowMinorDegreeLeOne
import Formalism.GaussJetBounds.GaussJetProofs.IntegralOperatorsOnJets
import Formalism.GaussJetBounds.GaussJetProofs.GaussB

universe u

namespace Formalism.DworkPowerSeriesWeights

theorem thmB : ThmB.{u} := theorem_B
theorem intOp : IntOp.{u} := by
  unfold IntOp
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro κ _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)



end Formalism.DworkPowerSeriesWeights
