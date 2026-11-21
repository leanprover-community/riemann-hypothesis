import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBC0
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfBcPolar

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
theorem UpperTheory.Gal.SV.quad_base_change_w_of_printed_results (_P : _root_.UpperTheory.V.Af.Hypotheses') : UpperTheory.V.Br.QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a ha2 _ π hr
  obtain rfl := ha2.out
  exact (UpperTheory.ConvolutionTheory.R2.quadBC2 F E h2 π hr).imp_right fun ⟨P, hP⟩ => ⟨P, UpperTheory.V.Br.IsBCw.of_isBC hP⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Bc in
theorem UpperTheory.V.Sd.up_quad_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.UpQuad := by
  intro hP F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE n _ hn r hr ⟨π, hreg, hatt⟩ hirr
  obtain ⟨P, hBC⟩ := (_root_.UpperTheory.Gal.SV.quad_base_change_w_of_printed_results hP F E hE n hn π hreg).resolve_left
    fun ⟨η, hη, ht⟩ => _root_.UpperTheory.V.Af.Bc.noTwist_of_prints hP F E Ω l ι hE n r π hr hatt hirr η hη ht
  have h := UpperTheory.V.Br.bcAtt0 F E Ω l ι n r π P hBC.toIsBC0
  exact ⟨P, h.1 hreg, h.2 hatt ((Bc.irrBasic.1 _ Unit _ n _).2.1 hirr)⟩
end
end
