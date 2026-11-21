import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CbccOfCore
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit

section
theorem UpperTheory.ConvolutionTheory.cbcc_of_unit (h : PositivityTheory.Rg.Tf.Loc.BCFLUnit) : UpperTheory.V.Z.Bc.CBCc :=
  UpperTheory.ConvolutionTheory.T.cbcc_of_core UpperTheory.ConvolutionTheory.ci (UpperTheory.ConvolutionTheory.GM.gm_of_bcfl h)
end

section
theorem UpperTheory.ConvolutionTheory.cbcc : UpperTheory.V.Z.Bc.CBCc :=
  UpperTheory.ConvolutionTheory.cbcc_of_unit PositivityTheory.Rg.Tf.Loc.bcflUnit
end
