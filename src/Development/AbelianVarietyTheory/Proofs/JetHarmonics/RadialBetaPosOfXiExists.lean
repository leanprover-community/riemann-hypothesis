module

public import Formalism.HermitianCurvature.StatementJC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaIntegrandIntegrableOfXiExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

open MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.WeightedFormPos


open Formalism.FourierDecayAlt.P.JCx2 in
theorem radialBetaPos_of_xiExists (hXi : B.XiExists) : JC.RadialBetaPos := by
  apply _root_.Formalism.FourierDecayAlt.P.radial_beta_pos <;> assumption

theorem radialModuleForm_of_xiExists (hXi : B.XiExists) : JC.RadialModuleForm :=
  radial_module_form_of_parts (radialBetaPos_of_xiExists hXi) radial_module_action bessel_function_finite_class
    bessel_module module_regularity

end GlobalTheory.WeightedFormPos
