import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussEveryIntProof
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussEveryOrthOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussOrthOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussIntOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.StructureTheoremCMOfUniformGaussModelsOfHypShape
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.GaussFormCMOfUniformGaussModelsOfHypShape
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NeZeroOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.IntegralOperatorTwoOrthogonal
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussEveryPh
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.EvenDegreeWeightBounds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaKappaShapeOfTransferIntegrality
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussTranslateOfCmCase
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt

namespace Formalism.L2.Th1.Top

theorem calcC : CalcC := CalcC_proof
theorem orthShape : OrthShape := OrthShape_of calcC
theorem orthShapeOne : OrthShapeOne := orthogonal_shape_one_letter
theorem cmDatum : CMDatum := CMDatum_proof
theorem jetsCM : JetsCM := JetsCM_of cmDatum
theorem calcP : CalcP := CalcP_of cmDatum
theorem kappa_integral : uniformGaussModelConditionReformulated := kappa_integral_of_calculation calcC
theorem hypShape : HypShape := HypShape_of calcC

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAEntryInt : ThmAEntryInt := ThmAEntryInt_proof
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAGaussInt : ThmAGaussInt := ThmAGaussInt_proof
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneLetterGaussInt : OneLetterGaussInt := OneLetterGaussInt_proof
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem kernelInt : KernelInt := KernelInt_proof

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem modelInert (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (hmod : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (hd : ¬ l ∣ dK)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (ι : ℂ ≃+* ℂ_[l]) :
    ∃ g2 g3 ε : Formalism.L2.Th1.CM.MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
      ∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS l g2 g3 ε)‖ ≤ 1 :=
  Formalism.L2.Th1.D.FAux.model l Formalism.L2.Th1.CM.cm2 Formalism.L2.Th1.CM.cm3 dK L hsq hmod hcm h5 hd hin ι



theorem thmAEntryEveryOrth : ThmAEntryEveryOrth := ThmAEntryEveryOrth_of orthShape
theorem thmAGaussEveryOrth : ThmAGaussEveryOrth := ThmAGaussEveryOrth_of orthShape
theorem oneLetterGaussEveryOrth : OneLetterGaussEveryOrth := OneLetterGaussEveryOrth_of orthShapeOne
theorem kernelEveryOrth : KernelEveryOrth := KernelEveryOrth_of orthShape
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAEntryOrth : ThmAEntryOrth := ThmAEntryOrth_of thmAEntryEveryOrth
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAGaussOrth : ThmAGaussOrth := ThmAGaussOrth_of thmAGaussEveryOrth
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneLetterGaussOrth : OneLetterGaussOrth := OneLetterGaussOrth_of oneLetterGaussEveryOrth
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem kernelOrth : KernelOrth := KernelOrth_of kernelEveryOrth

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAEntryInt7 : ThmAEntryInt7 := matrix_entries_integral_disc_seven
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAGaussInt7 : ThmAGaussInt7 := gauss_form_integral_disc_seven
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneLetterGaussInt7 : OneLetterGaussInt7 := one_letter_gauss_integral_disc_seven
theorem thmAEntryEveryOrth7 : ThmAEntryEveryOrth7 := ThmAEntryEveryOrth7_of orthShape
theorem thmAGaussEveryOrth7 : ThmAGaussEveryOrth7 := ThmAGaussEveryOrth7_of orthShape
theorem oneLetterGaussEveryOrth7 : OneLetterGaussEveryOrth7 := OneLetterGaussEveryOrth7_of orthShapeOne
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAEntryOrth7 : ThmAEntryOrth7 := ThmAEntryOrth7_of thmAEntryEveryOrth7
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem thmAGaussOrth7 : ThmAGaussOrth7 := ThmAGaussOrth7_of thmAGaussEveryOrth7
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneLetterGaussOrth7 : OneLetterGaussOrth7 := OneLetterGaussOrth7_of oneLetterGaussEveryOrth7

theorem ltNormExists : LTNormExists := lubin_tate_norm_exists
theorem transIntLT : TransIntLT := lubin_tate_transfer_integral
theorem local_kappa_shape_holds : uniformGaussModelConditionReformulated₂ := local_kappa_shape_of_transfer_integrality transIntLT
theorem theta_kappa_shape_holds : uniformGaussModelConditionEquivalent := theta_kappa_shape_of_transfer_integrality transIntLT



end Formalism.L2.Th1.Top
