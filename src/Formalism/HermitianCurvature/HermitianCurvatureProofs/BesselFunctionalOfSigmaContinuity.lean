import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiscreteSeriesFormOneReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiRegOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtomicFormOneReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNonvanishingFromL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FdegOfSchur
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeSS

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem quadConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG)
    (hDD : DecDD) (hBC : BeConv) : More.QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => quadA_of hSch hNIs hNI hGG hDD hBC hIn D hS1 hS2 hbe hbe' hγ,
    quadB_of hNI hGS hGG hDD hIn D hS1 hbe⟩

end Formalism.FourierDecayAlt.P.S3dx4

theorem Formalism.FourierDecayAlt.P.regularity_bundle_from_hypotheses : Formalism.FourierDecayAlt.ThreeDimData.More.MoreOfSteps :=
  fun hSch hNIs hNI hGS hGG hDD hBC _ =>
    ⟨Formalism.FourierDecayAlt.P.S3dx4.phiReg_of hSch hNIs hGG hDD hBC, Formalism.FourierDecayAlt.P.S3dx4.ooConv_of hSch hNIs hNI hGG hDD hBC,
      Formalism.FourierDecayAlt.P.S3dx4.quadConv_of hSch hNIs hNI hGS hGG hDD hBC⟩
end
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.ThreeDimData

theorem shape_true : Shape :=
  DDSmoothness.shape_of psi_constant schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound

theorem k_finite_form : KFinForm :=
  DDSmoothness.kFinForm_of psi_constant bessel_convergence bessel_function_bound

theorem zeroCase_true : ZeroCase :=
  UnipotentHaarMeasurability.zeroCase_of bessel_convergence norm_identity_smooth schur_hermitian

theorem zero_case_discrete_series : ZeroCaseDD :=
  UnipotentHaarMeasurability.zeroCaseDD_of bessel_convergence norm_identity_smooth schur_hermitian

theorem discrete_series_form_one : DDFormOne :=
  discrete_series_form_one_reduction psi_constant schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound double_coset_decomposition bessel_convergence norm_identity_smooth bessel_function_bound shape_true

theorem admissible_atomic_form_one : AtFormAdmOne :=
  admissible_atomic_form_one_reduction schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound
    shape_true k_finite_form zeroCase_true zero_case_discrete_series

theorem orbit_convergence_discrete_series : OrbConvDD :=
  S3dx4.orbConvDD_of_decDD double_coset_decomposition

theorem bessel_nonzero_l2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.bessel_nonzero_l2_reduction schur_hermitian norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence

theorem regularity_and_convergence_bundle : More.PhiReg ∧ More.OOConv ∧ More.QuadConv :=
  regularity_bundle_from_hypotheses schur_hermitian norm_identity_smooth norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence orbit_convergence_discrete_series

theorem orbit_integral_convergence : More.OOConv := regularity_and_convergence_bundle.2.1

theorem quadratic_convergence : More.QuadConv := regularity_and_convergence_bundle.2.2

end Formalism.FourierDecayAlt.P
end
end
