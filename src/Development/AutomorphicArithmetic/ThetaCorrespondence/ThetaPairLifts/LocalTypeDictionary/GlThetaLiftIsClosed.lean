import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinearStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGlOfZelevinskyClassification

section
section
namespace UpperTheory.Lit.Mix
theorem gl_thetaLift_isClosed : _root_.GlobalTheory.ThetaLiftGL.ThetaLiftGeneralLinearStatement := _root_.UpperTheory.Lit.HoweDuality.thetaLift_gl_of_zelevinsky_classification polynomialRing
end UpperTheory.Lit.Mix
end
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_general_linear : BernsteinZelevinskyFiniteness → BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W), r < t → IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π → π.IsIrreducible → ThetaPair μ σ π → Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  atlas_forward_decl _root_.UpperTheory.Lit.Mix.gl_thetaLift_isClosed
end
