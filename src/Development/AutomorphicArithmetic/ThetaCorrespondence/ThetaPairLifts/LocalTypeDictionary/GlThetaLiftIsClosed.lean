import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinearStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.MingZel

section
section
open MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel PositivityTheory.Tls2.Ming3 PositivityTheory.Rg.Ming
open scoped TensorProduct
namespace UpperTheory.Lit.HoweDuality
theorem thetaLift_gl_of_zelevinsky_classification (hZ : ZelevinskyPolynomialRing) : _root_.GlobalTheory.ThetaLiftGL.ThetaLiftGeneralLinearStatement :=
  fun hBZ _ k _ _ _ _ r t μ V _ _ W _ _ σ π hrt hμs hμu hσs hσi hσu hπs hπi hθ =>
    lift_of_irr k r t μ V W σ π hrt hμs hμu hσu hπs hπi
      (UpperTheory.Lit.Mix.top (GlobalTheory.geometricLemma_of_filtration hBZ GlobalTheory.geometricLemmaFiltration_unconditional) hBZ hZ
        k r t V σ μ hrt hσs hσi hσu hμs hμu) hθ
end UpperTheory.Lit.HoweDuality
end
end

section
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
end
