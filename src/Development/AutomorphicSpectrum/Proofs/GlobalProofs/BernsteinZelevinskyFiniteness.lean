import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredient

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_smooth_admissible_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.IrreducibleAdmissible k := by
  first | exact @GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | (intros; apply GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_induction_contragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.inductionContragredient | exact GlobalTheory.CompanionTheory.Glob.inductionContragredient | (intros; apply GlobalTheory.CompanionTheory.Glob.inductionContragredient <;> assumption)
end

section
namespace GlobalTheory.CompanionTheory.Published

theorem bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  fun k _ _ _ _ => ⟨GlobalTheory.T.irreducible_smooth_admissible_GL k, GlobalTheory.T.jacquet_module_finite_length k, GlobalTheory.T.parabolic_induction_finite_length k, GlobalTheory.T.parabolic_induction_contragredient k⟩

end GlobalTheory.CompanionTheory.Published
end
