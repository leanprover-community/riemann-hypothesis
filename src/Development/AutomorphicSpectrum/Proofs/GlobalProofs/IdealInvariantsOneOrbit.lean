import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalika

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_multiplication_jacquet_shalika : GlobalTheory.Published.ComplexMultiplicationJSt := by
  first | exact @GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | exact GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | (intros; apply GlobalTheory.CompanionTheory.Published.complexMultiplicationJ <;> assumption)
end

section
namespace GlobalTheory.CompanionTheory.CM

theorem idealInvariantsOneOrbit : GlobalTheory.Published.IdealInvariantsOneOrbitSt :=
  GlobalTheory.Published.ComplexMultiplicationJSt.oneOrbit GlobalTheory.T.complex_multiplication_jacquet_shalika

end GlobalTheory.CompanionTheory.CM
end
