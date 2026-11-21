import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionForStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase

section
namespace GlobalTheory.Published

theorem arDegree_of_heightProjection : HeightProjection → ChernDegreeComplex → ArDegree :=
  fun H H' => ⟨arBirational_of_arProj (GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula H), GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case H'⟩

end GlobalTheory.Published
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectionFormulaAndChernDegree_of_heightProjection : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ArDegree := by
  first | exact @GlobalTheory.Published.arDegree_of_heightProjection | exact GlobalTheory.Published.arDegree_of_heightProjection | (intros; apply GlobalTheory.Published.arDegree_of_heightProjection <;> assumption)
end
