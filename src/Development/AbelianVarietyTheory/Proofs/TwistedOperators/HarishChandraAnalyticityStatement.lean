import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_submodule_dense : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.LeviSubmoduleDense := by
  first | exact @GlobalTheory.LeviDense.leviSubmoduleDense | exact GlobalTheory.LeviDense.leviSubmoduleDense | (intros; apply GlobalTheory.LeviDense.leviSubmoduleDense <;> assumption)
end

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.Published

theorem harishChandraAnalyticity_of_admissible_of_analytic :
    GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic →
      GlobalTheory.Published.HarishChandraAnalyticity :=
  fun hadm han =>
    ⟨fun n ε H _ _ _ π hπ v w hv _ => GlobalTheory.T.admissible_unitary_K_finite.2 han n ε H π hπ v w hv, GlobalTheory.T.levi_submodule_dense hadm han⟩

end GlobalTheory.Published
end

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_analyticity : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.HarishChandraAnalyticity := by
  first | exact @GlobalTheory.Published.harishChandraAnalyticity_of_admissible_of_analytic | exact GlobalTheory.Published.harishChandraAnalyticity_of_admissible_of_analytic | (intros; apply GlobalTheory.Published.harishChandraAnalyticity_of_admissible_of_analytic <;> assumption)
end
