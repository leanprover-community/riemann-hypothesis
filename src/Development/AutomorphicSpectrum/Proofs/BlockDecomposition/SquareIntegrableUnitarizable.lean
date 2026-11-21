import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SqIntUnit

theorem isUnitarisable_of_isSqIntCoeff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : IrrGL k), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  intro k _ _ _ _ x h
  exact GlobalTheory.SqIntUnit.main k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr h

end GlobalTheory.CompanionTheory.SqIntUnit
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_unitarizable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff
