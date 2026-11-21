import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti

section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureCompact

theorem compactClause : CompactClause := by
  intro G _ _ _ _ _ _ H _ _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  borelize G
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH.isClosed fun h => ?_
  rw [GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact H hH h.2,
    GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact (⊤ : Subgroup H) (by simpa using isCompact_univ)
      (Subgroup.mem_top h)]

end GlobalTheory.QuotientMeasureCompact
end

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSubgroup_quotient_invariant_measure : CompactClause := by
  atlas_forward_decl GlobalTheory.QuotientMeasureCompact.compactClause
