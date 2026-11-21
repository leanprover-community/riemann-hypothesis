import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.CompanionTheory.AdmSix

theorem adm6_all : ∀ D : D7, LocalSituation.adm6 D := GlobalTheory.FundCont.fundamentalExactSequence_continuity_all_theories

end GlobalTheory.CompanionTheory.AdmSix
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm6_of_D7 : ∀ D : D7, LocalSituation.adm6 D := by
  atlas_forward_decl GlobalTheory.CompanionTheory.AdmSix.adm6_all
