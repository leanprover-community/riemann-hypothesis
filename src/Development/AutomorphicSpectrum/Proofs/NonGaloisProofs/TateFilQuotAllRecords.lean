import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDeRhamFiltrationQuotientInvariants

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.CompanionTheory.TateFilQuotRow

theorem adm5_all : ∀ D : D7, LocalSituation.adm5 D := GlobalTheory.TateFilQuot.tate_fil_quot

end GlobalTheory.CompanionTheory.TateFilQuotRow
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm5_of_D7 : ∀ D : D7, LocalSituation.adm5 D := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TateFilQuotRow.adm5_all
