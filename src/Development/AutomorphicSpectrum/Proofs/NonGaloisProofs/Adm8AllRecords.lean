import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.CompanionTheory.TateDualRow

theorem blochKato_dimFormula_all_finiteExt_coeffField : ∀ D : D7, LocalSituation.adm8 D := GlobalTheory.TateDualFil.main

end GlobalTheory.CompanionTheory.TateDualRow
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm8_forall : ∀ D : D7, LocalSituation.adm8 D := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TateDualRow.blochKato_dimFormula_all_finiteExt_coeffField
