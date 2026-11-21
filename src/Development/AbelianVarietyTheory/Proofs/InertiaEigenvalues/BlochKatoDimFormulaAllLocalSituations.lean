import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRingsStatement

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem blochKatoDim_at_every_local_situation : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm12 D := by
  intro D l _ K LL _
  exact GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_dimFormula_all_localSituations : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm12 D := by
  atlas_forward_decl GlobalTheory.blochKatoDim_at_every_local_situation
