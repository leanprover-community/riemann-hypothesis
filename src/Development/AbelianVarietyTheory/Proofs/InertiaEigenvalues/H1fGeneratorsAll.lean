import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLattice

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem h1f_generators_of_record : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  intro D l _ K LL _ T _
  exact GlobalTheory.T.h1f_generated_lattice l (D.loc l) (D.locA l) (D.locT l) K LL T

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm13 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  atlas_forward_decl GlobalTheory.h1f_generators_of_record
