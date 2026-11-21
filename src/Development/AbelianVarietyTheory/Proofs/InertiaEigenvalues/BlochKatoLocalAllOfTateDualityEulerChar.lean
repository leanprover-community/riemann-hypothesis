import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllPrimesOfBlochKato

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂

theorem aux_of_blochKato_tateDuality_eulerChar₂ :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ D : D7, LocalSituation.Conclusion5 D :=
  GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato

end GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.Conclusion5 D := by
  atlas_forward_decl GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂
