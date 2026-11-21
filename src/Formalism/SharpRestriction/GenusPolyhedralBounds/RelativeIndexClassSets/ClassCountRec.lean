import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCount
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ParOfEqBase
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FibreRankGat
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup

noncomputable section

namespace Formalism.MainNotions.Gaps.CC

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab Formalism.MainNotions.StandardLattice Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

structure ClsTie (D : D7) where

  pz : D.what₂.Word → 𝓞 D.host.E

  piG : Fin 2 → 𝓞 D.host.E
  hyp : ∀ u, LevHyp D.host (D.mem u).A.T (pz u) piG

  P : D.what₂.Word → Par D.host.F D.host.E D.R.k
  charpoly_eq_of_isIso : ∀ u, P u = hostPar D.host (D.mem u).A.T (pz u) piG
  S : ∀ u, (P u).Splits
  e : ∀ u, (D.mem u).C.cls 0 ≃ (P u).Cls (S u)

section Rec

variable {D : D7}


theorem card_classes_level_zero (X : ClsTie D) (u : D.what₂.Word) :
    (Nat.card ((D.mem u).C.cls 0) : ℝ) =
      massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  rw [Nat.card_congr (X.e u), classCount_par D.host (D.mem u).A.T (X.pz u) X.piG (X.hyp u) (X.P u) (X.charpoly_eq_of_isIso u) (X.S u)]
  rfl

theorem class_number_of_class_data (X : ClsTie D) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := fun _ _ u _ => card_classes_level_zero X u











end Rec

section Base

variable {R : Ranks} (H : Host R) (T0 : ℕ) [hT0 : Fact T0.Prime] (pz0 : 𝓞 H.E)
  (hpz0 : (pz0 : H.E) * H.conj (pz0 : H.E) = (T0 : H.E))



end Base

end Formalism.MainNotions.Gaps.CC

end
