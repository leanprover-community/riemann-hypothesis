import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtDelta
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtCompact
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtNonInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace ExtInhabitants

def c0 : Fin (flatAtlas 1).n := ⟨0, Nat.one_pos⟩






def exZdz : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ := fun _ y => y 0

end ExtInhabitants

open ExtInhabitants




end

end GroundTheory.Heights₂.Heights.EffectiveHS
