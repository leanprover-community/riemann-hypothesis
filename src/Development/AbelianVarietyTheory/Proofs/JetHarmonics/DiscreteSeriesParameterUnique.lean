module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory
namespace DSInequiv

open PI.DSInfCharCap

section
variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

end DSInequiv
end GlobalTheory
