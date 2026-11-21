import Formalism.HermitianCurvature.LatticeHerglotzBound

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ChainAndRowSums

open Formalism.FourierDecayAlt.crystallineComparison


theorem cm_one {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) : chainMat Wd c 1 = c 1 := by
  simp [chainMat]





end Formalism.FourierDecayAlt.P.ChainAndRowSums

