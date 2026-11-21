import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.LettersPoly

noncomputable section

namespace CompanionTheory.WaveGrid.LimSh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace

variable {P : M.Par} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wq'] {u u' : ℕ → ℝ}


end CompanionTheory.WaveGrid.LimSh
