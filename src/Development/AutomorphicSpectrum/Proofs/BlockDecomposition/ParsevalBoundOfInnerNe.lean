import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParsevalBoundMax

noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval

theorem parseval_bound : Ad3.LR.C.ParsB := fun Φ N => by
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Parseval.Max.parseval_bound_max Φ N
  exact ⟨C, fun ε hε hε1 h v hdet => by simpa [Dk] using hC ε hε hε1 h v hdet⟩


example : Ad3.LR.C.ParsB := parseval_bound

end GlobalTheory.CompanionTheory.Parseval
