import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.WeilBound.CoreStatements.HodgeTatePoints.EigFrob

section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eig_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) :=
  PositivityTheory.HtPt.Ci.eig_frob

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist
