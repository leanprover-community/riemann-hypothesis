import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjCompactOfAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCVPosIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open GroundTheory.Automorphic.Reduction (maxCompact)

namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def cell (ω : Set (GA E n)) (t₀ : ℝ) (m : Fin n → ℤ) : Set (H E n 0) :=
  {y | ∃ b ∈ ω, ∃ x : Fin n → ℝ, admitted t₀ x ∧ (∀ i, (m i : ℝ) ≤ x i ∧ x i ≤ m i + 1) ∧
    ∃ k ∈ maxCompact (K := E) (n := n), y.1 = b * An.tor E x * k}


end GlobalTheory.CompanionTheory.PiVec

end
