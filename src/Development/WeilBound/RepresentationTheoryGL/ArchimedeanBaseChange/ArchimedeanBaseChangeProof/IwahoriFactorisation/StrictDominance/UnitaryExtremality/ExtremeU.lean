import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetEigenvectorExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun

namespace PositivityTheory.SphericalProduct

theorem extremeU : ExtremeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU hA hI hS
  obtain ⟨y, hy, hy1⟩ := GlobalTheory.T.unitary_jacquet_nonzero L ϖ σ q n V ρ α hU hA hI hS
  obtain ⟨y', ξ, hy', heig, h1⟩ := GlobalTheory.T.unitary_jacquet_eigenvector_exists L ϖ σ q n V ρ hU hA y hy hy1
  obtain ⟨lam, hlam0, hne, hlam⟩ := GlobalTheory.T.unitary_equivariant_form L ϖ σ q n V ρ hU hA ξ y' hy' heig h1
  obtain ⟨β, hβ⟩ := GlobalTheory.T.unitary_character_facts L ϖ σ q n V ρ hU ξ y' hy' heig h1
  obtain ⟨hW, f, hf, hfe⟩ := GlobalTheory.T.unitary_frobenius_reciprocity L ϖ σ q n V ρ α hU hA hI hS β lam hlam0 hne
    (fun t ht v => by rw [← hβ t ht]; exact hlam t ht v)
  exact GlobalTheory.T.unitary_chamber_decomposition GlobalTheory.T.unitary_swap_reduction GlobalTheory.T.unitary_inverse_reduction L ϖ σ q n hU V ρ hA hI hS.1 α β hW f hf hfe

end PositivityTheory.SphericalProduct

end
