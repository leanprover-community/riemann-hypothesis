import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdeles
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuples
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Assemble

section
namespace PositivityTheory.SiegelWeilFormula.KWhit

theorem sdEx : SdEx := by
  intro F E _ _ _ _ _ σ hcm M J hJ ψ hψ n
  exact ⟨GlobalTheory.T.exists_selfdual_measure_hermitian_tuples F E σ hcm M J hJ ψ hψ n, GlobalTheory.T.exists_selfdual_measure_hermitian_adeles F E σ hcm ψ hψ n⟩

end PositivityTheory.SiegelWeilFormula.KWhit
end

section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem relEx_of (hA : RelAlg) (hS : SdEx) (hR : ThetaDictR.RelRealP) : RelEx := by
  intro _ _ F E _ _ _ _ _ σ d R Φ _ P gf hP x t u hx T hTnd
  obtain ⟨η, hOf, hη, hherm, hof, haniso, hcm, hJ, hTT⟩ := hA F E σ d
  obtain ⟨T₀, hrat, hTdh, hTdd⟩ := hTT T hTnd
  obtain ⟨θ, fr, g, l, εs, Φg, Φf, Φv, hth, hfr, hg, hΦg, hεs, hchr, hpl, hfrm, hpf, hpr⟩ :=
    hR F E σ d R Φ P gf hP x t u hx η hη hherm
  obtain ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ := hS F E σ hcm d.m (Jd d η) hJ d.B.ψ hchr d.n
  exact ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, ⟨hx, hrat, hη, hherm, hof, hth, hfr, hg⟩, hΦg, haniso, hεs,
    hcm, hJ, hTdh, hTdd, hchr, hpl, hfrm, hpf, hpr, hμ, hν⟩

theorem relEx : RelEx := relEx_of relAlg_pf sdEx ThetaDictR.relReal

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
