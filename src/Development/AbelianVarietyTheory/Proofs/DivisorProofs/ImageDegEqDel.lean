import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt

section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_image_birational_linearSystem_eq_selfInt : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → 0 < S.del ∧ (hilbertDegree S.imageIdeal : ℤ) = S.del ∧ ringKrullDim (MvPolynomial (Fin S.N) F ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  first | exact @GlobalTheory.ImageDegree.degree_image_eq_topSelf | exact GlobalTheory.ImageDegree.degree_image_eq_topSelf | (intros; apply GlobalTheory.ImageDegree.degree_image_eq_topSelf <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.ImageDegree

theorem imageDeg_eq_del : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → (CompHt.imageDeg ev T.D : ℤ) = T.del := by
  intro hQ F _ _ T V Ω _ _ _ _ _ _ Nm W ev hG hB hP
  obtain ⟨-, hdeg, hdim⟩ := GlobalTheory.T.degree_image_birational_linearSystem_eq_selfInt hQ F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨f, hf, -⟩ := hQ.chowInt F T.N T.D T.imageIdeal T.toLinSys.isHomogeneous_imageIdeal
    (GlobalTheory.Adelic.HeightExists.isPrime_imageIdeal hG.alg.variety) hdim
  rw [hP.imageDeg_eq hf]
  exact hdeg

end GlobalTheory.HSCore.ImageDegree
end
end
