import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoordsExistsUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels GlobalTheory.ThetaObjCompare
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorusFamilyTheta

theorem matrix_eq_of_im {g : ℕ} {Hm Hm' : Matrix (Fin g) (Fin g) ℂ} {s : Set (Fin g → ℂ)}
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ a ∈ s, ∀ c ∈ s, (hermForm Hm a c).im = (hermForm Hm' a c).im) :
    Hm = Hm' := by
  have k := HermAdjoint.adjoint_of_im (Hm - Hm') LinearMap.id 0 s hs fun a ha c hc => by
    have := h a ha c hc
    simp only [hermForm] at this
    simp [hermForm, Matrix.sub_mulVec, this]
  rw [← sub_eq_zero]
  ext i j
  simpa [hermForm, Pi.star_single] using k (Pi.single i 1) (Pi.single j 1)



end GlobalTheory.TorusFamilyTheta
