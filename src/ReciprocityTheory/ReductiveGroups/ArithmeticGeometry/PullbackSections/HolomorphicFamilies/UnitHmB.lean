import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}







variable (X : Data E r) (x : Frame X.Ψ r)

def cv (τ : X.Ψ) (v : Fin r → E) : Fin r → ℂ := (mat x τ)⁻¹.mulVec (Data.emb τ.1 v)

theorem emb_eq (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (v : Fin r → E) :
    Data.emb τ.1 v = (mat x τ).mulVec (cv X x τ v) := by
  rw [cv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]



end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
