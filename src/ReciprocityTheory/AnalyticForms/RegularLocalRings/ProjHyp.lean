module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypC

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

instance isNoetherian_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    IsNoetherian (projX P hP) :=
  (isNoetherian_iff_of_finite_iSup_eq_top (S := chartOpen hP) (iSup_chartOpen_eq_top hP)).mpr
    (isNoetherianRing_gammaChart hP)

def ptIdealOf {σ : Type} (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)

instance ptIdealOf_isPrime {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsPrime :=
  RingHom.ker_isPrime _

abbrev locAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (ptIdealOf z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I

end

end ReciprocityTheory.AnForm.R
