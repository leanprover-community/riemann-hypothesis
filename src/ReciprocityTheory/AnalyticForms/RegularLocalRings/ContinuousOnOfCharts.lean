module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

attribute [local instance] WData.lft

variable (w : WData P D hP)

end WData

end

end ReciprocityTheory.AnForm.R
