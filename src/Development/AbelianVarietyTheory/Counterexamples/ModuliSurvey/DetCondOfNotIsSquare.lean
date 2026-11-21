import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetCondCheck



variable {E : Type} [Field E] [NumberField E] [IsCMField E]




theorem nonempty_ringHom (k : Type) [Field k] [CharZero k] [IsAlgClosed k] :
    Nonempty (𝓞 E →+* k) :=
  ⟨((IsAlgClosed.lift : E →ₐ[ℚ] k) : E →+* k).comp (algebraMap (𝓞 E) E)⟩

end GlobalTheory.DetCondCheck
