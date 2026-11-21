import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PlacewiseToOutsideS
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RelativeK1Module
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct Pointwise

section
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]


end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ]
  {N N' : Type} [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N]
  [AddCommGroup N'] [Module R N'] [Module ℂ N'] [IsScalarTower ℂ R N']



end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ] [Fintype κ]

end

theorem UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    Htpy → KoszulExactBelowLengthOfWeaklyRegular :=
  _root_.UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy
