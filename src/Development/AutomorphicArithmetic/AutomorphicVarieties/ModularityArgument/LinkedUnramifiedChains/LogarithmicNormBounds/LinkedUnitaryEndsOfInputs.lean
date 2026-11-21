import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.XiAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.NotIrrOfLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.XiArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LamDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.MuRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CoefInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.ChiUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinPtDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AbsMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.OffSelf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.CRealAv

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.J
open private UpperTheory.V.J.oe_big UpperTheory.V.J.oe_res UpperTheory.V.J.oe_modIn from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx

namespace UpperTheory.Gal.projectedFormsSystemPart

def OpenEx2E : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M → Even N →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ → SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A],
    ∃ (c₁ : Coef l) (_ : Fr.IsCoef l c₁.O) (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
      (Λ : LamObj R.r) (J : Ideal R.B₀.B) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (m : ℕ),
      (∀ x ∈ A, x ∈ c₁.O) ∧ Large L c₁ ∧ IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧ R.B₀.Modular ι J Λ ∧ Num R.B₀ Λ J ∧
      Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin m) c₁.O) ∧ R.T.IsPhi φ ∧ Function.Surjective φ ∧ AllGood R.S (J.map φ) ∧
      R.T.DimT J ∧ EndPt R ι φ


end UpperTheory.Gal.projectedFormsSystemPart
