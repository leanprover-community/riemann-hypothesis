module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.HkFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {S : Scheme.{0}} {s : S ⟶ Sp (KA l)}

namespace IndexZero
open GlobalTheory.HeckeKerModel

theorem lift_closed {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have hs : Surjective (pullback.snd ν x) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩
  have : IsIso (pullback.snd ν x) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

end IndexZero

namespace KerScheme
variable {Xo : Moduli D l} {𝔓 : Ideal (𝓞 E)} {p i : ℕ}

theorem smooth (Z : KerScheme Xo 𝔓 p i) : Smooth (Z.π₁ ≫ Xo.s) := by
  have := Xo.smooth
  have := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := Z.et₁
  infer_instance

theorem isReduced (Z : KerScheme Xo 𝔓 p i) : IsReduced Z.Hk :=
  (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ Z.smooth).1

end KerScheme

end GlobalTheory.HkFam
end
