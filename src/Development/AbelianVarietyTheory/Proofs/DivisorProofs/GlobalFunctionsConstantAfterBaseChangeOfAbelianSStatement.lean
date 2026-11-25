module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

theorem _root_.GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → UConst A.hom := by
  first | exact @GlobalTheory.AbCoh.uConst_of_isAbelianScheme
