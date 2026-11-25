module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  first | exact @GlobalTheory.PsiRing.exists_basis_fibNZ
