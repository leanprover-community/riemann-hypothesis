module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)
open GlobalTheory.VB (IsVB IsFrame IsSubbundle Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.Vert

section Dim

attribute [local instance low] specializationOrder

end Dim

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

namespace Model

namespace Hom

variable {Z Z₁ : Model O} (f : Hom Z₁ Z)

end Hom

variable (Z : Model O)

variable {Z} {Z₁ : Model O} {E E' E'' : Z.X.Modules} {r : ℕ}

namespace GenIso

section Pull

variable {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)

end Pull

variable (φ : Z.GenIso E E')

variable (hE : IsVB E r) (hE' : IsVB E' r) (hE'' : IsVB E'' r)

variable {φ} {ψ : E' ⟶ E}

end GenIso

end Model

namespace Flag

variable {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N)

attribute [instance] isIso_last

end Flag

namespace Model

variable {Z : Model O} {E E' : Z.X.Modules} {N : ℕ}

namespace FlagPair

variable {φ : Z.GenIso E E'} (P : FlagPair φ N)

end FlagPair

end Model

end GlobalTheory.Vert
