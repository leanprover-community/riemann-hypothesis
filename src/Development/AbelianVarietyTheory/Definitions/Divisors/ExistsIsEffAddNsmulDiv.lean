module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)

namespace GlobalTheory.Vert

section Divisor

variable {X : Scheme.{0}}

variable (D D' : EffCartierData X)

end Divisor

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

attribute [instance] Model.isIntegral Model.flat

namespace Model

variable {O} (Z Z₁ Z₂ : Model O)

attribute [instance] Hom.surjective

section Over

variable {Z Z₁} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
include hf

end Over

variable {Z} {F G : Z.X.Modules}

end Model

namespace Model

variable {O} (Z Z₁ : Model O)

variable {Z}

variable (Z)

section Pull

variable {Z Z₁} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
include hf

end Pull

end Model

namespace VertDiv

open Model

variable {O} {Z : Model O} (P P' P'' : VertDiv Z)

variable {P P' P''} {g g' g'' : O} {s : P.M.Sec} {s' : P'.M.Sec} {s'' : P''.M.Sec}

section Pull

variable {Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)

end Pull

end VertDiv

namespace Model

variable {O} {Z : Model O}

end Model

end GlobalTheory.Vert
