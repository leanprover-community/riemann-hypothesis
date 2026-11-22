module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.Points GlobalTheory.CovTest

namespace GlobalTheory.VdmRec

section Free

variable {k : Type} [CommRing k] {X : Scheme.{0}} {ι : Type} [Fintype ι]

abbrev clo (z : X) : Closeds X := ⟨closure {z}, isClosed_closure⟩

instance isIntegral_clo (z : X) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
  isIntegral_red (Z := clo z) isIrreducible_singleton.closure

namespace FlagSp

variable {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} (F : FlagSp E r) {h : VMetric p E r}

end FlagSp

end Free

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal
open GlobalTheory.LieVB (omega unitSec dUnit)

namespace DRBase

attribute [instance] int cl

variable {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c)

end DRBase

end GlobalTheory.VdmRec

end
