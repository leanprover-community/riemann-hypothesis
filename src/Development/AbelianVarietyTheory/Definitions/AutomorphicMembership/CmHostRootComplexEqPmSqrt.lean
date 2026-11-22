module

public import Mathlib
public import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal

namespace GlobalTheory.ShFam

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section OneLevel

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

end OneLevel

abbrev LocFam (Xo : ∀ l : Level H, Moduli Dw l) : Type 1 :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W

structure Sys (Xo : ∀ l : Level H, Moduli Dw l) : Type 1 where

  Y : LocFam Xo

  clauses : ∀ p W hp hW, N2 (Y p W hp hW) ∧
    ∀ i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3 ∧ (Y p W hp hW i).N4

section Unif

variable {l : Level H}

variable {Xo : Moduli Dw l} {c : Coeff l} {N : ℕ} {ξ : E}

end Unif

end Free

variable {D : D7}

namespace FinalTheorems

variable {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

variable (s : FinalTheorems S κ)

end FinalTheorems

namespace SrcFam

open Formalism.L2.Geo (datW datW_N datW_j)

variable {A : Amb D} (F : SrcFam A)

end SrcFam

end GlobalTheory.ShFam
