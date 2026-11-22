module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompatStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSetStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSectionStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpanStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.FlatBC

section Alg

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

end Alg

section Sch

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

variable {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

end Sch

theorem btOrder_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) :=
  PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange

end GlobalTheory.CompanionTheory.Ar.BT.FlatBC
