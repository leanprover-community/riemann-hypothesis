module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit GlobalTheory.EigenSplit GlobalTheory.HTLat Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

variable {Λ : Type} [CommRing Λ] [StarRing Λ] [Module Λ D.toPre.X] (ιD : D.toPre.OAct Λ)

end Raynaud

namespace Point

open OmegaRank

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

end Point

end GlobalTheory.HTLat

namespace GlobalTheory.LocM

section Field

variable {p : ℕ} (C : SCF p)

variable [Fact p.Prime]

end Field

section Roots

variable {p : ℕ} [Fact p.Prime] {F : IntermediateField ℚ ℂ} {C : Type} [Field C] [IsAlgClosed C]

end Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}

section Fibre

variable (P : PointsOfFlagModel.PtC Y C)

variable [Fact p.Prime]

end Fibre

variable {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P)

variable [Fact p.Prime]

end GlobalTheory.LocM
