module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (thick thickObj thickMap thickTrans)
open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf (hMap sE)
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor GlobalTheory.Vert GlobalTheory.FormalPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

section Classes

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

variable {G}

variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace tens

variable {X X' : Scheme.{0}} (t : SAB H X) (Λ : Unim E)

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

end tens

section MapRight

variable {S S' : Scheme.{0}} {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
  {G G' A A' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj A] [IsCommMonObj A]
  [GrpObj A'] [IsCommMonObj A'] {G₁ G₁' A₁ A₁' : Over S'} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₁'] [IsCommMonObj G₁']
  [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₁'] [IsCommMonObj A₁']
  {a : OAct O G} {a' : OAct O G'} {b : OAct O A} {b' : OAct O A'} {a₁ : OAct O G₁} {a₁' : OAct O G₁'} {b₁ : OAct O A₁}
  {b₁' : OAct O A₁'}

end MapRight

section Thick

variable {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)

end Thick

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t) (Λ : Unim E)

def abPartAct : OAct (𝓞 E) U.D.toPre.P.A := letI := H.starRing; ofRingAct U.oD.onB.toRingAct

end Unif

section Point

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) (Λ : Unim E)

variable {X : Scheme.{0}} {π : X ⟶ Y.X} {t : SAB H X} (m : SABMap t Y.t π) (z : Sp ↥(intO ↥C.S) ⟶ X) (hz : z ≫ π = P.yt)

end Point

section Generic

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} (Z : Mdl Y i₀)

end Generic

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

variable (ct : At S κ p) (Λ : (uniTrue ct).Unim)

end Record

end GlobalTheory.LocM
