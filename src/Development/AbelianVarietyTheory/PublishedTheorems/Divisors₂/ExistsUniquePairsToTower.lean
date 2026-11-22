module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent unitOn)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta)
open ReciprocityTheory.ChartRestriction.G.Out (WeilIs)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R)

variable {G}

end PDivGroup

namespace EpsWeil

variable {R : Type} [CommRing R] (D : Type) [CommRing D] [Algebra R D]

variable {D} in
def epsUnit (b : D) : (DualNumber D)ˣ where
  val := 1 + TrivSqZeroExt.inr b
  inv := 1 - TrivSqZeroExt.inr b
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

variable (R) in
def epsMap : DualNumber R →ₐ[R] DualNumber D :=
  DualNumber.lift ⟨(Algebra.ofId R _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩

variable {D} {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

end EpsWeil

namespace Published

namespace BarsottiTateDieudonne

end BarsottiTateDieudonne

namespace BarsottiTateDieudonne

end BarsottiTateDieudonne

end Published

end GlobalTheory
