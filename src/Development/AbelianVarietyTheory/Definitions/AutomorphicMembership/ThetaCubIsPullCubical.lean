module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullRigIsSymmetric
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensorLB GlobalTheory.HomComb
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomComb

open ReciprocityTheory.ChartRestriction.G.Out

section Transport

variable {X X' W W' Y Y' Y₀ Y₀' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Φ : W' ⟶ W}
  {J K : Type} [Fintype J] [Fintype K] {u : J → (W ⟶ X)} {u' : J → (W' ⟶ X')}

end Transport

variable {S S' : Scheme.{0}} {G A : Over S} {G' A' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
  [GrpObj G'] [IsCommMonObj G'] [GrpObj A'] [IsCommMonObj A'] {J : Type} [Fintype J]

end GlobalTheory.HomComb

namespace GlobalTheory.HermTensor

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

variable {O : Type} [CommRing O] [StarRing O] {M : Type} [AddCommGroup M] [Module O M]
  {a : OAct O G} {b : OAct O A} (t : IsTensor A b G a M) (P : Summand O M) (h : HermForm O M)

instance isMonHom_crd (i : Fin P.n) : IsMonHom (crd t P i) := IsTensor.isMonHom_mapLeft _ _ _

instance isMonHom_biMap [GrpObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z] (q : BIx P.n) :
    IsMonHom (biMap t P h x z q) :=
  isMonHom_psum _ (fun i => by
    have := a.hom
    fin_cases i
    · exact inferInstanceAs (IsMonHom (x ≫ crd t P q.1.1))
    · exact inferInstanceAs (IsMonHom (z ≫ crd t P q.1.2 ≫ a.act (gram P h q.1.1 q.1.2)))) _

def IsAdj (a : OAct O G) (L : LB G.left) : Prop :=
  ∀ c, LBIso (cubeLB G ![fst G G ≫ a.act c, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a.act (star c)] L)

section Laws

variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ s : LB.Gen (Theta G L), s.IsGen) (hadj : IsAdj a L)

end Laws

section Rigid

variable [GrpObj T] [IsCommMonObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z]

end Rigid

section ThetaLaws

variable {L : RigLB G} (c : CubicalStr G L) (hadj : IsAdj a L.L) {w : O} (hw : w + star w = 1)

include c hadj hw

end ThetaLaws

section BaseChange

variable {S' : Scheme.{0}} {G₁ A₁ : Over S'} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj A₁] [IsCommMonObj A₁]
  {a₁ : OAct O G₁} {b₁ : OAct O A₁} (t₁ : IsTensor A₁ b₁ G₁ a₁ M) {f : S' ⟶ S} {φ : G₁.left ⟶ G.left}
  {ψ : A₁.left ⟶ A.left} (hφ : IsLinearPullback a₁ a f φ) (hψ : IsLinearPullback b₁ b f ψ)
  (hm : ∀ m, (t₁.tmul m).left ≫ ψ = φ ≫ (t.tmul m).left)
include hφ hψ hm

end BaseChange

end GlobalTheory.HermTensor
