module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.KerPull.Kernel

section General

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A A' H : C} [GrpObj A] [GrpObj A']
  {q : A ⟶ A'} [IsMonHom q] {i : H ⟶ A}

def kerLift (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) : W ⟶ H :=
  hp.lift f (toUnit W) (by rw [hf, Hom.one_def])

theorem kerLift_comp (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) :
    kerLift hp f hf ≫ i = f :=
  hp.lift_fst ..

end General

end GlobalTheory.CompanionTheory.KerPull.Kernel
