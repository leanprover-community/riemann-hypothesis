module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.KerPull.Kernel

section General

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A A' H : C} [GrpObj A] [GrpObj A']
  {q : A ⟶ A'} [IsMonHom q] {i : H ⟶ A}

theorem mono_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) : Mono i :=
  ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩

def kerLift (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) : W ⟶ H :=
  hp.lift f (toUnit W) (by rw [hf, Hom.one_def])

theorem kerLift_comp (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) :
    kerLift hp f hf ≫ i = f :=
  hp.lift_fst ..

theorem comp_kills (hp : IsPullback i (toUnit H) q η[A']) {W : C} (x : W ⟶ H) : (x ≫ i) ≫ q = 1 := by
  rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]

@[instance_reducible]
def grpObjOfIsKernel (hp : IsPullback i (toUnit H) q η[A']) : GrpObj H :=
  have := mono_of_isKernel hp
  { one := kerLift hp η[A] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    mul := kerLift hp (fst H H ≫ i * snd H H ≫ i) (by
      rw [MonObj.mul_comp, comp_kills hp, comp_kills hp, _root_.mul_one])
    inv := kerLift hp (i ≫ ι[A]) (by
      have e : i ≫ q = 1 := by simpa using comp_kills hp (𝟙 H)
      have h : (i⁻¹ * i) ≫ q = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
      rw [MonObj.mul_comp, e, _root_.mul_one] at h
      exact h)
    one_mul := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (fst (𝟙_ C) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (snd H (𝟙_ C)) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      exact _root_.mul_assoc _ _ _
    left_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact inv_mul_cancel i
    right_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact mul_inv_cancel i }

end General

end GlobalTheory.CompanionTheory.KerPull.Kernel
