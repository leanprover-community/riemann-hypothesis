module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolutionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocyclesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffElStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RingCont

abbrev MC (R : Type) [CommRing R] (F : Shv R) : CommRingCat.{0} ⥤ AbCx := Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F

theorem locVan (R : Type) [CommRing R] (F : Shv R) : ∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : ((MC R F).obj A).X n),
    ((MC R F).obj A).d n (n + 1) z = 0 →
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : ((MC R F).obj B).X (n - 1),
      ((MC R F).obj B).d (n - 1) n y = ((MC R F).map g).f n z := by
  intro n hn A z hz
  obtain ⟨_, cl, -, -, hcl0, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R (Spec A) F n hn (cl (sch.obj (Spec A)) n z hz)
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection A Y f hfe hfs
  refine ⟨B, g, hg, ?_⟩
  obtain ⟨h', hh'⟩ := hpull (sch.obj (Spec B)) (sch.obj (Spec A)) (sch.map (Spec.map g)) n z hz
  have h0 : pull R (sch.map (Spec.map g)) F n (cl (sch.obj (Spec A)) n z hz) = 0 := by
    rw [← hhf, Functor.map_comp, pull_comp, hx, map_zero]
  rw [hh', hcl0] at h0
  obtain ⟨y, hy⟩ := h0
  exact ⟨y, hy.symm⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨ι, hι⟩ := GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles R F
  have hF0 : PreservesFilteredColimitsOfSize.{0, 0} (onRings F ⋙ forget₂ _ AddCommGrpCat.{1}) :=
    ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).1.1 hF)
  exact GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent (MC R F) (onRings F ⋙ forget₂ _ AddCommGrpCat.{1})
    (Functor.whiskerLeft Scheme.Spec.rightOp ι) hF0
    (fun A => hι (op (Spec A)))
    (fun n hn A => (GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F).1 _ n hn)
    (locVan R F)
    (fun A B g hg n => GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F CommRingCat.{0} (Scheme.Spec.rightOp ⋙ sch.op) A _ (coAug g)
      (GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat R A B g hg) n)
    J D c hc n

end GlobalTheory.EtC.RingCont
