module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveObjFiniteTypeInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteTypeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitLeftFuncAndCechConerveLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactColimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactCongr
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

noncomputable def coAugNat {J : Type} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) :
    (D ⋙ Arrow.leftFunc) ⋙ CosimplicialObject.const CommRingCat.{0} ⟶ D ⋙ CosimplicialObject.cechConerve where
  app j := coAug (D.obj j).hom
  naturality i j f := by
    have h := (CosimplicialObject.augmentedCechConerve.map (D.map f)).w
    exact h

theorem wExact_of_finiteType_iso (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M)
    (hN : PreservesFilteredColimitsOfSize.{0, 0} N)
    (hε : ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A))
    (hM : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) :
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  intro A B g hg
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType A B g hg
  obtain ⟨⟨hU⟩, hX⟩ := GlobalTheory.EtC.isColimit_leftFunc_and_cechConerve_levels J D _ hc
  refine GlobalTheory.EtC.WExactColim.wExact_colimit CommRingCat.{0} N hN J (D ⋙ Arrow.leftFunc)
    (D ⋙ CosimplicialObject.cechConerve) (coAugNat D) (Arrow.leftFunc.mapCocone (Cocone.mk (Arrow.mk g) ι))
    (CosimplicialObject.cechConerve.mapCocone (Cocone.mk (Arrow.mk g) ι)) (coAug g) hU (fun k => hX k) ?_ ?_
  · intro j
    have h := (CosimplicialObject.augmentedCechConerve.map (ι.app j)).w
    exact h.symm
  · intro j
    obtain ⟨hj, hl, hr⟩ := hD j
    refine (GlobalTheory.EtC.wExact_congr CommRingCat.{0} _ _ (coAug (D.obj j).hom) N M ε (hε _ hl) (fun k => hε _ ?_)).2
      (hM _ _ _ hj)
    exact GlobalTheory.cechConerve_obj_finiteType_int _ _ (D.obj j).hom hr k

end GlobalTheory.EtC
