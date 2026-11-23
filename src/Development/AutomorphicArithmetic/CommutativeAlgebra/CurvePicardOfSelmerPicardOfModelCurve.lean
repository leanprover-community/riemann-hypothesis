module

public import Development.EtaleCohomology.EtaleSheaves.LeafPicCut
public import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfCharts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfFiniteExtension
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FinitePicTorsionOfFiniteKummerSelmer
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartsOfIsCurveOfIsUnit
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldFractionRingOfDedekindFiniteType
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.curve_picard_of_selmerPicard_of_modelCurve :
    LateralTheory.E.LeafPicCut.LeafSelPic → LateralTheory.E.LeafCurveVCut.LeafModelCurve → LateralTheory.E.E4.LeafPic := by
  intro hSel hModel hH q _ k B _ _ _ _ _ _ hq
  by_cases hB : IsField B
  · letI := hB.toField
    haveI : Subsingleton (CommRing.Pic B) := inferInstance
    exact Finite.of_subsingleton
  · haveI hK : IsFunctionField k (FractionRing B) := UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType k B hB
    obtain ⟨u, hu, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := FractionRing B)
    obtain ⟨C0, c0, x, ψ, hc, hx, hψ⟩ := hModel k (FractionRing B) u hu hfd
    haveI : IsIntegral C0 := hc.1
    obtain rfl : x = genericPoint C0 := hx.eq (genericPoint_spec C0)
    letI : Algebra k C0.functionField :=
      (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ).hom.toAlgebra
    letI : Algebra (FractionRing B) C0.functionField := (Spec.preimage ψ).hom.toAlgebra
    haveI : IsScalarTower k (FractionRing B) C0.functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have heq : Spec.map (CommRingCat.ofHom (algebraMap k C0.functionField)) =
        C0.fromSpecStalk (genericPoint C0) ≫ c0 := by
      change Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ) = _
      rw [Spec.map_comp, Spec.map_preimage, hψ]
    obtain ⟨hF, hch⟩ := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit hH q k hq c0 hc heq
    haveI := hF
    exact UpperTheory.finite_pic_torsion_of_finite_kummerSelmer hSel k B q
      (UpperTheory.finite_kummerSelmer_of_finite_extension k (FractionRing B) C0.functionField q hq (UpperTheory.finite_kummerSelmer_of_charts k _ q hch))
