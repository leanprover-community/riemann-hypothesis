module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Comma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isColimit_leftFunc_and_cechConerve_levels :
    ∀ (J : Type) [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) (c : Cocone D), IsColimit c →
      Nonempty (IsColimit (Arrow.leftFunc.mapCocone c)) ∧
      ∀ k : SimplexCategory, Nonempty (IsColimit ((CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k).mapCocone c)) := by
  intro J _ D c hc
  refine ⟨⟨isColimitOfPreserves Arrow.leftFunc hc⟩, fun k => ⟨?_⟩⟩
  have e : (CosimplicialObject.cechConerve ⋙ (evaluation SimplexCategory CommRingCat.{0}).obj k) =
      CosimplicialObject.augmentedCechConerve ⋙ CosimplicialObject.Augmented.drop ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k := rfl
  rw [e]
  have h1 : PreservesColimitsOfSize.{0, 0} (CosimplicialObject.augmentedCechConerve (C := CommRingCat.{0})) :=
    CosimplicialObject.cechConerveAdjunction.leftAdjoint_preservesColimits
  have h0 : PreservesColimitsOfShape J (CosimplicialObject.const CommRingCat.{0}) :=
    preservesColimitsOfShape_of_evaluation _ J fun m => by
      have : PreservesColimitsOfShape J (𝟭 CommRingCat.{0}) := inferInstance
      exact this
  have h2 : PreservesColimitsOfShape J (CosimplicialObject.Augmented.drop (C := CommRingCat.{0})) :=
    Comma.preservesColimitsOfShape_snd
  have h3 : PreservesColimitsOfShape J ((evaluation SimplexCategory CommRingCat.{0}).obj k) := inferInstance
  exact @isColimitOfPreserves _ _ _ _ _ _ _ ((evaluation SimplexCategory CommRingCat.{0}).obj k) _
    (isColimitOfPreserves CosimplicialObject.Augmented.drop
      (isColimitOfPreserves CosimplicialObject.augmentedCechConerve hc)) h3.preservesColimit

end GlobalTheory.EtC
