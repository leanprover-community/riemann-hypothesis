module

public import Development.EtaleCohomology.CohomologicalPurity.LeafRelPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

section
variable (R : Type) [CommRing R]

instance pcFreeP : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} R)) :=
    inferInstance
  unfold freeP; infer_instance

instance pcFree : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

instance pcWhisk : PreservesColimitsOfShape WalkingSpan ((SimplicialObject.whiskering _ _).obj (free R)) := by
  unfold SimplicialObject.whiskering; infer_instance

instance preservesSpanColimitsFaceMapComplex : PreservesColimitsOfShape WalkingSpan (AlgebraicTopology.alternatingFaceMapComplex (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => ?_)
  have e : AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation _ _).obj (op (SimplexCategory.mk n)) :=
    NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
      dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_natIso e.symm

instance pcExt : PreservesColimitsOfShape WalkingSpan
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i => ?_)
  by_cases h : ∃ j, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have e : ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ i ≅
        HomologicalComplex.eval _ _ j :=
      NatIso.ofComponents (fun K => K.extendXIso _ hj) (fun f => by
        change (HomologicalComplex.extendMap f _).f i ≫ _ = _ ≫ f.f j
        rw [HomologicalComplex.extendMap_f _ _ hj]; simp)
    exact preservesColimitsOfShape_of_natIso e.symm
  · refine Functor.preservesColimitsOfShape_of_isZero _ ?_ _
    rw [Functor.isZero_iff]
    intro K
    exact K.isZero_extend_X _ i (fun j hj => h ⟨j, hj⟩)

instance pcChains : PreservesColimitsOfShape WalkingSpan (chains R) := by
  unfold chains chainsN; infer_instance

end

theorem LeafChPush_of : LeafChPush := by
  intro q P
  set_option synthInstance.maxHeartbeats 200000 in
    have h : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout _ _
    exact (chains (ZMod q)).map_isPushout h

end LateralTheory.CohomologicalPurity.TubeCut
