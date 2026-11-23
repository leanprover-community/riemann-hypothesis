module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreCriterion
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocalDepthTwo
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Imports
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one (B : Type*) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (h : ringKrullDim B ≤ 1) : IsRegularLocalRing B := by
  by_cases hf : IsField B
  · let := hf.toField
    infer_instance
  · have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    have hm : maximalIdeal B ≠ ⊥ := fun hm => hf (isField_iff_maximalIdeal_eq.mpr hm)
    have h3 : IsIntegrallyClosed B ∧ ∃! P : Ideal B, P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, maximalIdeal B, ⟨hm, inferInstance⟩, fun P ⟨hP, hPp⟩ =>
        IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)⟩
    have hdvr : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hf).out 1 4).mpr h3
    infer_instance

theorem SerreCriterion.proof (hS : NormalLocalDepthTwo.Statement) (hN : SerreNormalOfRegularDepth.Statement) :
    SerreCriterion.Statement := by
  intro A _ hA
  refine ⟨fun h => ⟨fun P _ hdim => ?_, fun P _ => ?_⟩, fun h => hN A hA h.1 h.2⟩
  · obtain ⟨hd, hi⟩ := h P
    exact isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _ (by exact_mod_cast hdim)
  · obtain ⟨hd, hi⟩ := h P
    exact hS _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
