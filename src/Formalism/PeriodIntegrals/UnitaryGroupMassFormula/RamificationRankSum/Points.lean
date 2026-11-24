module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

theorem mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ζ.asIdeal ∈ (maximalIdeal O).primesOver ↥(As O A) := by
  haveI := ζ.isMaximal
  refine ⟨inferInstance, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) ζ.asIdeal)).symm

theorem isMaximal_of_mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] {q : Ideal ↥(As O A)}
    (hq : q ∈ (maximalIdeal O).primesOver ↥(As O A)) : q.IsMaximal := by
  obtain ⟨hp, hl⟩ := hq
  have h : q.under O = maximalIdeal O := hl.over.symm
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) q
    (h ▸ IsLocalRing.maximalIdeal.isMaximal O)

noncomputable def ptsEquiv (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] :
    Pts O A ≃ (maximalIdeal O).primesOver ↥(As O A) where
  toFun ζ := ⟨ζ.asIdeal, mem_primesOver O A ζ⟩
  invFun q := ⟨q.1, isMaximal_of_mem_primesOver O A q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ptsEquiv_apply (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ((ptsEquiv O A ζ : (maximalIdeal O).primesOver ↥(As O A)) : Ideal ↥(As O A)) = ζ.asIdeal := rfl

theorem finite_pts (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] : Finite (Pts O A) := by
  classical
  haveI : Finite ((maximalIdeal O).primesOver ↥(As O A)) := by
    have hfin : ((maximalIdeal O).primesOver ↥(As O A)).Finite :=
      Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)
    exact hfin.to_subtype
  exact Finite.of_equiv _ (ptsEquiv O A).symm

end PI.UnitaryGroupMassFormula.EfRankSum
