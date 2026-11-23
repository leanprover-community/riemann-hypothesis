module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotRing.proof : LocalQuotRing.Statement.{u} := by
  intro R _ P U _ hP hPU
  have hdisj : Disjoint (U.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun x hx hxP => hx (hPU hxP)
  have hPS : (P.map (algebraMap R (Localization.AtPrime U))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) P hP hdisj
  have hker : (P.map (algebraMap R (Localization.AtPrime U))).comap
      (algebraMap R (Localization.AtPrime U)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) hP hdisj
  haveI := hPS
  have hdom : IsDomain (localQuot P U) := Ideal.Quotient.isDomain _
  have hloc : IsLocalRing (localQuot P U) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : U.map (localQuotMap P U) = IsLocalRing.maximalIdeal (localQuot P U) := by
    rw [localQuotMap, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨hdom, hloc, fun y => ?_, fun x => ?_⟩
  · rw [hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  · rw [localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hker]

end GroundTheory.Heights₂.Heights.NumbersDVR
