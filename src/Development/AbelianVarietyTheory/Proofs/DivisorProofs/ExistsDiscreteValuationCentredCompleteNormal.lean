module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivVal

theorem exists_valuation_centre (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) :
    ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)),
      (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧
        ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  classical
  haveI : IsNoetherianRing V := hV.1
  by_cases hm : maximalIdeal V = ⊥
  · refine ⟨1, fun v => ?_, fun v hv => ?_⟩
    · by_cases h : algebraMap V (FractionRing V) v = 0
      · simp [h]
      · simp [Valuation.one_apply_of_ne_zero h]
    · rw [hm, Ideal.mem_bot] at hv
      simp [hv]
  · obtain ⟨T, hT, g, hg, hc⟩ := GlobalTheory.GoodVal.exists_dvr_centre (R := V) (K := FractionRing V)
      (L := FractionRing V) (maximalIdeal V) hm
    have hg' : ∀ v : V, algebraMap T (FractionRing V) (g v) = algebraMap V (FractionRing V) v := fun v => by
      simpa using congrArg (fun f => f v) hg
    have hne : maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
    let P : IsDedekindDomain.HeightOneSpectrum T := ⟨maximalIdeal T, inferInstance, hne⟩
    refine ⟨P.valuation (FractionRing V), fun v => ?_, fun v hv => ?_⟩
    · rw [← hg']
      exact P.valuation_le_one (g v)
    · rw [← hg']
      refine (P.valuation_lt_one_iff_mem (g v)).2 ?_
      show g v ∈ maximalIdeal T
      rw [← Ideal.mem_comap, hc]
      exact hv

end GlobalTheory.DivVal
