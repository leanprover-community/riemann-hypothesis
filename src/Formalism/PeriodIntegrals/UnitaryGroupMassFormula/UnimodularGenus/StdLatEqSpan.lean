module

public import Formalism.PeriodIntegrals.UnimodGenus
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

noncomputable section

namespace PI.UG.W

theorem hStd_apply (E : Type) [Field E] [StarRing E] (n : ℕ) (x y : Sp E n) :
    hStd E n x y = ∑ i, star (x i) * y i := rfl

theorem hStd_isSymm (E : Type) [Field E] [StarRing E] (n : ℕ) : (hStd E n).IsSymm := by
  refine LinearMap.isSymm_def.mpr fun x y => ?_

  rw [hStd_apply, hStd_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star, mul_comm]

theorem star_mem_range (E : Type) [Field E] [NumberField E] [StarRing E] (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  exact ⟨⟨star (algebraMap (𝓞 E) E r), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

def eStd (E : Type) [Field E] (n : ℕ) (i : Fin n) : Sp E n := Pi.single i 1

theorem hStd_eStd (E : Type) [Field E] [StarRing E] (n : ℕ) (i j : Fin n) :
    hStd E n (eStd E n i) (eStd E n j) = if i = j then 1 else 0 := by
  rw [hStd_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [eStd, hk]) (by simp)]
    simp [eStd]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [eStd, Ne.symm h]
    · simp [eStd, Pi.single_apply, hk]

end PI.UG.W
