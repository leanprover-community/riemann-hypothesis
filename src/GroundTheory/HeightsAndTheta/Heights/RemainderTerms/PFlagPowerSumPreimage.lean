module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ l ∈ Finset.Icc 1 N, g l = ∑ i : Fin N, g (i.val + 1) := by
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1)), hI, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])

theorem FlagPowerSumPreimage.proof : FlagPowerSumPreimage.Statement := by
  intro N T hT
  choose Sf hSf using fun l => Flag.exists_powerSumHom_eq (hT l)
  refine ⟨∑ i : Fin N, X i * Sf (i.val + 1), ?_, ?_⟩

  · rw [sum_Icc_one_eq_sum_fin N (fun l => psum (Fin N) ℚ l * T l), map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, hSf]
    simp [powerSumHom]
  · intro k hk1 hkN
    set j : Fin N := ⟨k - 1, by omega⟩ with hj
    rw [coeff_sum, Finset.sum_eq_single j]
    · rw [coeff_X_mul', if_pos (by simp), tsub_self, ← constantCoeff_eq,
        ← Flag.constantCoeff_powerSumHom, hSf]
      have : j.val + 1 = k := by simp [hj]; omega
      rw [this]
    · intro i _ hij
      rw [coeff_X_mul', if_neg]
      simp only [Finsupp.mem_support_iff, ne_eq]
      rw [Finsupp.single_apply, if_neg (fun h => hij h.symm)]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h

end

end RestTerms

end GroundTheory.Heights₂.Heights
