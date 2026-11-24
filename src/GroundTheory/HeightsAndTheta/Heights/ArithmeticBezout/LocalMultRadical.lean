module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem map_eq_maximalIdeal_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} [W.IsPrime]
    (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) :
    J.map (algebraMap A (Localization.AtPrime W)) = IsLocalRing.maximalIdeal (Localization.AtPrime W) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W),
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W J hW,
    ← IsLocalization.map_radical W.primeCompl (Localization.AtPrime W) J, hJ.radical]

theorem localMult_eq_one_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} (hJ : J.IsRadical)
    (hW : W ∈ J.minimalPrimes) : localMult J W = 1 := by
  have hWp : W.IsPrime := hW.1.1
  unfold localMult
  rw [dite_eq_left hWp, map_eq_maximalIdeal_of_isRadical hJ hW]
  have : IsSimpleModule (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one]
  rfl

theorem fundCycle_apply_of_isRadical {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) R)} (hJ : J.IsRadical) {W : Ideal (MvPolynomial (Fin n) R)}
    (hW : W ∈ (fundCycle J).support) : fundCycle J W = 1 := by
  classical
  have hval : fundCycle J W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  unfold fundCycle
  rw [Finsupp.onFinset_apply, if_pos hrel]
  exact localMult_eq_one_of_isRadical hJ hrel.1

end GroundTheory.Heights₂.Heights
