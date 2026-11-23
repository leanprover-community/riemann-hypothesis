module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem enat_eq_two_of_le_of_lt {x : ℕ∞} (h2 : 2 ≤ x) (h3 : x < 3) : x = 2 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h3 (by simp)
  | coe n =>
    have a : 2 ≤ n := by exact_mod_cast h2
    have b : n < 3 := by exact_mod_cast h3
    have : n = 2 := by omega
    subst this; rfl

private theorem enat_le_one_of_add_one_le_two {x : ℕ∞} (h : x + 1 ≤ 2) : x ≤ 1 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h (by simp)
  | coe n =>
    have : n + 1 ≤ 2 := by exact_mod_cast h
    exact_mod_cast (omega : n ≤ 1)

theorem LocalDomainDimTwo.proof : LocalDomainDimTwo.Statement := by
  intro A _ _ _ _ hno hQ
  obtain ⟨Q, hQp, h0, hQm⟩ := hQ
  have := hQp
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm
  have hm2 : (2 : ℕ∞) ≤ (IsLocalRing.maximalIdeal A).height :=
    le_trans (by rw [← one_add_one_eq_two]; exact add_le_add (le_trans le_add_self e1) le_rfl) e2
  have hm3 : (IsLocalRing.maximalIdeal A).height < 3 := by
    by_contra h3
    have hle : ((3 : ℕ) : ℕ∞) ≤ Order.height (IsLocalRing.closedPoint A) := by
      rw [← PrimeSpectrum.height_eq_orderHeight]
      exact not_lt.mp h3
    obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height _ hle
    have s0 := p.step ⟨0, by omega⟩
    have s1 := p.step ⟨1, by omega⟩
    have s2 := p.step ⟨2, by omega⟩
    have e01 : (Fin.succ (⟨0, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨1, by omega⟩ := Fin.ext rfl
    have e12 : (Fin.succ (⟨1, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨2, by omega⟩ := Fin.ext rfl
    have e2l : (Fin.succ (⟨2, by omega⟩ : Fin p.length)) = Fin.last p.length := Fin.ext (by simp [hlen])
    rw [e01] at s0
    rw [e12] at s1
    rw [e2l] at s2
    have hl : p.toFun (Fin.last p.length) = IsLocalRing.closedPoint A := hlast
    rw [hl] at s2
    refine hno (p.toFun (Fin.castSucc ⟨1, by omega⟩)).asIdeal (p.toFun (Fin.castSucc ⟨2, by omega⟩)).asIdeal
      (p.toFun _).isPrime (p.toFun _).isPrime ?_ ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s1)
      ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s2)
    exact lt_of_le_of_lt bot_le ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s0)
  have hm : (IsLocalRing.maximalIdeal A).height = 2 := enat_eq_two_of_le_of_lt hm2 hm3
  refine ⟨?_, hm, ?_⟩
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm]
    rfl
  · intro Q' hQ' h0' hQm'
    have := hQ'
    have f1 := Ideal.height_add_one_le_of_lt_of_isPrime h0'
    have f2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm'
    rw [hm] at f2
    exact le_antisymm (enat_le_one_of_add_one_le_two f2) (le_trans le_add_self f1)

end GroundTheory.Heights₂.Heights.NumbersDVR
