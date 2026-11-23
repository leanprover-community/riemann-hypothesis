module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeComplexRadical
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Nullstellensatz
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem ComplexFormsOnPoints.proof (hR : PrimeComplexRadical.Statement)
    (hM : ComplexMinimalPrimesContract.Statement) : ComplexFormsOnPoints.Statement := by
  intro K _ ι _ P hP hrel F hF
  have hrad := hR (Σ k, ι k) P hP
  apply hrad
  rw [← Ideal.sInf_minimalPrimes]
  refine Ideal.mem_sInf.2 fun {Q} hQ => ?_
  have hQp : Q.IsPrime := hQ.1.1
  have hc := hM (Σ k, ι k) P hP Q hQ
  choose i hi using hrel

  let h0 : MRing ι := ∏ k, X ⟨k, i k⟩
  have h0P : h0 ∉ P := by
    intro hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 hmem
    exact hi k hk
  have hQh : map (Int.castRingHom ℂ) h0 ∉ Q := by
    intro hmem
    apply h0P
    rw [← hc]
    exact Ideal.mem_comap.2 hmem
  have hPQ : ∀ f ∈ P, map (Int.castRingHom ℂ) f ∈ Q := by
    intro f hf
    rw [← hc] at hf
    exact Ideal.mem_comap.1 hf
  have hv : F * map (Int.castRingHom ℂ) h0 ∈ vanishingIdeal ℂ (zeroLocus ℂ Q) := by
    rw [mem_vanishingIdeal_iff]
    intro z hz
    have hz : ∀ p ∈ Q, eval z p = 0 := hz
    change eval z _ = 0
    have hzh : eval z (map (Int.castRingHom ℂ) h0) = ∏ k, z ⟨k, i k⟩ := by
      simp [h0, map_prod]
    by_cases h0z : eval z (map (Int.castRingHom ℂ) h0) = 0
    · rw [map_mul, h0z, mul_zero]
    · have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := by
        rw [hzh] at h0z
        exact fun k => Finset.prod_ne_zero_iff.1 h0z k (Finset.mem_univ k)
      have hzP : z ∈ mcPts P := ⟨fun k => ⟨i k, hne k⟩, fun f hf => hz _ (hPQ f hf)⟩
      rw [map_mul, hF z hzP, zero_mul]
  rw [vanishingIdeal_zeroLocus_eq_radical, hQp.radical] at hv
  exact (hQp.mem_or_mem hv).resolve_right hQh

end GroundTheory.Heights₂.Heights.HilbertSamuel
