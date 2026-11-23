module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroDimIsolated
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem ZeroDimIsolated.proof : ZeroDimIsolated.Statement := by
  intro n I q hdim
  classical
  have : Ring.KrullDimLE 0 (curveLocalRing I q) := Ring.krullDimLE_iff.2 (by simpa using hdim)
  have hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧
      ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈
        Ring.jacobson (curveLocalRing I q) := by
      rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
      intro P hP
      have hP' : Ideal.IsMaximal P := hP
      let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
      have hPm : (Ideal.comap π P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')
      have hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
          (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q))) := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]
        simp [RingHom.mem_ker]
      rw [← IsLocalRing.eq_maximalIdeal hPm] at hL
      exact hL
    rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← map_pow] at hk
    have hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
        ((X i - C (q i)) ^ k) ∈
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hk
    obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap
    exact ⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩
  choose s hs k hk using hnil
  refine ⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩
  · apply (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds
    simp [map_prod, Finset.prod_ne_zero_iff, hs]
  · rintro x ⟨hxZ, hxN⟩
    simp only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN
    rw [Set.mem_singleton_iff]
    funext i
    have h := hxZ _ (hk i)
    simp only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (hxN i (Finset.mem_univ i))
    · exact sub_eq_zero.1 h

end GroundTheory.Heights₂.Heights
