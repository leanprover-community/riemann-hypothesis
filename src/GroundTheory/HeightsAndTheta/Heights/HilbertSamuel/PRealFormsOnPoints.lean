module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealFormsOnPoints
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIndependentModBaseChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RealFormsOnPoints.proof (hN : ComplexFormsOnPoints.Statement)
    (hB : IndependentModBaseChange.Statement) : RealFormsOnPoints.Statement := by
  intro K _ ι _ Ω _ y d e r g hP hg hli c hc
  obtain ⟨_, ⟨hprime, -, hrel⟩, -, -⟩ := hP

  have hZ : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (mCoordIdeal y) (g i)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have hmem : ∑ i, n i • g i ∈ mCoordIdeal y := by

      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_zsmul] using hn
    have h0 : mConeMap y (∑ i, n i • g i) = 0 := hmem
    have hsum : mConeMap y (∑ i, n i • g i) =
        MvPolynomial.C (∑ i, n i • aeval y (g i)) * ∏ k, MvPolynomial.X k ^ e k := by

      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ProjLine.mConeMap_eq_of_isMultiHomog y (hg i), map_zsmul, smul_mul_assoc]
    rw [hsum] at h0
    have hX : (∏ k, MvPolynomial.X k ^ e k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact (MvPolynomial.C_eq_zero).mp ((mul_eq_zero.mp h0).resolve_right hX)

  have hC := hB _ (mCoordIdeal y) r g hZ
  set I := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) with hI

  have hF : (∑ i, (c i : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) (g i)) ∈ I := by
    refine hN K ι _ hprime hrel _ fun z hz => ?_

    rw [map_sum]
    simpa only [smul_eval] using hc z hz
  rw [Fintype.linearIndependent_iff] at hC
  funext i
  have h := hC (fun i => (c i : ℂ)) (by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hF

    rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]) i
  exact_mod_cast h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
