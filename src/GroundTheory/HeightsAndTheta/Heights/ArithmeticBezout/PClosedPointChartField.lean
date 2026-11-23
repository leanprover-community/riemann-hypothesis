module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointChartField
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartZeroTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem ClosedPointChartField.proof : ClosedPointChartField.Statement := by
  intro F _ n I i hI hdim hXi
  have := hI.isPrime
  set ξ := genPt I
  have hξ : ξ i ≠ 0 := fun h =>
    hXi ((ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I (X i)).1 (by simpa using h))
  set g : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I) :=
    aeval fun m => ξ m * (ξ i)⁻¹ with hg

  have hhom : ∀ (h : MvPolynomial (Fin n) F) (d : ℕ), h.IsHomogeneous d →
      ChartZeroTrdeg.homogAt h i d = h := by
    intro h d hh
    conv_rhs => rw [h.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hα' : (α.sum fun _ e => e) = d := by
      have := hh (mem_support_iff.mp hα)
      simpa [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using this
    rw [hα', Nat.sub_self, pow_zero, mul_one]

  have hker : RingHom.ker g = I ⊔ Ideal.span {X i - 1} := by
    apply le_antisymm
    · intro p hp
      rw [RingHom.mem_ker] at hp
      have hH : ChartZeroTrdeg.homogAt p i p.totalDegree ∈ I := by
        rw [← ChartZeroTrdeg.aeval_genPt_eq_zero_iff',
          ChartZeroTrdeg.aeval_homogAt p i _ le_rfl ξ hξ]
        rw [← hg, hp, mul_zero]
      have hd : p - ChartZeroTrdeg.homogAt p i p.totalDegree ∈ Ideal.span {X i - 1} := by
        rw [← Ideal.Quotient.eq]
        have h1 : Ideal.Quotient.mk (Ideal.span {X i - 1}) (X i : MvPolynomial (Fin n) F) = 1 := by
          rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
          exact Ideal.subset_span rfl
        conv_lhs => rw [p.as_sum]

        simp only [ChartZeroTrdeg.homogAt, map_sum, map_mul, map_pow, h1, one_pow, mul_one]
      have := (I ⊔ Ideal.span {X i - 1}).add_mem (Ideal.mem_sup_left hH) (Ideal.mem_sup_right hd)
      simpa using this
    · refine sup_le ?_ ?_
      · intro f hf

        rw [RingHom.mem_ker, ← sum_homogeneousComponent f, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        have hh : (homogeneousComponent d f).IsHomogeneous d :=
          homogeneousComponent_isHomogeneous d f
        have h0 : aeval ξ (homogeneousComponent d f) = 0 :=
          (ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I _).2 (hI.isHomog f hf d)
        by_cases hz : homogeneousComponent d f = 0
        · rw [hz, map_zero]
        have := ChartZeroTrdeg.aeval_homogAt (homogeneousComponent d f) i d
          (hh.totalDegree hz).le ξ hξ
        rw [hhom _ d hh, h0] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hξ)
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        change g (X i - 1) = 0
        simp [hg, hξ]

  let e : (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ≃ₐ[F] g.range :=
    (Ideal.quotientEquivAlgOfEq F (hker.symm.trans (AlgHom.ker_rangeRestrict g).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective g.rangeRestrict_surjective)
  have htr := GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof F n 0 I i hI (by simpa using hdim) hXi
  rw [Algebra.adjoin_range_eq_range_aeval] at htr
  have halg : Algebra.IsAlgebraic F g.range := trdeg_eq_zero_iff.1 (by simpa using htr)
  have hfield : IsField g.range := isField_of_isIntegral_of_isField' (Field.toIsField F)
  have : Algebra.FiniteType F g.range :=
    Algebra.FiniteType.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have : Module.Finite F g.range := Algebra.IsIntegral.finite
  exact ⟨MulEquiv.isField hfield e.toMulEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩

end ObjectsChow

end GroundTheory.Heights₂.Heights
