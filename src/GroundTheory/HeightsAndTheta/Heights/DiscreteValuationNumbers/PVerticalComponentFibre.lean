module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFibreVar
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalComponentFibre.proof (h : FibreVarieties.Statement.{0}) :
    VerticalComponentFibre.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP f b hf hfP W hW hrel hϖW
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro hmem
    have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hP.noTorsion, Ideal.mem_bot] at this
    exact hϖ.ne_zero this

  have hmin : W ∈ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).minimalPrimes := by
    refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hϖW)⟩, ?_⟩
    rintro Q ⟨hQ, hQle⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun e => hWQ (e ▸ le_rfl))
    have hPQ : P ≤ Q := le_sup_left.trans hQle
    have hϖQ : (C ϖ : MRing ι O) ∈ Q := hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    let π := Ideal.Quotient.mk P
    have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
    have : (W.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPW)
    have : (Q.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPQ)
    have hle1 : (W.map π).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    have hlt' : Q.map π < W.map π := by
      refine (Ideal.map_mono hlt.le).lt_of_not_ge fun e => hlt.not_ge ?_
      have := Ideal.comap_mono (f := π) e
      rwa [Ideal.comap_map_of_surjective' π hsurj, Ideal.comap_map_of_surjective' π hsurj,
        Ideal.mk_ker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ] at this
    have : (W.map π).FiniteHeight := ⟨Or.inr (hle1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
    have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt').trans_le hle1
    rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
    have hbot : Q.map π ≤ ⊥ := h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    have : π (C ϖ) ∈ (⊥ : Ideal (MRing ι O ⧸ P)) := hbot (Ideal.mem_map_of_mem π hϖQ)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hϖP this

  have hdiv : divCycle P (C ϖ) W ≠ 0 := by
    unfold divCycle
    rw [dite_eq_left ⟨hmin, hrel⟩]
    have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
        ((P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W),
        Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
      exact hmin
    have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
    have : Nontrivial (Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
    have hpos := Module.length_pos (R := Localization.AtPrime W)
      (M := Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W)))
    rw [multAt, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
    exact_mod_cast (ENat.toNat_pos hpos.ne' hne).ne'
  exact (h O ϖ hϖ K ι P d hP).2 W hdiv

end GroundTheory.Heights₂.Heights.NumbersDVR
