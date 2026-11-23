module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMGeneralPoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLocusOpen
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.KrullDimension.Zero

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets IsLocalRing

theorem isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes {n : ℕ}
    {I W : Ideal (MvPolynomial (Fin n) ℂ)} [W.IsPrime] (hW : W ∈ I.minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime W))) := by
  set S := Localization.AtPrime W
  set J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) S)
  have hJm : J ≤ maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hW.1.2
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hdim : Ring.KrullDimLE 0 (S ⧸ J) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro K hK
    have : K.IsPrime := hK.1.1
    have hKm : K ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal hK.1.1.ne_top
    have hI : I ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      Ideal.map_le_iff_le_comap.mp hK.1.2
    have hKW : K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) ≤ W := by
      have h := Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin n) ℂ) S) hKm
      rwa [show (maximalIdeal S).comap (algebraMap (MvPolynomial (Fin n) ℂ) S) = W from
        Localization.AtPrime.under_maximalIdeal] at h
    have hWK : W ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      hW.2 ⟨Ideal.IsPrime.comap _, hI⟩ hKW
    have hmK : maximalIdeal S ≤ K := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_le_iff_le_comap.mpr hWK
    rw [le_antisymm hKm hmK]
    exact maximalIdeal.isMaximal S
  have h0 : ringKrullDim (S ⧸ J) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim
  exact
    { exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _, by simpa using h0⟩ }

theorem CMGeneralPoint.proof (hOpen : CMLocusOpen.Statement) : CMGeneralPoint.Statement := by
  intro n I W hW
  have : W.IsPrime := hW.1.1
  obtain ⟨g, hgW, hg⟩ :=
    hOpen n I W hW.1.2 (isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes hW)
  have hfin : (I.minimalPrimes \ {W}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset Set.sdiff_subset
  have hsel : ∀ W' ∈ I.minimalPrimes \ {W}, ∃ h, h ∈ W' ∧ h ∉ W := by
    rintro W' ⟨hW', hne⟩
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc (hW.2 hW'.1 hc))
  choose! h hh using hsel
  refine ⟨g * ∏ W' ∈ hfin.toFinset, h W', ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› hmem with h1 | h1
    · exact hgW h1
    · obtain ⟨W', hW', h2⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (hh W' (hfin.mem_toFinset.mp hW')).2 h2
  · intro q hq hf
    rw [map_mul, map_prod] at hf
    have hg0 : eval q g ≠ 0 := left_ne_zero_of_mul hf
    have hp0 := right_ne_zero_of_mul hf
    refine ⟨fun W' hW' hqW' => ?_, ?_⟩
    · by_contra hne
      have hmem : W' ∈ I.minimalPrimes \ {W} := ⟨hW', hne⟩
      exact hp0 (Finset.prod_eq_zero (hfin.mem_toFinset.mpr hmem) (hqW' _ (hh W' hmem).1))
    · have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
        fun x hx => RingHom.mem_ker.mpr (hq x hx)
      exact hg _ (hW.1.2.trans hWq) fun hk => hg0 (RingHom.mem_ker.mp hk)

end GroundTheory.Heights₂.Heights
