module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
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
import Mathlib.RingTheory.Ideal.Height
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

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

variable {n : ℕ}

theorem isLocalRing_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    [Nontrivial (curveLocalRing I q)] : IsLocalRing (curveLocalRing I q) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective

theorem OrdFiniteNonZeroDivisor.proof : OrdFiniteNonZeroDivisor.Statement := by
  intro n I q f hrad hdim hord
  have : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing (curveLocalRing I q) := isLocalRing_curveLocalRing I q
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  rw [mem_nonZeroDivisors_iff_right]
  intro y hyx
  by_contra hy

  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes (curveLocalRing I q), y ∉ p := by
    have : y ∉ (⊥ : Ideal (curveLocalRing I q)).radical := by
      rintro ⟨k, hk⟩
      exact hy (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
    simpa [← Ideal.sInf_minimalPrimes, minimalPrimes] using this
  have hpP : p.IsPrime := hp.1.1
  have hxp := (hpP.mem_or_mem (hyx ▸ p.zero_mem)).resolve_left hyp

  have hpmax : ¬ p.IsMaximal := by
    intro hm
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := curveLocalRing I q)
    rw [← IsLocalRing.eq_maximalIdeal hm, Ideal.height_eq_zero_iff.mpr hp, hdim] at h1
    exact absurd h1 (by decide)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      (integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (curveNormalisation I q))
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (algebraMap_curveNormalisation_injective I q)]; exact bot_le)
  obtain ⟨P, hPm, hQP⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  apply hord ⟨P, hPm⟩
  have : P.IsPrime := hPm.isPrime
  have hd : Disjoint (P.primeCompl : Set (curveNormalisation I q)) Q :=
    Set.disjoint_left.2 fun a ha haQ ↦ ha (hQP haQ)
  set Q' := Q.map (algebraMap (curveNormalisation I q) (Localization.AtPrime P)) with hQ'def
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd
  have hQ'u : Q'.under _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd
  have hle : Ideal.span {(algebraMap (curveNormalisation I q) (Localization.AtPrime P)
      (algebraMap (curveLocalRing I q) (curveNormalisation I q)
        (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)))} ≤ Q' := by
    rw [Ideal.span_singleton_le_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hQp] at hxp
    exact hxp

  change Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {_}) = ⊤
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨-, hart⟩ := hne
  have : IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Q') :=
    isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)
  have : IsArtinianRing (Localization.AtPrime P ⧸ Q') := isArtinian_of_tower (Localization.AtPrime P) this
  have hQ'max : Q'.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hQeq : Q = P := by
    rw [← hQ'u, IsLocalRing.eq_maximalIdeal hQ'max, Localization.AtPrime.under_maximalIdeal]
  apply hpmax
  rw [← hQp]
  have : Q.IsMaximal := hQeq ▸ hPm
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q

end GroundTheory.Heights₂.Heights
