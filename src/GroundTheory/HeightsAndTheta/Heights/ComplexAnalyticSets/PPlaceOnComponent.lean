module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StReducedNormalisationPlace
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveMinimalPrimeQuotient
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {p : Ideal R} (hp : p ∈ minimalPrimes R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = p) : ringKrullDim S = 1 := by
  have hpp : p.IsPrime := hp.1.1
  refine le_antisymm (hR ▸ ringKrullDim_le_of_surjective φ hφ) ?_
  obtain ⟨x, y, hxy⟩ := Order.one_le_krullDim_iff.1 (le_of_eq hR.symm : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
  have hxm : x.asIdeal < IsLocalRing.maximalIdeal R :=
    lt_of_lt_of_le hxy (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)
  have hpm : p < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun h ↦ ?_
    have hpx : p ≤ x.asIdeal := hp.2 ⟨x.isPrime, bot_le⟩ (h ▸ hxm.le)
    exact (lt_of_le_of_lt hpx hxm).ne h
  have hk : ∀ K : Ideal R, p ≤ K → (K.map φ).comap φ = K := fun K hK ↦ by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.2 hK]
  have h0 : (p.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hker.le
  have h1 : ((IsLocalRing.maximalIdeal R).map φ).IsPrime :=
    Ideal.map_isPrime_of_surjective hφ (hker.le.trans hpm.le)
  refine Order.one_le_krullDim_iff.2 ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩
  change p.map φ < (IsLocalRing.maximalIdeal R).map φ
  refine lt_of_le_of_ne (Ideal.map_mono hpm.le) fun h ↦ hpm.ne ?_
  rw [← hk p le_rfl, h, hk _ hpm.le]

theorem PlaceOnComponent.proof (h₁ : ReducedNormalisationPlace.Statement)
    (h₂ : CurveMinimalPrimeQuotient.Statement) : PlaceOnComponent.Statement := by
  intro n I q hrad hdim P
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  have : Nontrivial (curveLocalRing I q) := by
    refine not_subsingleton_iff_nontrivial.1 fun h ↦ ?_
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨p, hp, hS⟩ := h₁ (curveLocalRing I q) P
  obtain ⟨J, hJ, hJq, φ, hφ, hker, hφf⟩ := h₂ n I q p hp
  obtain ⟨P', hP'⟩ := hS (curveLocalRing J q) φ hφ hker
  refine ⟨J, hJ, hJq, ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes hdim hp φ hφ hker, P', fun f ↦ ?_⟩
  have e := hP' (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hφf] at e
  exact e

end GroundTheory.Heights₂.Heights
