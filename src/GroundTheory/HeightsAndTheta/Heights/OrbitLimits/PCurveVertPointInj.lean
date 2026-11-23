module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace CurveVerticalPointInjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem coord_ne_zero (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ)
    (hA : IsArithVar (mCoordIdeal y) 1) (hs : IsMultiHomog s d) {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  classical
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ K ι (mCoordIdeal y) s d hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ K ι _ W hJ hW.1)

end CurveVerticalPointInjective


open CurveVerticalPointInjective in
theorem CurveVertPointInj.proof (hCh : CurveVertPointChart.Statement) : CurveVertPointInj.Statement := by
  intro K _ ι _ Ω _ y s d hA hs hsP W hW W' hW' hWW'
  choose c hc using hW.2
  choose c' hc' using hW'.2
  obtain ⟨hmax, hrat, hform⟩ := hCh K ι Ω y s d hA hs hsP W hW c hc
  obtain ⟨-, -, hform'⟩ := hCh K ι Ω y s d hA hs hsP W' hW' c' hc'
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    coord_ne_zero y _ fun h => hc k (le_sup_left.trans hW.1.1.2 h)
  choose a' b' hb' hab' using fun k => hrat ⟨k, c' k⟩
  have hab'' : ∀ k, (b' k : Ω) * y ⟨k, c' k⟩ = a' k * y ⟨k, c k⟩ := fun k => by
    rw [← hab' k]; field_simp [hyc k]
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := isMultiHomogIdeal_of_mem_divSupp y s d hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' e g he).1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform e g he).2 ⟨a * ∏ k, a' k ^ e k, (∏ k, b' k ^ e k) * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · obtain ⟨k, -, hk⟩ := (hmax.isPrime.prod_mem_iff (s := Finset.univ)).1 h
        exact hb' k (hmax.isPrime.mem_of_pow_mem _ hk)
      · exact hb h
    · push_cast
      calc (∏ k, (b' k : Ω) ^ e k) * b * aeval y g
          = a * ∏ k, ((b' k : Ω) * y ⟨k, c' k⟩) ^ e k := by
            rw [mul_assoc, habg, Finset.prod_congr rfl fun k _ => mul_pow (b' k : Ω) _ (e k),
              Finset.prod_mul_distrib]; ring
        _ = (a * ∏ k, (a' k : Ω) ^ e k) * ∏ k, y ⟨k, c k⟩ ^ e k := by
            simp_rw [hab'', mul_pow, Finset.prod_mul_distrib]; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights.Targets
