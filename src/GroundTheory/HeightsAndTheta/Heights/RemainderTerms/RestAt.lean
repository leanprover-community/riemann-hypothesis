module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.DegPolynomialIsHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealRootRingToRealAlt
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealTransferOfSyzygy
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StaircaseIsHomogeneous
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoeffRenameProdCongrRight
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace RestBoundEq

theorem core (hA : RestBound.Statement)
    (f r a j k : ℕ) (c : SmallBlock) (bot : Bool) (h : r + a = j + k)
    (hf : 1 ≤ f) (hr : 1 ≤ r) (ha : 1 ≤ a) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hsp : ∀ m τ, rootRingToReal f (r + a) j k h (smallPowerSum f r a c m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot m τ)
    (hF : rootRingToReal f (r + a) j k h (restPolynomial f r a c) = IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot)
    (hD : rootRingToReal f (r + a) j k h (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot)
    (hn : f * (r * a) = IndefiniteRowSideFullHecke.RestTerms.nDim f j k)
    (I : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ) (hI : IndefiniteRowSideFullHecke.RestTerms.IsFlagIntegral f j k I)
    (vol : ℝ) (hvol : 0 < vol) (P : Set ℕ) (B₀ : ℝ)
    (hB₀ : 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀)
    (σ : ℕ → ℕ → Fin f → Fin f × Bool) (Q : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ : IndefiniteRowSideFullHecke.RestTerms.IsPsumDecomp f j k (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) Q) :
    Summable (fun p : IndefiniteRowSideFullHecke.RestTerms.primesOver P B₀ =>
        IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1) ∧
      |∑' p : IndefiniteRowSideFullHecke.RestTerms.primesOver P B₀, IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1| ≤
        1.6 * ((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) * vol *
          |I (IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot)| := by
  have hB₀' : 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ := by rw [h]; exact hB₀
  obtain ⟨⟨Q₀, hQ₀⟩, hall⟩ := hA f r a c B₀ hf hr ha hB₀'
  have hFh := RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.proof f r a c
  obtain ⟨hQh, -⟩ := isPowerSumDecomposition_homogeneousComponent f (r + a) _ Q₀ hFh hQ₀
  set Qh : ℕ → Fin f → RootRing f (r + a) :=
    fun m τ => homogeneousComponent (topDegree f (r + a) + 1 - m) (Q₀ m τ) with hQhdef
  obtain ⟨c₀, -, hIc⟩ := FlagIntegralProportional.intersectionNumber_baseChange f j k hf hj hk I hI
  set κ : ℝ := c₀ / FlagEq.stairConst f (j + k) with hκ
  have hIκ : ∀ G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k, G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) →
      I G = κ * flagIntegralReal f (j + k) G := by
    intro G hG
    rw [hIc G hG, flagIntegralReal_eq_mul_ddConst, hκ]
    field_simp [FlagEq.stairConst_pos.ne']
  have htop : topDegree f (r + a) = IndefiniteRowSideFullHecke.RestTerms.dimFl f j k := by
    rw [h]; rfl
  have hDle := le_dimFl f j k hf
  set s : ℕ → ℕ → Fin f → Fin f := fun p n τ => (σ p n τ).1 with hs
  set e : ℕ → ℕ → Fin f → ℕ → ℚ := fun p n τ m => lieSign bot (σ p n τ).2 (m - 1) with he
  obtain ⟨hsum, hbd⟩ := hall Qh hQh s e (fun _ _ _ _ => lieSign_cases _ _ _) P
  have hQ' : IndefiniteRowSideFullHecke.RestTerms.IsPsumDecomp f j k (rootRingToReal f (r + a) j k h (restPolynomial f r a c))
      Q := by rw [hF]; exact hQ
  have hterm : ∀ (p : ℕ) (τ : Fin f) (m : ℕ), m ∈ Icc 2 (j + k) → ∀ n : ℕ,
      IndefiniteRowSideFullHecke.RestTerms.restTerm f j k I σ Q p τ m n =
        κ * (((p : ℝ) ^ ((n + 1) * m))⁻¹ * ((e p (n + 1) τ m *
          restTerm f (r + a) Qh m τ (smallPowerSum f r a c (m - 1) (s p (n + 1) τ)) : ℚ) : ℝ)) := by
    intro p τ m hm n
    obtain ⟨hm2, hmN⟩ := Finset.mem_Icc.1 hm
    have hlie := lieClass_reduce f j k hf bot I hI Q hQ.1 (σ p (n + 1) τ) τ m hm2 hmN
    have hG := smallPowerSum_isHomogeneous f r a c (m - 1) (σ p (n + 1) τ).1
    have hhom : (IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot (m - 1) (σ p (n + 1) τ).1 * Q τ m).IsHomogeneous
        (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
      rw [← hsp]
      have := ((rootRingToReal_isHomogeneous_iff f (r + a) j k h _ _).2 hG).mul
        (hQ.1 τ m (by omega) hmN)
      convert this using 1
      omega
    have hwd := flagIntegralReal_transfer_of_syzygy f (r + a) j k h _ Qh hQh Q hQ'.2 m τ _
      (fun S hS => syzygy_term_zero hA f r a c hf hr ha S hS τ (σ p (n + 1) τ).1 m hm2 (by omega))
    rw [IndefiniteRowSideFullHecke.RestTerms.restTerm, hlie, hIκ _ hhom, ← hsp, hwd]
    simp only [restTerm, he, hs]
    push_cast
    ring
  have hIcc : Finset.Icc 2 (r + a) = Finset.Icc 2 (j + k) := by rw [h]
  have hmodel : ∀ p : ℕ, IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p =
      vol * κ * restPrimeModel f r a c Qh s e p := by
    intro p
    have hX : (∑ τ : Fin f, ∑ m ∈ Icc 2 (j + k), ∑' n : ℕ,
        IndefiniteRowSideFullHecke.RestTerms.restTerm f j k I σ Q p τ m n) =
        κ * ∑ τ : Fin f, ∑ m ∈ Icc 2 (r + a), ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * m))⁻¹ *
          ((e p (n + 1) τ m * restTerm f (r + a) Qh m τ
            (smallPowerSum f r a c (m - 1) (s p (n + 1) τ)) : ℚ) : ℝ) := by
      rw [hIcc, Finset.mul_sum]
      refine sum_congr rfl fun τ _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [← tsum_mul_left]
      exact tsum_congr fun n => hterm p τ m hm n
    rw [IndefiniteRowSideFullHecke.RestTerms.restAt, restPrimeModel, hX]
    ring
  have hs' : Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
      restPrimeModel f r a c Qh s e p) := summable_abs_iff.1 hsum
  have hJ : I (IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot) = κ * (fibreDegree f r a c : ℝ) := by
    have hh : (IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
      rw [← hD, ← htop]
      exact (rootRingToReal_isHomogeneous_iff f (r + a) j k h _ _).2 (degPolynomial_isHomogeneous f r a c)
    rw [hIκ _ hh, ← hD, TermBoundEq.flagIntegralReal_rootRingToReal]
    rfl
  have hn' : ((f * (r * a) + 1 : ℕ) : ℝ) = (IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1 := by
    rw [hn]; push_cast; ring
  rw [hn'] at hbd
  refine ⟨?_, ?_⟩
  · show Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
      IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1)
    simp_rw [hmodel]
    exact hs'.mul_left _
  · show |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1| ≤ _
    simp_rw [hmodel]
    rw [tsum_mul_left, abs_mul, abs_mul, abs_of_pos hvol, hJ, abs_mul]
    have h0 : 0 ≤ vol * |κ| := by positivity
    calc vol * |κ| * |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Qh s e p|
        ≤ vol * |κ| * (1.6 * ((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) * |(fibreDegree f r a c : ℝ)|) :=
          mul_le_mul_of_nonneg_left hbd h0
      _ = _ := by ring

end RestBoundEq

theorem RestBound.imp : RestBound.Statement → IndefiniteRowSideFullHecke.RestTerms.RestBound.Statement := by
  intro hA f j k hf hj hk bot _hsmall I hI vol hvol P _hP B₀ hB₀ σ Q hQ
  cases bot with
  | false =>
    exact RestBoundEq.core hA f j k j k .first false rfl hf hj hk hj hk
      (rootRingToReal_smallPowerSum_first f j k) (rootRingToReal_restPolynomial_first f j k)
      (rootRingToReal_degreePolynomial_first f j k) (by unfold IndefiniteRowSideFullHecke.RestTerms.nDim; ring)
      I hI vol hvol P B₀ hB₀ σ Q hQ
  | true =>
    exact RestBoundEq.core hA f k j j k .last true (Nat.add_comm k j) hf hk hj hj hk
      (rootRingToReal_smallPowerSum_last f k j) (rootRingToReal_restPolynomial_last f k j)
      (rootRingToReal_degreePolynomial_last f k j) (by unfold IndefiniteRowSideFullHecke.RestTerms.nDim; ring)
      I hI vol hvol P B₀ hB₀ σ Q hQ

end

end GroundTheory.Heights₂.Heights.RestTerms
