module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem LemmaA.proof (h1 : FlagIntegralTopDegree.Statement)
    (h2 : FlagIntegralVandermondePos.Statement) (h3 : FlagDividedDifferencePoly.Statement)
    (h4 : FlagAntisymDecomposition.Statement) (h5 : FlagVandermondeHomogeneous.Statement)
    (h6 : FlagAntisymHomogeneous.Statement) (h7 : FlagQuotientHomogeneous.Statement)
    (h8 : FlagRestrictHomogeneous.Statement) (h9 : FlagRestrictSymmetric.Statement)
    (h10 : FlagRestrictDecomposition.Statement) (h11 : FlagPowerSumPreimage.Statement)
    (h12 : FlagRestrictConstantCoeff.Statement) (h13 : FlagIntegralViaQuotient.Statement) :
    LemmaA.Statement := by
  intro f N
  refine ⟨flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f, ?_, ?_, ?_⟩
  · exact div_ne_zero (h2 f N).ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr N.factorial_ne_zero))
  · exact fun H hH => h1 f N H hH
  intro F Q hF k hk1 hkN τ G hG
  choose R hR hRsym using fun l σ => h3 f N (G * Q l σ)
  set P : RootRing f N := ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ
    with hPdef
  have hanti : antisymmetrize f N (G * F) = blockVandermonde f N * P := h4 f N F G Q R hF hR
  refine ⟨P, ?_, ?_, ?_⟩
  · have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) _)).mpr
        (Flag.blockVandermonde_ne_zero f N)
    rw [dividedDifference, hanti, map_mul, mul_div_cancel_left₀ _ hΔ]
  · intro hFh
    have hGF : (G * F).IsHomogeneous (topDegree f N + k) := by
      have := hG.mul hFh
      rwa [show k - 1 + (topDegree f N + 1) = topDegree f N + k by omega] at this
    have hA := h6 f N (G * F) _ hGF
    rw [hanti] at hA
    exact h8 f N τ P k (h7 _ _ _ _ _ (Flag.blockVandermonde_ne_zero f N) (h5 f N) hA)
  · obtain ⟨S, hS, hScoeff⟩ := h11 N (fun l => restrictToBlock f N τ (R l τ))
      (fun l => h9 f N τ (R l τ) (hRsym l τ))
    refine ⟨S, ?_, ?_⟩
    · rw [hS, hPdef, h10]
    · rw [hScoeff k hk1 hkN, h12, h13 f N _ _ (hR k τ)]

end

end RestTerms

end GroundTheory.Heights₂.Heights
