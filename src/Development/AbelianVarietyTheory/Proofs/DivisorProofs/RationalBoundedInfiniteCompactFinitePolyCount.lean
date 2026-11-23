module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdelesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem place_le_norm_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (ξ : E)
    (w : InfinitePlace E) : w ξ ≤ ‖pInf E (algebraMap E (Ad E) ξ)‖ := by
  have h := norm_le_pi_norm (pInf E (algebraMap E (Ad E) ξ)) w
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h
  exact h

theorem rat_bounded_compact_polynomial : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ∃ m : ℕ,
    ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧
      ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ)
        ≤ C * T ^ m := by
  intro E _ _ _
  obtain ⟨m, C₀, hC₀, hcount⟩ := GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le E
  refine ⟨m, fun Kf hKf => ?_⟩
  obtain ⟨n, hn, hint⟩ := GlobalTheory.T.exists_common_denominator_compact_finiteAdeles E Kf hKf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨C₀ * (n : ℝ) ^ m, by positivity, fun T hT => ?_⟩
  have hnT : (1 : ℝ) ≤ n * T := by nlinarith
  obtain ⟨hAfin, hAcard⟩ := hcount (n * T) hnT
  set A := {x : 𝓞 E | ∀ w : InfinitePlace E, w (x : E) ≤ n * T}
  set S := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hsub : S ⊆ (fun x : 𝓞 E => (x : E) / n) '' A := by
    intro ξ hξ
    have hi : IsIntegral ℤ ((n : E) * ξ) := hint ξ hξ.2
    refine ⟨⟨(n : E) * ξ, hi⟩, fun w => ?_, ?_⟩
    · show w ((n : E) * ξ) ≤ n * T
      rw [← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul, Complex.norm_natCast,
        InfinitePlace.norm_embedding_eq]
      exact mul_le_mul_of_nonneg_left ((place_le_norm_pInf ξ w).trans hξ.1) (Nat.cast_nonneg n)
    · show (n : E) * ξ / n = ξ
      field_simp
  have hSfin : S.Finite := (hAfin.image _).subset hsub
  refine ⟨hSfin, ?_⟩
  have h1 : S.ncard ≤ A.ncard :=
    (Set.ncard_le_ncard hsub (hAfin.image _)).trans (Set.ncard_image_le hAfin)
  calc (S.ncard : ℝ) ≤ A.ncard := by exact_mod_cast h1
    _ ≤ C₀ * (n * T) ^ m := hAcard
    _ = C₀ * (n : ℝ) ^ m * T ^ m := by rw [mul_pow]; ring

end GlobalTheory
