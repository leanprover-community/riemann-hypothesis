module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem prod_one_sub_rootOfUnityPoint (h1 : SchProdOneSubRootsOfUnity.Statement) {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ) := by
  let f : ℕ → Polynomial ℂ := fun i =>
    1 - Polynomial.C (if i < k then rootOfUnity k ^ i else 0) * Polynomial.X
  calc ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X)
      = ∏ i ∈ range N, f i := Fin.prod_univ_eq_prod_range f N
    _ = ∏ i ∈ range k, f i := by
        refine (prod_subset (range_subset_range.2 hkN) fun i _ hik => ?_).symm
        have : ¬ i < k := fun h => hik (mem_range.2 h)
        simp [f, this]
    _ = ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) :=
        prod_congr rfl fun i hi => by simp [f, mem_range.1 hi]
    _ = 1 - Polynomial.X ^ k := h1 k hk

theorem SchCompleteAtRootsOfUnity.proof (h1 : SchProdOneSubRootsOfUnity.Statement)
    (h2 : SchCompleteGenerating.Statement) : SchCompleteAtRootsOfUnity.Statement := by
  intro N k d hk hkN
  let H : ℕ → ℂ := fun n => aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ n)
  have hrec : ∀ n, H n - (if k ≤ n then H (n - k) else 0) = if n = 0 then 1 else 0 := by
    intro n
    have e := h2 N (rootOfUnityPoint N k) n
    rw [prod_one_sub_rootOfUnityPoint h1 hk hkN] at e
    rw [← e]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow, sub_mul,
      sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [H]
  show H d = _
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e := hrec d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [if_neg (by omega), sub_zero, if_pos rfl] at e
      rw [e, if_pos (dvd_zero k)]
    · by_cases hkd : k ≤ d
      · rw [if_pos hkd, if_neg (show d ≠ 0 by omega), sub_eq_zero, ih (d - k) (by omega)] at e
        have hdvd : k ∣ d - k ↔ k ∣ d := by
          conv_rhs => rw [show d = d - k + k by omega]
          exact (Nat.dvd_add_self_right).symm
        rw [e]
        exact if_congr hdvd rfl rfl
      · rw [if_neg hkd, if_neg (show d ≠ 0 by omega), sub_zero] at e
        rw [e, if_neg]
        exact fun h => hkd (Nat.le_of_dvd hd h)

end GroundTheory.Heights₂.Heights.RestTerms
