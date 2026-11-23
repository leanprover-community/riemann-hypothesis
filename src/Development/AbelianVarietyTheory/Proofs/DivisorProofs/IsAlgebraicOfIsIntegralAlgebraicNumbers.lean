module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPowStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isAlgebraic_of_isIntegral_algebraicNumbers {x : ℂ}
    (hx : IsIntegral (integralClosure ℚ ℂ).toSubring x) : IsAlgebraic ℚ x := by
  have hx' : IsIntegral (integralClosure ℚ ℂ) x := hx
  exact (isIntegral_trans (R := ℚ) (A := integralClosure ℚ ℂ) x hx').isAlgebraic

theorem fam_value_isAlgebraic : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (IsAlgebraic ℚ) N (f i)) → IsAlgebraic ℚ (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsAlgebraic ℚ (f i τ₀ / Ω ^ w) := by
  intro ι _ act w N f τ₀ Ω hN hb hf hq hj hΩ i
  refine isAlgebraic_of_isIntegral_algebraicNumbers
    (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N f (integralClosure ℚ ℂ).toSubring τ₀ Ω hN hb hf (fun k => ?_) ?_ hΩ i)
  · obtain ⟨a, ha, hal⟩ := hq k
    exact ⟨a, ha, fun n => (hal n).isIntegral⟩
  · exact isIntegral_algebraMap (R := (integralClosure ℚ ℂ).toSubring) (A := ℂ)
      (x := ⟨jT τ₀, hj.isIntegral⟩)

end GlobalTheory.QFam
