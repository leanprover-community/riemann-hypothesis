module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem mul_diag_of_par {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {S T : Mat m K}
    (hS : Par m O S) (hT : Par m O' T) (τ : ι) (i : Fin (m τ)) :
    (S * T) τ i i = S τ i i * T τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [(hT τ).2.2.2 l i l.isLt h, mul_zero]
  · rw [(hS τ).2.2.2 i l i.isLt h, zero_mul]

theorem diag_of_par : ∀ (ι : Type) (m : ι → ℕ) (K : Type) [Field K] (O : Subring K) (S : Mat m K), Par m O S →
    ∀ x : Root m, S x.1 x.2 x.2 ≠ 0 ∧ (S x.1 x.2 x.2)⁻¹ ∈ O ∧ S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ ∧
      ∀ T : Mat m K, Par m ⊤ T → (S * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * T x.1 x.2 x.2 := by
  intro ι m K _ O S hS x
  have hSi : Par m O S⁻¹ := hS.inv
  have h1 : S x.1 x.2 x.2 * S⁻¹ x.1 x.2 x.2 = 1 := by
    rw [← mul_diag_of_par hS hSi, Mat.mul_inv hS.det_ne]
    exact Matrix.one_apply_eq _
  have hne : S x.1 x.2 x.2 ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hinv : S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  refine ⟨hne, ?_, hinv, fun T hT => mul_diag_of_par hS hT x.1 x.2⟩
  rw [← hinv]
  exact (hSi x.1).1 x.2 x.2

end GlobalTheory.FlagPush
