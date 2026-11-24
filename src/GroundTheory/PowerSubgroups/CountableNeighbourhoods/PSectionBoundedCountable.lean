module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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

namespace GroundTheory.Variant₂.N1

noncomputable def coeffNorm {K : Type} {ι : K → Type} (G : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) : ℝ :=
  ∑ m ∈ MvPolynomial.support G, ‖(Int.castRingHom ℂ) (AddMonoidAlgebra.coeff G m)‖

theorem norm_eval_le_of_forall_norm_le {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (k : K) × ι k → ℂ} {c : (k : K) → ι k}
    (hz : ∀ (k : K) (i : ι k), ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖)
    {G : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {δ : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G δ) :
    ‖(MvPolynomial.eval z) ((MvPolynomial.map (Int.castRingHom ℂ)) G)‖ ≤
      coeffNorm G * ∏ k : K, ‖z ⟨k, c k⟩‖ ^ δ k := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq', coeffNorm, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod, Fintype.prod_sigma]
  refine Finset.prod_le_prod₀ (fun k _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun k _ => ?_
  rw [← hG m hm k, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hz k i) _

end GroundTheory.Variant₂.N1
