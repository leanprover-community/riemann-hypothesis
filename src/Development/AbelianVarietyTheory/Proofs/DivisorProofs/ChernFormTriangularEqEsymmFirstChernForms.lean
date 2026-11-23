module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureLowerTriangularPositiveDiagonalStatement
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTri

theorem coeff_charpolyRev_neg_of_tri {R : Type} [CommRing R] {s : ℕ} (F : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, j < i → F i j = 0) (k : ℕ) :
    (Matrix.charpolyRev (-F)).coeff k = ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, F i i := by
  rw [Matrix.charpolyRev, Matrix.det_of_upperTriangular]
  · have e : ∀ i, ((1 : Matrix (Fin s) (Fin s) (Polynomial R)) -
        (Polynomial.X : Polynomial R) • (-F).map Polynomial.C) i i = 1 + Polynomial.C (F i i) * Polynomial.X := by
      intro i
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, map_neg, smul_eq_mul,
        mul_neg, sub_neg_eq_add, mul_comm]
    simp only [e]
    rw [Finset.prod_one_add, Polynomial.finsetSum_coeff]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, Polynomial.coeff_C_mul_X_pow]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp [eq_comm]
  · intro i j hij
    have hij' : j < i := hij
    simp [h i j hij', hij'.ne']

theorem chernAt_tri : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ j, chernAt T v j = aeval (fun i => ofValues (ddc (fun x => -Real.log (d i x)) v)) (esymm (Fin s) ℂ j) := by
  intro n s T d v hT hd htri j
  have key := GlobalTheory.T.chernCurvature_lowerTriangular_positive_diagonal n s T d v hT hd htri
  rw [chernAt, chernPoly, coeff_charpolyRev_neg_of_tri _ (fun a b hab => by
    simp [curvPoly, fun ξ η => (key ξ η).1 a b hab]), esymm]

  simp only [map_sum, map_prod, aeval_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have e (i : Fin s) : ofValues (ddc (fun x => -Real.log (d i x)) v) =
      kappa • (aeval sym (curvPoly T v i i) : Ev n) := by

    simp only [ofValues, ddc, curvPoly, Matrix.of_apply, map_sum, map_mul, aeval_C, aeval_X, Finset.smul_sum,
    fun ξ η => (key ξ η).2 i, leviForm_neg, ← Algebra.smul_def, smul_smul, ContinuousLinearMap.neg_apply]
  simp only [e]
  rw [Finset.prod_smul, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2]

end GlobalTheory.ChernTri
