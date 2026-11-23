module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveRationalSectionSum

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_smul {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    logNorm X s (fun p => c p.1 * z p) = logNorm X s z := by
  unfold logNorm
  rw [eval_smul_homog s a hs c z, X.smul c z hc, norm_mul]
  have hprod : (∏ k, ‖c k‖ ^ X.a k) = ‖∏ k, c k ^ a k‖ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hXa k, zpow_natCast, norm_pow]
  rw [hprod, mul_div_mul_left _ _
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)))]

theorem arInt_eq_sum {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    arInt P s X (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      ∑ᶠ q : projPts P, logNorm X s (Quot.out q : mcPts P) := by
  have : Nonempty K := hP.1
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) =>
      Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) = Fin.elim0 :=
    funext fun j => j.elim0
  unfold arInt
  rw [hφ]
  exact PtsIntegralPoints.homogProof K ι P _ hP.2.1.2.1 (HilbertSamuel.CurvePointsFinite.proof K ι P hP)
    fun c z hc _ => logNorm_smul hXa hs c z hc


end CurveRationalSectionSum


end

end GroundTheory.Heights₂.Heights.Targets
