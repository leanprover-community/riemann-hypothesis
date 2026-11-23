module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos

theorem isPsh_add_zero_add (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  unfold ReciprocityTheory.AnForm.M.IsPsh
  intro x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hfun : ((Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Θ.φ x _ + 0 + Θ.φ x _ = (2 : ℝ) • Θ.φ x _
    rw [smul_eq_mul]
    ring
  have hlevi : ∀ z v, ReciprocityTheory.AnForm.levi (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) z v =
      2 * ReciprocityTheory.AnForm.levi (Θ.φ x ∘ (A.chart j).symm) z v := by
    intro z v
    unfold ReciprocityTheory.AnForm.levi
    have h1 : fderiv ℝ (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) =
        (2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm) := fderiv_const_smul_field (2 : ℝ)
    have h2 : fderiv ℝ ((2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) =
        (2 : ℝ) • fderiv ℝ (fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) := fderiv_const_smul_field (2 : ℝ)
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun, hlevi]
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi]
  · exact mul_nonneg (by norm_num) (hpos x j y hy' w hw).le

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos
