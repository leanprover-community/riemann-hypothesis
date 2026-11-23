module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexGramMetricChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem top_sub_top_mixPot (I : AllFam) (hI : I.IsFamily) {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type}
    [Fintype κ] {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (hP : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) (hs₀ : IsSmoothMetric m₀)
    (hs₁ : IsSmoothMetric m₁) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  classical
  have hB := tele_smooth_ratio hs₀ hs₁
  have hsymm := (hI Unit (GlobalTheory κ)).1
  have hadd := (hI Unit (GlobalTheory κ)).2.1
  have htel := Finset.sum_range_sub
    (fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i)) (D + 1)
  have hT0 : tele_fam m₀ m₁ (D + 1) 0 = fun _ => HermLine.ofCone m₀ := by
    funext j
    simp [tele_fam]
  have hT1 : tele_fam m₀ m₁ (D + 1) (D + 1) = fun _ => HermLine.ofCone m₁ := by
    funext j
    simp [tele_fam, j.isLt]
  simp only [hT0, hT1] at htel
  unfold top
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e1 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (i + 1)) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₁)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl)]
    have : HermLine.ofCone m₁ = tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  have e0 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₀)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have : HermLine.ofCone m₀ = tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  rw [e1, e0, tele_ofCone_tensor m₀ m₁,
    hadd _ _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _) (tele_smooth_ofCone hs₀) hB,
    add_sub_cancel_left, fam_degZero I hI hP _ (tele_fam_smooth hs₀ hs₁ _ _) _ hB rfl]
  have hpot : pot (tele_fam m₀ m₁ D i) = mixPot m₀ m₁ D i := by
    funext j z
    simp only [pot, mixPot, tele_fam]
    split_ifs <;> rfl
  rw [hpot]
  rfl

theorem DefectMetricChange.proof (hR : RealGramComparison.Statement)
    (hC : ComplexGramMetricChange.Statement) (hM : ResolutionMixedIntegral.Statement) :
    DefectMetricChange.Statement := by
  intro D Ω _ _ κ _ I d m₁ P0₁ hs hc hle hp e hI he
  have h₁ := hR D Ω κ (d.withMetric m₁ P0₁ hs hc hle hp) e he
  have h₀ := hR D Ω κ d e he
  have hc₁ := hC D Ω κ d m₁ P0₁ hs hc hle hp e he
  have htop : top I d.x m₁ D = top I d.x d.m D + ((D : ℝ) + 1) * resMetricInt d m₁ := by
    rw [← hM D Ω κ d m₁ hs, ← top_sub_top_mixPot I hI d.arith d.smooth hs]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
