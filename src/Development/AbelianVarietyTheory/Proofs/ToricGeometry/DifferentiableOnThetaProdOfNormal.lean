module

public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.PTheta

namespace GlobalTheory

theorem differentiable_thetaTerm_prod {ι : Type} [Fintype ι] (a b : ι → ℝ) (l : ι → ℤ) :
    Differentiable ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l) := by
  unfold thetaTerm eC
  simp only [dotProduct, Matrix.mulVec, shiftVec, ofRealVec, Pi.add_apply, Matrix.of_apply]
  fun_prop

theorem differentiableOn_theta_prod_of_normal {ι : Type} [Fintype ι] (a b : ι → ℝ)
    {U : Set ((ι → ℂ) × (ι → ι → ℂ))} (hU : IsOpen U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ l, ∀ p ∈ K, ‖thetaTerm a b p.1 (Matrix.of p.2) l‖ ≤ u l) :
    DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) U := by
  intro c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hK : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨u, hu, hbd⟩ := hle _ hK (isCompact_closedBall c (ε / 2))
  have hr : (0 : ℝ) < ε / 4 := by positivity
  have hlim : TendstoUniformlyOn
      (fun s : Finset (ι → ℤ) => fun p : (ι → ℂ) × (ι → ι → ℂ) =>
        ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) Filter.atTop
      (Metric.ball c (2 * (ε / 4))) := by
    have h := tendstoUniformlyOn_tsum hu (fun l p hp => hbd l p hp)
    refine h.mono ?_
    intro p hp
    exact Metric.ball_subset_closedBall (by simpa [show 2 * (ε / 4) = ε / 2 by ring] using hp)
  have hF : ∀ᶠ s : Finset (ι → ℤ) in Filter.atTop, DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (Metric.ball c (2 * (ε / 4))) :=
    Filter.Eventually.of_forall fun s => by
      have h := Differentiable.sum (u := s) fun l _ => differentiable_thetaTerm_prod a b l
      have e : (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l) =
          ∑ l ∈ s, fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l := by
        funext p
        rw [Finset.sum_apply]
      rw [e]
      exact h.differentiableOn
  have hd := (GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball hlim hF).1
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

theorem thetaHolo_of_domainOpen_of_mTest (hopen : DomainOpenStatement)
    (hM : ThetaMTestStatement) : ThetaHoloStatement := by
  intro ι _ a b
  refine differentiableOn_theta_prod_of_normal a b ((hopen ι).preimage continuous_snd) ?_
  intro K hKU hK
  obtain ⟨u, hu, hbd⟩ := hM ι a K hK (fun p hp => hKU hp)
  exact ⟨u, hu, fun l p hp => hbd b p hp l⟩

end GlobalTheory
