module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import Mathlib.Analysis.Analytic.Order
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

variable {n : ℕ}

def branchOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (c : VarBranch I 1 q)
    (f : MvPolynomial (Fin n) ℂ) : ℕ∞ :=
  analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0

theorem branchOrder_eq_of_vanishesToOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) (f : MvPolynomial (Fin n) ℂ) (k : ℕ)
    (h : VanishesToOrder (fun t ↦ eval (c.toFun t) f) c.radius k) : branchOrder c f = k := by
  obtain ⟨H, hHd, hH0, hF⟩ := h
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
  have hball : ∀ τ ∈ Metric.ball (0 : ℂ) c.radius, ι τ ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    intro τ hτ
    simpa [ι, Metric.mem_ball, dist_zero_right, pi_norm_const] using hτ
  have hg : AnalyticAt ℂ (H ∘ ι) 0 :=
    (hHd.comp hιd.differentiableOn hball).analyticAt (Metric.ball_mem_nhds 0 c.radius_pos)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), eval (c.toFun (ι τ)) f = (τ - 0) ^ k • (H ∘ ι) τ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) c.radius_pos] with τ hτ
    refine (hF _ (hball τ hτ)).trans ?_
    simp [ι]
  have hF' : AnalyticAt ℂ (fun τ : ℂ ↦ eval (c.toFun (ι τ)) f) 0 :=
    AnalyticAt.congr (((analyticAt_id.sub analyticAt_const).pow k).smul hg) (hev.mono fun τ h ↦ h.symm)
  exact hF'.analyticOrderAt_eq_natCast.2
    ⟨H ∘ ι, hg, hH0 _ (hball 0 (Metric.mem_ball_self c.radius_pos)), hev⟩

def BranchNormalisation.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    IsRadicalAt I q → 0 < m →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ringKrullDim (curveLocalRing I q) = 1 ∧
      (∀ f : MvPolynomial (Fin n) ℂ, (∀ b, branchOrder (c b) f ≠ ⊤) →
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q)) ∧
      ∃ e : Fin m ≃ MaximalSpectrum (curveNormalisation I q), ∀ b,
        Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ (e b).asIdeal) = 1 ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime (e b).asIdeal)
              (algebraMap (curveNormalisation I q) (Localization.AtPrime (e b).asIdeal)
                (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
            branchOrder (c b) f

end

end GroundTheory.Heights₂.Heights
