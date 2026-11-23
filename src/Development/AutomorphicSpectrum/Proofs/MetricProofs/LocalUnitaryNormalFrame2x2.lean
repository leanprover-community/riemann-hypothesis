module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrameStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBoundStatement
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

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near :
    ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) →
      (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) →
      ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧
        IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧
        (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧
        (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  intro d G y hpd hC
  let Gh : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ := fun y' => (1 / 2 : ℂ) • (G y' + (G y')ᴴ)
  have hent : ∀ y' p q, Gh y' p q = (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) := by
    intro y' p q
    simp [Gh, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
    ring
  have hherm : ∀ y', (Gh y').IsHermitian := by
    intro y'
    ext p q
    rw [Matrix.conjTranspose_apply, hent, hent]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      apply Complex.ext <;> simp
    simp only [RCLike.star_def, map_mul, map_add (f := _), Complex.conj_conj, hhalf]
    ring
  have hEq : ∀ᶠ y' in 𝓝 y, Gh y' = G y' := by
    filter_upwards [hpd] with y' h
    have e : (G y')ᴴ = G y' := h.isHermitian.eq
    ext p q
    simp only [Gh, e, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hy : Gh y = G y := hEq.self_of_nhds
  have hpdy : (Gh y).PosDef := by
    rw [hy]
    exact hpd.self_of_nhds
  have hCh : ∀ p q, ContDiffAt ℝ 2 (fun y' => Gh y' p q) y := by
    intro p q
    have h1 := hC p q
    have h2 : ContDiffAt ℝ 2 (fun y' => (starRingEnd ℂ) (G y' q p)) y :=
      Complex.conjCLE.contDiff.contDiffAt.comp y (hC q p)
    have e : (fun y' => Gh y' p q) = fun y' => (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) :=
      funext fun y' => hent y' p q
    rw [e]
    exact contDiffAt_const.mul (h1.add h2)
  obtain ⟨g, hg, hu, h1, hd⟩ := GlobalTheory.T.exists_holomorphic_normal_frame d Gh y hpdy hherm hCh
  refine ⟨g, hg, hu, ?_, GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry G g y hC hg, ?_, ?_⟩
  · have hc : ∀ p q, ContinuousAt (fun y' => g y' p q) y := fun p q => (hg p q).continuous.continuousAt
    have hdetc : ContinuousAt (fun y' => (g y').det) y := by
      simp only [Matrix.det_fin_two]
      exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
    have hne : ∀ᶠ y' in 𝓝 y, (g y').det ≠ 0 := hdetc.eventually_ne hu.ne_zero
    filter_upwards [hpd, hne] with y' ha hb
    exact (GlobalTheory.T.log_sine_mobius_transform (G y') (g y') ha (isUnit_iff_ne_zero.mpr hb)).1
  · rw [← hy]
    exact h1
  · intro p q
    have hev : (fun y' => ((g y')ᴴ * G y' * g y') p q) =ᶠ[𝓝 y] fun y' => ((g y')ᴴ * Gh y' * g y') p q := by
      filter_upwards [hEq] with y' h
      rw [h]
    rw [hev.fderiv_eq]
    exact hd p q
