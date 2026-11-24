module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoMul

theorem wirt_const_mul {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirt τ bar (fun z => c * g z) = fun z => c * wirt τ bar g z := by
  funext z
  have h : fderiv ℝ (fun z => c * g z) z = c • fderiv ℝ g z := by
    have := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) c) z
    simpa [Pi.smul_def, smul_eq_mul] using this
  simp only [wirt, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtWord_const_mul {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirtWord ws (fun z => c * g z) = fun z => c * wirtWord ws g z := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [wirtWord_cons, wirtWord_cons, ih, wirt_const_mul]

theorem isGood_mul (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ)
    (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ) (hk : DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane)
    (hP : GlobalTheory.HeckeTwo.IsGood P) : GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun σ hσ => contDiffOn_const.mul (h1 σ hσ), fun w z hz => ?_⟩
  simp only [wirtWord_const_mul]
  exact hk.mul (h2 w z hz)

end GlobalTheory.HeckeTwoMul
