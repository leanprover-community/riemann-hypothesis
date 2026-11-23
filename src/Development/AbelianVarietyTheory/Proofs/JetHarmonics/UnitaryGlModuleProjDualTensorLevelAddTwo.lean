module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNearStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensorStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LowKSubSingleSqrtCkvLeStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearLeOfAddDistLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem algTens_pr_single_lev :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)]
      [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
      (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ)
      (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr →
      Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
      ∀ c s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w)) := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hT hS _ hw c s
  obtain ⟨hlow, hsq⟩ := GlobalTheory.T.lowK_sub_single_sqrt_ckv_le n kk ε μ bv s hS
  obtain ⟨hw1, hw2⟩ := hw
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS1, hS2, hS3, hS4⟩ :=
      GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE.2.1 (fun s => (hF s).2.1) hT h0 hw1 s c
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (add_nonneg h0 (Real.sqrt_nonneg _))
    push_cast
    linarith
  · have h1 := (GlobalTheory.T.wtNear_pr_and_io_of_algTens M n ε E N F io pr (lowK ε μ) (j : ℝ) hT).1 w hw2 s c
    refine wtNear_le_of_add_dist_le (N s) n ε (F s) _ _ _ _ ?_ h1
    have h2 : ∑ a, |lowK ε μ a - lowK ε (μ - Pi.single s 1) a| = 1 := by
      rw [hlow, Finset.sum_eq_single s]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [h2]
    push_cast
    linarith

end GlobalTheory
