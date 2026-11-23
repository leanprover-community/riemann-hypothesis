module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_right_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂) → ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, conv μ E k k' (x * k₂.1) = conv μ E k k' x * E.ρ k₂ := by
  intro _ n _ _ μ _ E k k' _ _ hk' x hx k₂
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : E.ρ k₂ * E.ρ k₂⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : E.ρ k₂⁻¹ * E.ρ k₂ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let L : (E.V →L[ℂ] E.V) ≃L[ℂ] (E.V →L[ℂ] E.V) :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂))
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂⁻¹))
      (fun A => by simp [mul_assoc, hinv]) (fun A => by simp [mul_assoc, hinv'])
  have hL : ∀ A, L A = A * E.ρ k₂ := fun A => rfl
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 (y⁻¹ : G n).isUnit
      exact this.ne_zero
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  unfold conv
  rw [← hL, ← L.integral_comp_comm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change k y.val * k' ((y⁻¹ : G n).val * (x * k₂.1)) = L (k y.val * k' ((y⁻¹ : G n).val * x))
  rw [hL, ← mul_assoc, hk' _ (hmem y) k₂, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
