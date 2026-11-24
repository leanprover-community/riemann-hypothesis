module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace UpperTheory.ConvolutionTheory.BW

private theorem finite_span_of_killed {K X : Type} {d : ℕ} (ρ : K → Matrix (Fin d) (Fin d) ℂ) (ψ : K → X → ℂ)
    (h : ∀ x : K →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ g : X, (x.sum fun k c => c * ψ k g) = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) := by
  let A : (K →₀ ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ := Finsupp.linearCombination ℂ ρ
  let B : (K →₀ ℂ) →ₗ[ℂ] (X → ℂ) := Finsupp.linearCombination ℂ ψ
  have hAB : LinearMap.ker A ≤ LinearMap.ker B := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext g
    have := h x (by simpa [A, Finsupp.linearCombination_apply] using hx) g
    simpa [B, Finsupp.linearCombination_apply, Finsupp.sum_apply'] using this
  haveI : FiniteDimensional ℂ ((K →₀ ℂ) ⧸ LinearMap.ker A) :=
    Module.Finite.equiv A.quotKerEquivRange.symm
  have hr : LinearMap.range ((LinearMap.ker A).liftQ B hAB) = Submodule.span ℂ (Set.range ψ) := by
    rw [Submodule.range_liftQ]
    exact Finsupp.range_linearCombination ℂ
  rw [← hr]
  infer_instance

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep in
theorem UpperTheory.ConvolutionTheory.BW.killedOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KilledOps E := by
  intro E _ _ _ n ρ φ hφ
  refine ⟨fun k x hx g => ?_, ?_⟩
  · have h0 : ((x.mapDomain fun k' => k' * k).sum fun k' c => c • ρ.ρ k') = 0 := by
      rw [Finsupp.sum_mapDomain_index (h := fun k' c => c • ρ.ρ k') (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
      have : (x.sum fun k' c => c • ρ.ρ (k' * k)) = (x.sum fun k' c => c • ρ.ρ k') * ρ.ρ k := by
        rw [Finsupp.sum_mul]
        simp only [map_mul, smul_mul_assoc]
      rw [this, hx, zero_mul]
    have h1 := hφ _ h0 g
    rw [Finsupp.sum_mapDomain_index (h := fun (k' : KA E n) c => c * φ.1 (g * (k' : GA E n))) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at h1
    simp only [Subgroup.coe_mul, ← mul_assoc] at h1
    exact h1
  · unfold GroundTheory.Automorphic.AutomorphicForm.IsKFinite
    exact finite_span_of_killed ρ.ρ _ (fun x hx g => hφ x hx g)
