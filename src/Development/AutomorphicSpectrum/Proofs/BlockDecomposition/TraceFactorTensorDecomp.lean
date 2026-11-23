module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfHom
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.HomTrace

theorem trace_pi_blocks {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Type)
    [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, FiniteDimensional ℂ (P i)]
    (S : ∀ i, P i →ₗ[ℂ] P i) :
    LinearMap.trace ℂ (∀ i, P i) (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, LinearMap.trace ℂ (P i) (S i) := by
  have h : (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, (LinearMap.single ℂ P i) ∘ₗ (S i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun j => ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.sum_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij.symm]
    · simp

  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  have h2 : (S i ∘ₗ LinearMap.proj i) ∘ₗ LinearMap.single ℂ P i = S i := by
    refine LinearMap.ext fun x => ?_
    simp
  rw [h2]

theorem trace_of_block_sandwich : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : Type) (W H : ι → Type) [AddCommGroup I] [Module ℂ I] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)] [FiniteDimensional ℂ I] [∀ i, FiniteDimensional ℂ (W i)] [∀ i, Nontrivial (W i)] (R : I ≃ₗ[ℂ] ∀ i, W i →ₗ[ℂ] H i) (F : I →ₗ[ℂ] I) (a : ∀ i, H i →ₗ[ℂ] H i) (b : ∀ i, W i →ₗ[ℂ] W i), (∀ x i, R (F x) i = a i ∘ₗ R x i ∘ₗ b i) → (∀ i, FiniteDimensional ℂ (H i)) ∧ LinearMap.trace ℂ I F = ∑ i, LinearMap.trace ℂ (W i) (b i) * LinearMap.trace ℂ (H i) (a i) := by
  intro ι _ _ I W H _ _ _ _ _ _ _ _ _ R F a b hF
  haveI hP : FiniteDimensional ℂ (∀ i, W i →ₗ[ℂ] H i) := LinearEquiv.finiteDimensional R
  haveI hHom : ∀ i, FiniteDimensional ℂ (W i →ₗ[ℂ] H i) := fun i =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ) (φ := fun i => W i →ₗ[ℂ] H i) i)
      (fun y => ⟨Pi.single i y, by simp⟩)
  haveI hH : ∀ i, FiniteDimensional ℂ (H i) := fun i => finiteDimensional_of_hom (W i) (H i)
  refine ⟨hH, ?_⟩
  have hconj : R.conj F =
      LinearMap.pi fun i => sandwich (a i) (b i) ∘ₗ LinearMap.proj i := by
    rw [LinearEquiv.conj_apply]
    refine LinearMap.ext fun f => funext fun i => ?_
    have := hF (R.symm f) i
    simpa [sandwich] using this
  rw [← LinearMap.trace_conj' F R, hconj, trace_pi_blocks]
  exact Finset.sum_congr rfl fun i _ => trace_sandwich (a i) (b i)

end GlobalTheory.CompanionTheory.HomTrace
