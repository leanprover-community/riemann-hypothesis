module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ProjEig

open Module NumberField

section

variable {E : Type} [Field E] [NumberField E]

theorem trace_dualInt_mul (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x : E) :
    Algebra.trace ℚ E (dualInt E k * x) = (integralBasis E).repr x k := by
  classical
  have h : ∀ l, Algebra.trace ℚ E (dualInt E k * integralBasis E l) = if l = k then 1 else 0 := by
    intro l
    have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
      (traceForm_nondegenerate ℚ E) (integralBasis E) k l
    rw [Algebra.traceForm_apply] at this
    unfold dualInt
    convert this
  conv_lhs => rw [← (integralBasis E).sum_repr x]

  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, h]
  simp

theorem mul_dualInt_eq (a : 𝓞 E) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * dualInt E l =
      ∑ k, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : E) *
        dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr ((a : E) * dualInt E l)
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm (a : E),
    mul_assoc, trace_dualInt_mul, integralBasis_apply]
  have : (a : E) * algebraMap (𝓞 E) E (RingOfIntegers.basis E k)
      = algebraMap (𝓞 E) E (a * RingOfIntegers.basis E k) := by simp
  rw [this, integralBasis_repr_apply, Algebra.smul_def]
  simp [dualInt]

theorem sum_dualInt_mul :
    ∑ k, dualInt E k * ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
  classical
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun y => ?_

  rw [Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum,
  Algebra.trace_eq_matrix_trace (integralBasis E) y, sub_eq_zero, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, trace_dualInt_mul, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    integralBasis_apply, mul_comm y]

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem mem_eigSp_iff_apply (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem rho_mul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    ρ a * eigProj ρ σ = σ (a : E) • eigProj ρ σ := by
  classical
  unfold eigProj
  rw [Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ k, ρ a * (σ (dualInt E k) • ρ (RingOfIntegers.basis E k)) =
      ∑ l, (σ (dualInt E k) *
        (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : K)) •
          ρ (RingOfIntegers.basis E l) := by
    intro k
    rw [mul_smul_comm, ← map_mul]
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E k)]

    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, mul_smul, Int.cast_smul_eq_zsmul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_

  rw [smul_smul, ← map_mul, mul_dualInt_eq, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul σ, map_intCast, mul_comm]

theorem eigProj_mul_rho_comm (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  unfold eigProj
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, mul_comm]

end

theorem eigProj_spec : ∀ (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
    (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K),
    (∀ x, eigProj ρ σ x ∈ eigSp ρ σ) ∧ (∀ x ∈ eigSp ρ σ, eigProj ρ σ x = x) ∧
    (∀ σ' : E →+* K, σ' ≠ σ → ∀ x ∈ eigSp ρ σ', eigProj ρ σ x = 0) ∧
    ∀ a : 𝓞 E, eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  intro K _ _ V _ _ E _ _ ρ σ
  refine ⟨fun x => ?_, fun x hx => ?_, fun σ' hσ x hx => ?_, eigProj_mul_rho_comm ρ σ⟩
  · rw [mem_eigSp_iff_apply]
    intro a
    rw [← Module.End.mul_apply, rho_mul_eigProj, LinearMap.smul_apply]
  · rw [mem_eigSp_iff_apply] at hx
    unfold eigProj
    rw [LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, hx, smul_smul, ← map_mul]

    rw [← Finset.sum_smul, ← map_sum, sum_dualInt_mul, map_one, one_smul]
  · rw [mem_eigSp_iff_apply] at hx
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, σ' (a : E) ≠ σ (a : E) := by
      by_contra hcon
      push Not at hcon
      exact hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hcon))
    have h1 : eigProj ρ σ (ρ a x) = ρ a (eigProj ρ σ x) := by
      rw [← Module.End.mul_apply, eigProj_mul_rho_comm, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ a), rho_mul_eigProj, LinearMap.smul_apply, hx, map_smul,
      ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
    exact h1.resolve_left (sub_ne_zero.mpr ha)

end GlobalTheory.CompanionTheory.Ar.HT.ProjEig
