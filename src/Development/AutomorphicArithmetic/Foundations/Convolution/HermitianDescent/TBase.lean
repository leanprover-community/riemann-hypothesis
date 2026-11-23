module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
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

@[expose] public section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.tBase :
    UpperTheory.ConvolutionTheory.D.TBase := by
  intro k R _ _ _ _ A _ _ n b c hc g hg
  haveI : Module.Finite k A := Module.Finite.of_basis b
  let e : A ⊗[k] R ≃ₐ[k] R ⊗[k] A := Algebra.TensorProduct.comm k A R
  let τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R := Algebra.TensorProduct.congr AlgEquiv.refl c
  have hτ : UpperTheory.ConvolutionTheory.D.IsGal τ 2 := (UpperTheory.ConvolutionTheory.D.galBase k R A c 2 hc).2.2.2
  have he : ∀ z, e (τ z) = UpperTheory.ConvolutionTheory.D.io c A (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [e, τ, UpperTheory.ConvolutionTheory.D.io]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) *
      UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
    have h2 : UpperTheory.ConvolutionTheory.D.io c A (g : R ⊗[k] A) *
        UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [Units.inv_eq_of_mul_eq_one_right hg.1] at h2 ⊢
    exact h2
  let a : (A ⊗[k] R)ˣ := Units.map (e.symm : R ⊗[k] A →* A ⊗[k] R) g⁻¹
  have ha : e (a : A ⊗[k] R) = ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) := e.apply_symm_apply _
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 k k A (A ⊗[k] R) τ 2 hτ a (by
    apply e.injective
    rw [Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one, AlgEquiv.one_apply,
      map_mul, he, ha, h1, map_one])
  refine ⟨Units.map (e : A ⊗[k] R →* R ⊗[k] A) z, ?_⟩
  have h3 := congrArg e hz
  rw [map_mul, he, ha] at h3
  change UpperTheory.ConvolutionTheory.D.io c A (e z) = g * e z
  calc UpperTheory.ConvolutionTheory.D.io c A (e z)
      = g * (((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) * UpperTheory.ConvolutionTheory.D.io c A (e z)) := by
        rw [Units.mul_inv_cancel_left]
    _ = g * e z := by rw [h3]
