module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem UpperTheory.ConvolutionTheory.FX.aeval_single_zero {ι ι' : Type} (q : ι → MvPolynomial ι' ℂ)
    (p : MvPolynomial ι ℂ) :
    aeval (fun i => (AddMonoidAlgebra.single 0 (q i) : EP ι')) p
      = (AddMonoidAlgebra.single 0 (aeval q p) : EP ι') := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, aeval_C]
    rfl
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr, AddMonoidAlgebra.single_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]

private theorem UpperTheory.ConvolutionTheory.FX.lin_delta {ι ι' : Type} [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (i : ι) :
    lin (fun j => if δ i = j then (1 : ℝ) else 0) = (X (δ i) : MvPolynomial ι' ℂ) := by
  unfold lin
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.lin_push {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) :
    lin (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0)) = rename δ (lin v) := by
  unfold lin

  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, map_mul, rename_C, rename_X,
  Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.ren_single {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    ren δ (AddMonoidAlgebra.single v p : EP ι) =
      (AddMonoidAlgebra.single (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0))
        (rename δ p) : EP ι') := by
  have h1 : (fun i => (C ((0 : ι → ℂ) i) + lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i) :
      MvPolynomial ι' ℂ)) = X ∘ δ := by
    funext i
    have := UpperTheory.ConvolutionTheory.FX.lin_delta δ i
    simp only [Pi.zero_apply, map_zero, zero_add, Function.comp]
    exact this
  unfold ren aff lift
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change aeval (fun i => (AddMonoidAlgebra.single 0 (C ((0 : ι → ℂ) i) +
      lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i)) : EP ι')) p *
    (AddMonoidAlgebra.single (Matrix.vecMul v _) (C (expChar 0 (Multiplicative.ofAdd v))) : EP ι') = _
  rw [UpperTheory.ConvolutionTheory.FX.aeval_single_zero, h1, AddMonoidAlgebra.single_mul_single, zero_add]
  have h2 : expChar (0 : ι → ℂ) (Multiplicative.ofAdd v) = 1 := by simp [expChar]
  rw [h2, map_one, mul_one, rename_eq_aeval]

theorem UpperTheory.ConvolutionTheory.FX.piece_ren :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (k : ℕ), piece k (ren δ f) = rename δ (piece k f) := by
  intro ι _ f ι' _ _ δ k
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  obtain ⟨ha', h0', hs'⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι' k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, h0, h0', map_zero]
  | add f g hf hg => rw [map_add (f := _), ha, ha', map_add (f := _), hf, hg]
  | single v p =>

    rw [UpperTheory.ConvolutionTheory.FX.ren_single, hs, hs', map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_pow, rename_C, UpperTheory.ConvolutionTheory.FX.lin_push, rename_homogeneousComponent]
