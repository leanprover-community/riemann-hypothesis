module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open TensorProduct

private theorem ladder {X Y : Type} [DecidableEq X] [DecidableEq Y] (f : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ)) (f' : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
    (h : ∀ x y, f' (Finsupp.single x 1) y = (f (Finsupp.single x 1) y : ℤ)) (u : ℂ ⊗[ℤ] (X →₀ ℤ)) :
    f' (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X u) = TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y (f.lTensor ℂ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul c v =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
    | single x n =>
      have e1 : TensorProduct.finsuppScalarRight ℤ ℤ ℂ X (c ⊗ₜ[ℤ] Finsupp.single x n)
          = ((n : ℂ) * c) • Finsupp.single x (1 : ℂ) := by
        ext x'
        rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
        by_cases hx : x = x'
        · subst hx; simp
        · simp [Finsupp.single_apply, hx]
      have e2 : Finsupp.single x n = n • Finsupp.single x (1 : ℤ) := by simp
      ext y
      rw [e1, map_smul, LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, e2, map_smul,
        Finsupp.smul_apply, Finsupp.smul_apply, h]
      simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      push_cast
      ring

theorem UpperTheory.exactBase_integral_to_complex :
    UpperTheory.V.Af.BA.ExactBase := by
  intro X Y Z f g f' g' hf hg hfg
  classical
  have hex := Module.Flat.lTensor_exact ℂ hfg
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Z).toAddEquiv
    (f₁₂ := (f.lTensor ℂ).toAddMonoidHom) (f₂₃ := (g.lTensor ℂ).toAddMonoidHom)
    (g₁₂ := f'.toAddMonoidHom) (g₂₃ := g'.toAddMonoidHom) ?_ ?_ hex
  · exact AddMonoidHom.ext fun u => ladder f f' hf u
  · exact AddMonoidHom.ext fun u => ladder g g' hg u
