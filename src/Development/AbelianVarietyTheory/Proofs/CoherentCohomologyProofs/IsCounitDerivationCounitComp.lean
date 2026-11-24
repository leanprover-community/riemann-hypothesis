module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

namespace GlobalTheory.LeftRightDerivations

variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]

def IsCounitDerivation (φ : H →ₗ[k] k) : Prop :=
  ∀ a b : H, φ (a * b) =
    Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a

noncomputable def contrRight (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H φ

@[simp] theorem contrRight_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrRight φ (a ⊗ₜ[k] b) = φ b • a := by
  simp [contrRight]

theorem contrRight_counit_comul (a : H) :
    contrRight (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by

  simp [contrRight, Coalgebra.lTensor_counit_comul]

theorem contrRight_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrRight φ (s * t) =
      contrRight (Coalgebra.counit (R := k)) s * contrRight φ t +
        contrRight (Coalgebra.counit (R := k)) t * contrRight φ s := by

  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrRight_tmul, hφ b d, Algebra.smul_def, map_add (f := _), map_mul]
      ring

theorem contrRight_one (φ : H →ₗ[k] k) : contrRight φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrRight_tmul]

section Ring

variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

theorem IsCounitDerivation.map_one {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) : φ 1 = 0 := by

  have h := hφ 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  simpa using h

noncomputable def derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrRight φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrRight_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrRight_mul hφ,
      contrRight_counit_comul, smul_eq_mul]

end Ring

end GlobalTheory.LeftRightDerivations
