module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.IsTensorProduct
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorPushout

theorem tensor_equiv_baseChange_tensor :
    ∀ (K A B R X Y : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A]
      [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R]
      [IsScalarTower K B R] [Algebra.IsPushout K A B R] [AddCommGroup X] [Module K X] [Module A X]
      [IsScalarTower K A X] [AddCommGroup Y] [Module K Y] [Module B Y] [IsScalarTower K B Y],
      ∃ t : X ⊗[K] Y ≃ₗ[K] (R ⊗[A] X) ⊗[R] (R ⊗[B] Y),
        ∀ x y, t (x ⊗ₜ y) = ((1 : R) ⊗ₜ[A] x) ⊗ₜ[R] ((1 : R) ⊗ₜ[B] y) := by
  intro K A B R X Y
  intros
  refine ⟨((TensorProduct.AlgebraTensorModule.cancelBaseChange K A A X Y).symm.restrictScalars K).trans <|
    (((Algebra.IsPushout.cancelBaseChange K A B R Y).symm.lTensor X).restrictScalars K).trans <|
    ((TensorProduct.comm A X (R ⊗[B] Y)).restrictScalars K).trans <|
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R R (R ⊗[B] Y) X).symm.restrictScalars K).trans <|
    ((TensorProduct.comm R (R ⊗[B] Y) (R ⊗[A] X)).restrictScalars K), fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, TensorProduct.comm_tmul]

end GlobalTheory.CompanionTheory.TensorPushout
