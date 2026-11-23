module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
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

open scoped TensorProduct

namespace GlobalTheory.CentralizerMapTensor

theorem cenMap_tmul_eq (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (x : ℚ_[ℓ]) (f : F) :
    GlobalTheory.LKInvGood.cenMap ℓ F B (x ⊗ₜ[ℚ] f) = x ⊗ₜ[ℚ] algebraMap F B f := rfl

theorem commute_cenMap (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) :
    Commute (GlobalTheory.LKInvGood.cenMap ℓ F B a) y := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add a₁ a₂ h₁ h₂ => rw [map_add (f := _)]; exact h₁.add_left h₂
  | tmul x f =>
    rw [cenMap_tmul_eq]
    induction y using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | add y₁ y₂ h₁ h₂ => exact h₁.add_right h₂
    | tmul z b =>
      unfold Commute SemiconjBy
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm x z, Algebra.commutes f b]

end GlobalTheory.CentralizerMapTensor
