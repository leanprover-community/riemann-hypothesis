module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem fockAct1_Eab_inl_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inr b)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inr b) G) := by
  intro P Q R h k a b G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have hterm : ∀ c : Fin R, omE ((Sum.inl a : Ix P Q), (Sum.inl c : Ix R 0)) (Sum.inr b, Sum.inl c)
      (embR P Q R h k G) = (X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)) * embR P Q R h k G := by
    intro c
    simp [omE, raiB, lowB, linePos, mul_assoc]
  simp only [hterm, ← Finset.sum_mul]
  simp only [opR, mulM, embR, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, LinearMap.mulRight_apply, map_mul, aeval_X, mR]
  ring

end GlobalTheory.CharPair
