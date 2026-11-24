module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
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
import Mathlib.Tactic.Linter.Style
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

open Matrix

namespace LateralTheory.DivDb.TangentFieldExtension
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

theorem ev_DX (Y x : Mat C N) (f : MP C N) : ev x (DX Y f) = dAt f x (Y * x) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dAt, ev, DX, MvPolynomial.derivation_C]
  | add f g hf hg =>
    rw [map_add (f := _), ev, map_add (f := _), ← ev, ← ev, hf, hg]
    simp only [dAt, map_add (f := _), ev, add_mul, Finset.sum_add_distrib]
  | mul_X f q hf =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [ev, map_add (f := _), map_mul] at hf ⊢
    rw [hf]

    simp only [DX, MvPolynomial.mkDerivation_X, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    dAt, ev, Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.pderiv_X, add_mul,
    Finset.sum_add_distrib, Matrix.mul_apply]
    congr 1
    · simp [Pi.single_apply, apply_ite (MvPolynomial.eval _)]
    · rw [Finset.mul_sum]; simp only [mul_assoc]

theorem TanField_of (hChain : Chain) : TanField := by
  intro C _ N S Y
  constructor
  · intro hY f hf s hs
    obtain ⟨f', hev, hd⟩ := hChain C N N (LinearMap.mulRight C s) f
    have hf' : f' ∈ Van (S : Set (Mat C N)) := fun x hx => by
      rw [hev, LinearMap.mulRight_apply]; exact hf _ (S.mul_mem hx hs)
    have h1 : dAt f' 1 Y = 0 := hY f' hf'
    rw [hd] at h1
    simp only [LinearMap.mulRight_apply, one_mul] at h1
    show ev s (DX Y f) = 0
    rw [ev_DX]; exact h1
  · intro h f hf
    have h1 : ev 1 (DX Y f) = 0 := h f hf 1 S.one_mem
    rw [ev_DX, mul_one] at h1
    exact h1

end LateralTheory.DivDb.TangentFieldExtension
