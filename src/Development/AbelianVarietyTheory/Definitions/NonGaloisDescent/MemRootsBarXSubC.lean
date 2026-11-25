module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
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
namespace GlobalTheory.GLq.Model
open Polynomial Formalism.CyclotomicNorms

variable (g : ℕ) [hg : Fact g.Prime]


open Formalism.MainNotions.ArithmeticCylinders
variable {g}

theorem thetaOf_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  apply GlobalTheory.GLq.LabelModel.thetaOf_pow <;> assumption

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  rw [toG, dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem tl_self {n : ℕ} (M : Mt g n) : tl n M = M := by
  ext i j
  simp [tl, entN]

theorem hc_full {n : ℕ} (α : Gn g n → ℂ) (hα : IsClass α) : hc n 0 α (fun _ => 1) n = α := by
  funext x

  have hpar : ∀ M : Mt g n, InPar n M := fun M i j _ hi => absurd i.isLt (not_lt.mpr hi)
  have hα' : ∀ y : Gn g n, α (y⁻¹ * x * y) = α x := fun y => by
    simpa using hα x y⁻¹
  have hcard : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [hc, hcT, hpar, if_true, mul_one, tl_self, toG_coe, hα', Finset.sum_const,
    Finset.filter_true, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

end GlobalTheory.GLq.Model
