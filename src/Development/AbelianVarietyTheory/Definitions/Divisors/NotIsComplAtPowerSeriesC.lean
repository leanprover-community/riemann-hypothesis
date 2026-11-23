module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

noncomputable section
open IsLocalRing

namespace GlobalTheory.TChart

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : GlobalTheory.LocM.InvFun ℤ}

theorem Taut.s_ne_zero (C : Taut ζ g n φ) (k : Fin C.m ⊕ Fin C.N) : C.s k ≠ 0 := by
  intro h
  have hflat : C.ψ.Flat := C.compl.2.2.1
  algebraize [C.ψ]

  have hreg : IsSMulRegular C.R
      (algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k)) :=
    IsSMulRegular.of_flat (MvPolynomial.isRegular_X (n := k) (R := C.W)).left.isSMulRegular
  have h0 : algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k) = 0 := h
  rw [h0] at hreg
  exact one_ne_zero (hreg (a₁ := (1 : C.R)) (a₂ := 0) (by simp))

end GlobalTheory.TChart
