module

public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.FormalDegreeBessel.FinalIO
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SumSgnLProdCol
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.GGEq

@[expose] public section

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem qminor_row_alt {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (u : ℂ)
    (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E (x ∘ π) y u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by
  rw [quantumMinorRowSkew_holds A n m E x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem qminor_col_alt {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (u : ℂ) (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E x (y ∘ π) u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by
  rw [quantumMinorColSkew_holds A n m E hE x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem qnCovHat2_of_lin (hLin : PI.QnCovLin) : PI.QnCovHat2 := by
  intro A _ _ n E P Q hE hQP hPQ u a a' β β'
  rcases n with _ | _ | m
  · simp [chat2A]
  · simp [chat2A]
  · have hE' : GlRel (Econj E P Q) := glRelAd A (m + 2) E P Q hE hQP
    have h1 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y π => qminor_row_alt E u x y π) (fun x y π => qminor_col_alt E hE u x y π) β β' a a'
    have h2 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u)
      (fun x y π => qminor_row_alt (Econj E P Q) u x y π)
      (fun x y π => qminor_col_alt (Econj E P Q) hE' u x y π) (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a')
    have h3 := GG_cov (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u) P Q
      (fun x y => hLin A (m + 2) m E P Q hQP x y u) β β' a a'
    have hdet : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
    rw [hdet, one_smul, h1, h2] at h3
    have hne : ((m.factorial : ℂ) * m.factorial) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
        (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
    have h4 := congrArg (fun z => ((m.factorial : ℂ) * m.factorial)⁻¹ • z) h3
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
    exact h4

end PI.QnCovHat2W
