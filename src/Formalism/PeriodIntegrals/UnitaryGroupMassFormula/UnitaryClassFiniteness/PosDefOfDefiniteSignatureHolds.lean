module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.ClassFiniteOf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

theorem Jpq_zero (M : ℕ) : Jpq M 0 = 1 := by
  unfold PI.UJClassFin.Jpq
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem cT_conj {m : Type} (X : Matrix m m ℂ) : cT (starRingEnd ℂ) X = Xᴴ := by
  unfold PI.UJClassFin.cT
  ext i j
  rfl

theorem posDefOfDefiniteSignature_holds : SigPos := by
  intro M A h
  unfold HasSignature at h
  obtain ⟨e, P, hP⟩ := h
  rw [cT_conj, Jpq_zero] at hP
  generalize hBdef : reindex e e A = B at hP
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ,
      Q = ((P⁻¹ : GL (Fin M ⊕ Fin 0) ℂ) : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) := ⟨_, rfl⟩
  have hPQ : (P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) * Q = 1 := by
    rw [hQ]
    exact Units.mul_inv P
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h2 := congrArg (fun v => (P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec, hPQ] using h2
  have hBeq : B = Qᴴ * 1 * Q := by
    calc B = ((P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) * Q)ᴴ * B
          * ((P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ) * Q) := by
          rw [hPQ]; simp
      _ = Qᴴ * ((P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ)ᴴ * B
          * (P : Matrix (Fin M ⊕ Fin 0) (Fin M ⊕ Fin 0) ℂ)) * Q := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * 1 * Q := by rw [hP]
  have hBpos : B.PosDef := by
    rw [hBeq]
    exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj
  have hA : A = B.submatrix e e := by
    rw [← hBdef]
    ext i j
    simp
  rw [hA]
  exact hBpos.submatrix e.injective

end PI.UnitaryGroupMassFormula.UJClassFin
