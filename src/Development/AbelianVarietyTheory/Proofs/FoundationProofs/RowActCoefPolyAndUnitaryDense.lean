module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Formalism.LocalToGlobal.Columns.PolyFn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem exists_poly_rowAct_coef (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P := by
  induction f using MvPolynomial.induction_on generalizing l with
  | C a => exact ⟨C (l (C a)), fun g => by simp [rowAct]⟩
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp l
    obtain ⟨Q, hQ⟩ := hq l
    exact ⟨P + Q, fun g => by simp only [map_add (f := _), hP, hQ]⟩
  | mul_X p v hp =>
    choose P hP using fun b : Fin n => hp (l ∘ₗ LinearMap.mulRight ℂ (X (b, v.2)))
    refine ⟨∑ b, X (v.1, b) * P b, fun g => ?_⟩
    have e : rowAct ℂ g (X v) = ∑ b, g v.1 b • X (b, v.2) := by
      simp [rowAct, smul_eq_C_mul]

    rw [map_mul, e, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
    rfl

theorem eq_zero_of_vanish_unitaryGroup (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) : P = 0 := by
  have hinj : Function.Injective (fun x : Fin n × Fin n => ((), x) : Fin n × Fin n → Unit × Fin n × Fin n) :=
    fun x y e => congrArg Prod.snd e
  apply rename_injective _ hinj
  rw [map_zero]
  refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := Unit) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
  rw [eval_rename]
  have := h (u ()) (Matrix.mem_unitaryGroup_iff'.2 (hu ()))
  simpa [Function.comp_def] using this

theorem rowAct_coef_poly_and_unitary_dense :
    (∀ (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ) (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)),
      ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
        l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P) ∧
    ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
      (∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) → P = 0 :=
  ⟨exists_poly_rowAct_coef, eq_zero_of_vanish_unitaryGroup⟩

end GlobalTheory.Branching
