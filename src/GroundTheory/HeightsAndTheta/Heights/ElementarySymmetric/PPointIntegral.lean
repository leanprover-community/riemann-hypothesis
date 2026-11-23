module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace PointIntegral

variable {n : ℕ}

theorem zeroSet_ker_eval (p : Fin n → ℂ) :
    zeroSet (RingHom.ker (MvPolynomial.eval p)) = {p} := by
  ext x
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, RingHom.mem_ker]
  constructor
  · intro h
    funext i
    have := h (X i - C (p i)) (by simp)
    simpa [sub_eq_zero] using this
  · rintro rfl q hq
    exact hq

theorem isFiniteProjection (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by
  have hsurj : Function.Surjective (projHom (RingHom.ker (MvPolynomial.eval p)) A) := by
    intro q
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨C (eval p q), ?_⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp
  refine ⟨?_, ?_⟩
  · intro P Q hPQ
    obtain ⟨a, rfl⟩ : ∃ a, P = C a := ⟨AddMonoidAlgebra.coeff P 0, (eq_C_of_isEmpty P)⟩
    obtain ⟨b, rfl⟩ : ∃ b, Q = C b := ⟨AddMonoidAlgebra.coeff Q 0, (eq_C_of_isEmpty Q)⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk] at hPQ
    rw [Ideal.Quotient.eq, RingHom.mem_ker] at hPQ
    simp [sub_eq_zero] at hPQ
    rw [hPQ]
  · exact RingHom.Finite.of_surjective _ hsurj

theorem proof : PointIntegral.Statement := by
  intro n p f φ
  set J := RingHom.ker (MvPolynomial.eval p)
  have hZ : zeroSet J = {p} := zeroSet_ker_eval p
  have hex : ∃ A : Matrix (Fin 0) (Fin n) ℂ, IsFiniteProjection J A :=
    ⟨0, isFiniteProjection p 0⟩
  rw [varInt, dite_eq_left hex]
  set A := hex.choose
  have hsheet : IsSheetAt J A p (fun _ => p) := by
    refine ⟨Set.univ, isOpen_univ, trivial, differentiableOn_const _, rfl, ?_, Set.univ,
      Filter.univ_mem, ?_⟩
    · intro y _
      exact ⟨Subsingleton.elim _ _, by rw [hZ]; rfl⟩
    · intro x hx _
      rw [hZ] at hx
      exact hx.1
  have hfib : ∀ y, fibre J A y = {p} := by
    intro y
    ext x
    simp only [fibre, Set.mem_ofPred_eq, hZ, Set.mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
  have hdens : ∀ y, chartDens J A f φ y = f p := by
    intro y
    rw [chartDens, sheetSum, hfib y, finsum_mem_singleton]
    have hs : ∃ s, IsSheetAt J A p s := ⟨_, hsheet⟩
    rw [dite_eq_left hs]
    simp [ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  rw [chartInt]
  simp_rw [hdens]
  simp [Measure.real, MeasureTheory.volume_pi]

end PointIntegral

end

end GroundTheory.Heights₂.Heights
