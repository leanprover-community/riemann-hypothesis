module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLeadIdealDim
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearFormCut
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHomogDimZeroPow
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem leadIdeal_isHomogeneous (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    (leadIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous _ _)⟩)

theorem linIdeal_isHomogeneous {d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    (linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℂ j).C_mul (A i j)))⟩)

theorem linIdeal_cons {k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (B : Matrix (Fin 1) (Fin n) ℂ) :
    linIdeal (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = linIdeal A ⊔ linIdeal B := by
  have h : linPoly (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) =
      Fin.cons (linPoly B 0) (linPoly A) := by
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hB : Set.range (linPoly B) = {linPoly B 0} := by
    rw [Set.range_unique]
    rfl
  rw [linIdeal, linIdeal, linIdeal, h, Fin.range_cons, hB, Set.insert_eq, Ideal.span_union, sup_comm]

theorem ConeAvoidsExists.proof (hlead : LeadIdealDim.Statement) (hcut : LinearFormCut.Statement)
    (hpow : HomogDimZeroPow.Statement) : ConeAvoidsExists.Statement := by
  intro n d J _ hd
  have key : ∀ k, k ≤ d → ∃ A : Matrix (Fin k) (Fin n) ℂ,
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (leadIdeal J ⊔ linIdeal A)) ≤
        ((d - k : ℕ) : WithBot ℕ∞) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, ?_⟩
      have h0 : linIdeal (0 : Matrix (Fin 0) (Fin n) ℂ) = ⊥ := by
        rw [linIdeal, Set.range_eq_empty, Ideal.span_empty]
      rw [h0, sup_bot_eq, Nat.sub_zero, ← hd]
      exact hlead n J
    | succ k ih =>
      intro hk
      obtain ⟨A, hA⟩ := ih (by omega)
      have hdk : d - k = (d - (k + 1)) + 1 := by omega
      rw [hdk] at hA
      obtain ⟨B, hB⟩ := hcut n _ _ hA
      refine ⟨Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ), ?_⟩
      rw [linIdeal_cons, ← sup_assoc]
      exact hB
  obtain ⟨A, hA⟩ := key d le_rfl
  rw [Nat.sub_self, Nat.cast_zero] at hA
  obtain ⟨N, hN⟩ := hpow n _ ((leadIdeal_isHomogeneous J).sup (linIdeal_isHomogeneous A)) hA
  exact ⟨A, N, hN⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
