module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  intro l _ Ω _ _ _ e S A W h
  obtain ⟨φ, hφ, hd⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W h
  have hφ' : φ ∈ H0g W := (Subgroup.commutator_le.2 (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))) hφ
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hφ'
  rw [MonoidHom.mem_ker] at h1 h2
  have hχ : (cycBar ℚ Ω l * (dt W)⁻¹) φ = 1 := by
    simp [h1, h2]
  refine ⟨φ, ?_⟩
  have : mat (dual1 W) φ = mat W φ := by
    unfold dual1
    generalize (cycBar ℚ Ω l * (dt W)⁻¹) = χ at hχ
    simp [mat, tw, hχ]
  rw [this]; exact hd

end GlobalTheory.Ord2
