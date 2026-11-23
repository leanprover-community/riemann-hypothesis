module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnita
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, CompleteSpace (H τ)] (σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : (ι → Mt n) → (K →L[ℂ] K)) (v : ∀ τ, H τ) (k : K), (∀ τ, (Hm τ).det ≠ 0 ∧ IsURepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ ‖v τ‖ = 1) → ρ 1 = 1 → (∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, ρ (u * u') = ρ u * ρ u') → (∀ u ∈ UG Hm, ∀ y, ‖ρ u y‖ = ‖y‖) → (∀ u ∈ UG Hm, ⟪k, ρ u k⟫_ℂ = ((‖k‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) → ∃ Φ : ContinuousMultilinearMap ℂ H K, Φ v = k ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ y, Φ (Function.update y τ (σ τ g (y τ))) = ρ (Pi.mulSingle τ g) (Φ y)) ∧ ∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u ∈ UG Hm, z = ρ u k} : Set K) := by
  first | exact @GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq | exact GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq | (intros; apply GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq <;> assumption)
