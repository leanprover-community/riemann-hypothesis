module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSkewDetUnitOfAvoidance
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

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance' : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R), (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R), (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ), (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det → ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) → ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) := by
  first | exact @GlobalTheory.exists_conj_skew_det_unit_of_avoidance | exact GlobalTheory.exists_conj_skew_det_unit_of_avoidance | (intros; apply GlobalTheory.exists_conj_skew_det_unit_of_avoidance <;> assumption)
