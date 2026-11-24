module

public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitary
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

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.delSq_unitary_stable_and_irreducible : ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  first | exact @GlobalTheory.WeylUnitary.delSq_irreducible_unitary | exact GlobalTheory.WeylUnitary.delSq_irreducible_unitary | (intros; apply GlobalTheory.WeylUnitary.delSq_irreducible_unitary <;> assumption)
