module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.pair_kEquivariant_of_lieAlgebra_compat : ∀ (p q : ℕ) (T : GrpData p q), (∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y})) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : Mat p q → E →ₗ[ℂ] E) (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, IsKC Y → ∀ w, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ w)) (j₁ (a Y w)) 0 ∧ HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ w)) (j₂ (a Y w)) 0) → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') := by
  first | exact @GlobalTheory.RealPar.pair_kEquivariant_of_lie | exact GlobalTheory.RealPar.pair_kEquivariant_of_lie | (intros; apply GlobalTheory.RealPar.pair_kEquivariant_of_lie <;> assumption)
