module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsometryIntertwinerOfDerivedAction
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.exists_isometry_intertwiner_of_derived_action : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T) (πU : URep T) (E : D.HK.V →ₗ[ℂ] πU.H), Dense (Set.range D.ι) → (∀ y, ‖E y‖ = ‖D.ι y‖) → (∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E y)) (E (D.HK.act Y y)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ j : D.U.H →ₗᵢ[ℂ] πU.H, (∀ y, j (D.ι y) = E y) ∧ ∀ g x, j (D.U.π g x) = πU.π g (j x) := by
  first | exact @GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived | exact GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived | (intros; apply GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived <;> assumption)
