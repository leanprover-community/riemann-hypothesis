module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Formalism.MainNotions.S Matrix MeasureTheory

theorem _root_.GlobalTheory.T.hilbert_schur_unitary_irreducible_scalar : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g v, ‖π g v‖ = ‖v‖) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ A : H →L[ℂ] H, (∀ g, π g * A = A * π g) → ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  first | exact @GlobalTheory.hilbert_schur | exact GlobalTheory.hilbert_schur | (intros; apply GlobalTheory.hilbert_schur <;> assumption)
