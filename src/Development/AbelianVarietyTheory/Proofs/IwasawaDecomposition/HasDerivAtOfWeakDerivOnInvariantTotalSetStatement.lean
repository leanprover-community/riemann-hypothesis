module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOfWeakDerivOnInvariantTotalSet
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (D : Set H) (x w : H), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t y, ‖U t y‖ = ‖y‖) → (∀ y, Continuous fun t => U t y) → Dense (Submodule.span ℂ D : Set H) → (∀ t, ∀ y ∈ D, U t y ∈ D) → (∀ y ∈ D, HasDerivAt (fun t : ℝ => inner ℂ (U t x) y) (inner ℂ w y) 0) → HasDerivAt (fun t : ℝ => U t x) w 0 := by
  first | exact @GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | exact GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | (intros; apply GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total <;> assumption)
