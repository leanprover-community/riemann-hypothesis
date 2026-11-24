module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndex
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

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.card_roots_closedBall_dominant_coeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  first | exact @GlobalTheory.card_roots_closedBall_eq_dominantIndex | exact GlobalTheory.card_roots_closedBall_eq_dominantIndex | (intros; apply GlobalTheory.card_roots_closedBall_eq_dominantIndex <;> assumption)
