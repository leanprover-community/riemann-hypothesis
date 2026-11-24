module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumOrbitsCountingPrincipleFiniteFibres
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

theorem _root_.GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  first | exact @GlobalTheory.OrbitCounting.counting_principle | exact GlobalTheory.OrbitCounting.counting_principle | (intros; apply GlobalTheory.OrbitCounting.counting_principle <;> assumption)
