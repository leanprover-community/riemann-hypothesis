module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairOrbitsFiniteAndCardProd
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

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  first | exact @GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum | exact GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum | (intros; apply GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum <;> assumption)
