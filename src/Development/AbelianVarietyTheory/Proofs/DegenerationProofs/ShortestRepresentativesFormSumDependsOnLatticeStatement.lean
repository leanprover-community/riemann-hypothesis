module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ShortestRepresentativesFormSumDependsOnLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.shortestRepresentatives_form_sum_depends_on_lattice : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  first | exact @GlobalTheory.OneBasis.sum_adapted_eq | exact GlobalTheory.OneBasis.sum_adapted_eq | (intros; apply GlobalTheory.OneBasis.sum_adapted_eq <;> assumption)
