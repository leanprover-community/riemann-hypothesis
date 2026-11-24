module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_proper_integral_model : ∀ (Ω : Type) [Field Ω] (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → ∃ (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of o)), CoordTie o ξ x ∧ (∀ q : X, genPt ξ ⤳ q) ∧ IsIntegral X ∧ IsProper s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap o Ω)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_cl_scheme | exact GlobalTheory.CompanionTheory.Ar.exists_cl_scheme | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_cl_scheme <;> assumption)
