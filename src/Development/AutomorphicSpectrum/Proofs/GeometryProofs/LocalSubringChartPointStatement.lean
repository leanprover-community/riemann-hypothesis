module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringChartPoint
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

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.local_subring_chart_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ (F : Type) [Field F] (θ : Ω →+* F) (A : Subring F) [IsLocalRing A], (∀ j, θ (x j / x c) ∈ A) → ∃ (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), InChart ξ x c ⟨centre z, h⟩ ∧ (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartPoint.point_of_local_subring | exact GlobalTheory.CompanionTheory.Ar.ChartPoint.point_of_local_subring | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartPoint.point_of_local_subring <;> assumption)
