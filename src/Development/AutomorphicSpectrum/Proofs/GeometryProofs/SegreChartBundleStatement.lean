module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.segre_chart_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (W : ChartBundle ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) r E) (L : Lat ξ E), CoordTie ℤ ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) W.lat → ∀ (c : (k : K) → J k) (f : Ω) (b : Fin r → E), GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y c ≠ 0 → f ∈ chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c → f ≠ 0 → (GroundTheory.Heights₂.Heights.LowerBoundFree.IsFrameOver y W c f b ↔ ∀ p : Cpt ξ, InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p → unitAt ξ p f → L.IsFrameAt b p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | exact GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | (intros; apply GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt <;> assumption)
