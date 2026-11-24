module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointOfTorusPointAtClosedPointField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem _root_.GlobalTheory.T.toricTorsionPoint_of_torusPoint_at_closedPointField : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → IsUnit (k : V) → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), x ^ k = 1 → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β → TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.torAt_of_closedPoint | exact GlobalTheory.Poinc.Sep.Spz.torAt_of_closedPoint | (intros; apply GlobalTheory.Poinc.Sep.Spz.torAt_of_closedPoint <;> assumption)
