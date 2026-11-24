module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundlePullbackGenerator
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem _root_.GlobalTheory.T.line_bundle_pullback_generator : ∀ {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (Mn : Submonoid R) [IsLocalization Mn Rm] {X X' Y : Scheme.{0}} {π : X' ⟶ Spec (CommRingCat.of R)} {π' : Y ⟶ Spec (CommRingCat.of Rm)} {κ : Y ⟶ X'}, IsPullback κ π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) → ∀ [CompactSpace X'] [QuasiSeparatedSpace X'] {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}, PGen w → L.IsLB → L'.IsLB → ∀ (th : Out.H0 L 1) (ψ : Y ⟶ X) (n : ℕ) (u : FG L Y), (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), u.sum U h = h ψ * (h (κ ≫ F) ^ n)⁻¹) → ∃ (s : Out.H0 L' n), ∃ t ∈ Mn, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → (gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n).val * sval s (r ≫ κ) z J' = GlobalTheory.TwistLoc.gc (r ≫ κ ≫ π) z t * (sval th (r ≫ ψ) z J * ((u.v r z J)⁻¹).val) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared <;> assumption)
