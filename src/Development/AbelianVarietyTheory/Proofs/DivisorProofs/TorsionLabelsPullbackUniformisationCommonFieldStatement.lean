module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsPullbackUniformisationCommonField
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull


theorem _root_.GlobalTheory.T.torsionLabels_pullback_uniformisation_common_field : ∀ {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], IsCN V → IsCN V' → ∀ (j : V →+* V') (hj : Function.Injective j), IsLocalHom j → ∀ {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left) (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)), IsPullUnif j hD (Iso.refl _) U U' → IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j) → ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] [Algebra (FractionRing V') F'], (∀ r : V, algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) r) = algebraMap (FractionRing V') F' (algebraMap V' (FractionRing V') (j r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A), QkToAkU U.toUnifPre F' k p₁ x₁ → ∃ (p' : QkPt D'.toPre F' k) (x' : TFK (R := V') F' ⟶ A'.A), p'.y = hD.xe.symm p₁.y ∧ QkToAkU U'.toUnifPre F' k p' x' ∧ x'.left ≫ gA = x₁.left := by
  first | exact @GlobalTheory.Poinc.Sep.BaseChangeLabels.qkToAkU_pullback_common_field | exact GlobalTheory.Poinc.Sep.BaseChangeLabels.qkToAkU_pullback_common_field | (intros; apply GlobalTheory.Poinc.Sep.BaseChangeLabels.qkToAkU_pullback_common_field <;> assumption)
