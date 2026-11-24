module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvr
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.exists_common_pullback_semiAbelian_dvr : ∀ (Y : Scheme.{0}) (G : Over Y) [GrpObj G], IsSemiAbelian G → ∀ (V : Type) [CommRing V] [IsDomain V] (Gu : Over (Sp V)) [GrpObj Gu], IsSemiAbelian Gu → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (fV : V →+* V') (ξ : Sp V' ⟶ Y) (AK : Over (Sp (FractionRing V'))) [GrpObj AK] (α : AK.left ⟶ Gu.left) (Ψ : AK.left ⟶ G.left), IsGrpPullback AK Gu (spMap ((algebraMap V' (FractionRing V')).comp fV)) α → IsGrpPullback AK G (spMap (algebraMap V' (FractionRing V')) ≫ ξ) Ψ → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left) (ω : AK.left ⟶ G'.left), IsGrpPullback G' Gu (spMap fV) β ∧ IsGrpPullback G' G ξ β' ∧ ω ≫ G'.hom = AK.hom ≫ spMap (algebraMap V' (FractionRing V')) ∧ ω ≫ β = α ∧ ω ≫ β' = Ψ ∧ ∀ (F : Gu ⟶ Gu) (f : G ⟶ G) (eK : AK ⟶ AK), eK.left ≫ α = α ≫ F.left → eK.left ≫ Ψ = Ψ ≫ f.left → ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ F.left ∧ F'.left ≫ β' = β' ≫ f.left := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr | exact GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr | (intros; apply GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr <;> assumption)
