module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianPullbackAbelianOverOpen
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.semiAbelian_pullback_abelian_over_open : ∀ {S X : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hX : IsSeparated (toZ X)) (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (H : Over S) [GrpObj H] (hH : IsSemiAbelian H) (U₀ U : S.Opens) (hU₀ : (U₀ : Set S).Nonempty) (hU : (U : Set S).Nonempty) (u' : U₀.toScheme ⟶ X) (c : U.toScheme ⟶ X) (A₀ : Over U₀.toScheme) [GrpObj A₀] (e₀ : A₀.left ⟶ H.left) (e₁ : A₀.left ⟶ A.left) (h₀ : IsGrpPullback A₀ H U₀.ι e₀) (h₁ : IsGrpPullback A₀ A u' e₁) (K : Type) [Field K] (pt : Sp K ⟶ S) (hpt : Set.range pt = {genericPoint S}) (hgen : ∀ (x : Sp K ⟶ U.toScheme) (y : Sp K ⟶ U₀.toScheme), x ≫ U.ι = pt → y ≫ U₀.ι = pt → x ≫ c = y ≫ u'), ∃ e : pullback A.hom c ⟶ H.left, IsGrpPullback ((Over.pullback c).obj A) H U.ι e := by
  first | exact @GlobalTheory.FactorOverOpen.factor_over_open | exact GlobalTheory.FactorOverOpen.factor_over_open | (intros; apply GlobalTheory.FactorOverOpen.factor_over_open <;> assumption)
