module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureMapClosedFibreLocalHom
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cubicalStructureMap_closedFibre_localHom : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), IsLocalHom φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (hβ : IsGrpPullback G' G (spMap φ) β) (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G') (w : LB.Iso P'.L.L (P.L.L.pull β)), GlobalTheory.UU.IsCPMap P' P (spMap φ) β hβ.1.w w → ∀ (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)) (P'₀ : GlobalTheory.UU.CP (thickObj W (maximalIdeal W) 0 G')), GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P → GlobalTheory.UU.IsLevelCP (maximalIdeal W) 0 P'₀ P' → ∃ (ρ : R ⧸ maximalIdeal R ^ (0 + 1) →+* W ⧸ maximalIdeal W ^ (0 + 1)) (β₀ : (thickObj W (maximalIdeal W) 0 G').left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (hβ₀ : IsGrpPullback (thickObj W (maximalIdeal W) 0 G') (thickObj R (maximalIdeal R) 0 G) (spMap ρ) β₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ := by
  first | exact @GlobalTheory.UU.ClosedFib.exists_isCPMap_closedFibre | exact GlobalTheory.UU.ClosedFib.exists_isCPMap_closedFibre | (intros; apply GlobalTheory.UU.ClosedFib.exists_isCPMap_closedFibre <;> assumption)
