module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalHomCompletedStalkToDvrOverTrait
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.isLocalHom_completedStalk_to_dvr_over_trait : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (g' : R →+* V') (ξ : Sp V ⟶ M.Z), Irreducible (h ϖ) → ξ (IsLocalRing.closedPoint V) = x → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → IsLocalHom g' := by
  first | exact @GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square | exact GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square | (intros; apply GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square <;> assumption)
