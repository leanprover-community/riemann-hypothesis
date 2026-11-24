module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relAmple_of_ample_on_closed_subscheme_localBase : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  first | exact @GlobalTheory.AmpleLocalBase.relAmple_of_closed | exact GlobalTheory.AmpleLocalBase.relAmple_of_closed | (intros; apply GlobalTheory.AmpleLocalBase.relAmple_of_closed <;> assumption)
