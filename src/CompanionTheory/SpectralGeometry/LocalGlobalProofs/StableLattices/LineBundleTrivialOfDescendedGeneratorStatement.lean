module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.line_bundle_trivial_of_descended_generator : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f →
    ∀ (D : LB Q), D.IsLB → ∀ (t : LB.Gen (D.pull f)), t.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ P), a ≫ f = b ≫ f → ∀ (w : W) (i : D.ι), f (a w) ∈ D.U i →
        gm a w ((D.pull f).U fun _ => i) (t.s fun _ => i) = gm b w ((D.pull f).U fun _ => i) (t.s fun _ => i)) →
      Triv D := by
  first | exact @GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen | exact GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen | (intros; apply GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen <;> assumption)
