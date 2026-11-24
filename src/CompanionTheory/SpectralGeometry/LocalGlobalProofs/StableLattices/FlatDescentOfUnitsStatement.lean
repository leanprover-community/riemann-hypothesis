module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.flat_descent_of_units : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f → ∀ V : Q.Opens,
    Function.Injective (pullU f V) ∧ ∀ a : Γ(P, f ⁻¹ᵁ V)ˣ,
      (∀ (W : Scheme.{0}) (b c : W ⟶ P), b ≫ f = c ≫ f → ∀ w : W, f (b w) ∈ V →
        gm b w (f ⁻¹ᵁ V) a = gm c w (f ⁻¹ᵁ V) a) → ∃ s : Γ(Q, V)ˣ, pullU f V s = a := by
  first | exact @GlobalTheory.CompanionTheory.FnDesc.units_descend | exact GlobalTheory.CompanionTheory.FnDesc.units_descend | (intros; apply GlobalTheory.CompanionTheory.FnDesc.units_descend <;> assumption)
