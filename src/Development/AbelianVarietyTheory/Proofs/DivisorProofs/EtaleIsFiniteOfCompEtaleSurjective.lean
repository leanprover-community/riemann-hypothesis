module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFinitePresentationOfEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_isFinite_of_comp_etale_surjective :
    ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) →
      IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  intro X Y Z h f h1 h2 h3 h4 h5 h6
  have : LocallyOfFinitePresentation f := GlobalTheory.T.locally_finite_presentation_of_etale_cover X Y Z h f h1 h2 h3 h4 h5 h6
  exact ⟨etale_of_comp_of_etale_of_surjective h f, isFinite_of_comp_surjective h f⟩

end GlobalTheory
