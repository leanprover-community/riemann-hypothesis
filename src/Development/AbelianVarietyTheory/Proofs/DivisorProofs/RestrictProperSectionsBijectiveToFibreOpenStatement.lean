module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictProperSectionsBijectiveToFibreOpen
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_proper_surjective_sections_bijective_over_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  first | exact @GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | exact GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | (intros; apply GlobalTheory.restrict_proper_sections_bijective_to_fibre_open <;> assumption)
