module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProperStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveDescentOfAffineOpensStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualisedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppTopOfFibreSquareProjectionsEqStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_fibreSquare_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y := by
  intro R _ S Y Z π y p q H r h1 h2
  have A : IsPullback (pullback.fst p p ≫ q) (pullback.snd p p) π (p ≫ y) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback p p) H.flip
  have X : IsPullback r (pullback.snd p p) (pullback.snd π π) q := by
    refine IsPullback.of_right (h₁₂ := pullback.fst π π) ?_ h2 (IsPullback.of_hasPullback π π)
    rw [h1, ← H.w]; exact A
  have := IsPullback.paste_vert X H.flip
  rwa [pullback.condition (f := p), pullback.condition (f := π)]

theorem descend_of_equalised_fibreSquare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ _ _ _ S Y Z π y p q hπ hs hS hy H
  have hinj := GlobalTheory.T.appTop_injective_of_surjective_integral_toSpecDomain R S π hs hS
  have heq := GlobalTheory.T.mem_range_appTop_of_fibreSquare_projections_eq R S π hπ hS hinj
  let r : pullback p p ⟶ pullback π π := pullback.map p p π π q q y H.w H.w
  have h1 : r ≫ pullback.fst π π = pullback.fst p p ≫ q := pullback.lift_fst _ _ _
  have h2 : r ≫ pullback.snd π π = pullback.snd p p ≫ q := pullback.lift_snd _ _ _
  have hP := isPullback_fibreSquare_baseChange R S Y Z π y p q H r h1 h2
  exact GlobalTheory.T.app_injective_descent_of_affineOpens Y Z p fun V hV => ⟨GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper R S Y Z π y p q hπ hy H hinj V hV,
    GlobalTheory.T.mem_range_app_of_flat_baseChange_equalised R S Y Z π y p q hπ hy H r h1 h2 hP heq V hV⟩

end GlobalTheory
