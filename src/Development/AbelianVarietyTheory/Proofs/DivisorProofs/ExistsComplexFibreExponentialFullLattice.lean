module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibreExp

theorem exists_exp_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G))
      (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
        ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hgG y
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  have hj := isGrpPullback_pullback G y
  have hA : IsAbelianScheme ((Over.pullback y).obj G) := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj
  have hgA : SmoothOfRelativeDimension g ((Over.pullback y).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hj.1 hgG
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif _ g hA hgA
  obtain ⟨h1, h2⟩ := GlobalTheory.UnifTangent.tangent_bijection u hgA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hj (𝟙_ _) y (Category.id_comp _).symm
  have he := GlobalTheory.PointUnif.isExp_push hj u h1 h2 Φ hΦ
  exact ⟨fun z => Φ (u.ex z), u.Λ, he, u.discrete, u.full,
    fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)⟩

end GlobalTheory.FibreExp
