module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLe
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

theorem _root_.GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  first | exact @GlobalTheory.SiegBaseChange.pullbackTriple_of_le | exact GlobalTheory.SiegBaseChange.pullbackTriple_of_le | (intros; apply GlobalTheory.SiegBaseChange.pullbackTriple_of_le <;> assumption)
