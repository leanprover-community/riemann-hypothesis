module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmple
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

theorem _root_.GlobalTheory.T.exists_morphism_of_sectionRatios_veryAmple : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  first | exact @GlobalTheory.Mum.exists_morphism_of_secRatio | exact GlobalTheory.Mum.exists_morphism_of_secRatio | (intros; apply GlobalTheory.Mum.exists_morphism_of_secRatio <;> assumption)
