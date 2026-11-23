module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.glue_schemes_over_opens_along_cocycle : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  first | exact @GlobalTheory.CocycleGlue.glue_over_opens | exact GlobalTheory.CocycleGlue.glue_over_opens | (intros; apply GlobalTheory.CocycleGlue.glue_over_opens <;> assumption)
