module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGrpObjOfLocalGroupLawsOnCover
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_grpObj_of_local_group_laws_on_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (m n : A ⊗ A ⟶ A) (e : Out.baseOver S ⟶ A), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i ∧ (lift x₀ y₀ ≫ n).left = (x⁻¹).left ≫ ψ i) → (∀ i, (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = (U i).ι ≫ e.left) → ∃ _ : GrpObj A, ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i) := by
  first | exact @GlobalTheory.CoverGlue.exists_grpObj_of_cover | exact GlobalTheory.CoverGlue.exists_grpObj_of_cover | (intros; apply GlobalTheory.CoverGlue.exists_grpObj_of_cover <;> assumption)
