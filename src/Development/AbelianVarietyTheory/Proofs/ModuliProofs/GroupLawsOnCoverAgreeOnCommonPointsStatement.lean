module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GroupLawsOnCoverAgreeOnCommonPoints
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.group_laws_on_cover_agree_on_common_points : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (B : ∀ i j, Over (U i ⊓ U j).toScheme) [∀ i j, GrpObj (B i j)] (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j, IsGrpPullback (B i j) (G i) (S.homOfLE inf_le_left) (a i j)) → (∀ i j, IsGrpPullback (B i j) (G j) (S.homOfLE inf_le_right) (b i j)) → (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (x * y).left ≫ ψ i = (x' * y').left ≫ ψ j ∧ (x⁻¹).left ≫ ψ i = (x'⁻¹).left ≫ ψ j) ∧ ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (1 : Out.baseOver (U j).toScheme ⟶ G j).left ≫ ψ j := by
  first | exact @GlobalTheory.CoverOpCompat.opCompat | exact GlobalTheory.CoverOpCompat.opCompat | (intros; apply GlobalTheory.CoverOpCompat.opCompat <;> assumption)
