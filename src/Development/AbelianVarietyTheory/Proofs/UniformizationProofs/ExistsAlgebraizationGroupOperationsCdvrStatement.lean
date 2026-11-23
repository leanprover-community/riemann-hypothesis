module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAlgebraizationGroupOperationsCdvr
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_algebraization_group_operations_cdvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  first | exact @GlobalTheory.GrpAlg.exists_group_operations | exact GlobalTheory.GrpAlg.exists_group_operations | (intros; apply GlobalTheory.GrpAlg.exists_group_operations <;> assumption)
