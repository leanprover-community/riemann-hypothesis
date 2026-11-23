module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionLiftSpecialFibreOfGenericRational
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_torsion_lift_specialFibre_of_generic_rational : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x) → UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (C : Type) [Field C] [IsAlgClosed C] (ga : FractionRing V →+* C) (m : ℕ), IsUnit (m : V) → (∀ y : Over.mk (spMap ga ≫ jK V) ⟶ G, y ^ m = 1 → ∃ x : Sp (FractionRing V) ⟶ G.left, spMap ga ≫ x = y.left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∀ x : Over.mk (spMap f) ⟶ G, x ^ m = 1 → ∃ h : baseOver (Sp V) ⟶ G, h ^ m = 1 ∧ spMap f ≫ h.left = x.left := by
  first | exact @GlobalTheory.exists_torsion_lift_of_generic_rational | exact GlobalTheory.exists_torsion_lift_of_generic_rational | (intros; apply GlobalTheory.exists_torsion_lift_of_generic_rational <;> assumption)
