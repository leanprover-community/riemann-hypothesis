module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorAlgebraProductDiagramCompat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tensor_algebra_product_diagram_compat : ∀ (K : Type) [Field K] (P Q : Type) [Category.{0} P] [Category.{0} Q] [Finite Q] [Quiver.IsThin Q] (F : P ⥤ CommAlgCat.{0} K) (G : Q ⥤ CommAlgCat.{0} K) (E : P × Q ⥤ CommAlgCat.{0} K) (i₁ : ∀ T : P × Q, F.obj T.1 →ₐ[K] E.obj T) (i₂ : ∀ T : P × Q, G.obj T.2 →ₐ[K] E.obj T), (∀ (T T' : P × Q) (a : T ⟶ T') (b : F.obj T.1), i₁ T' (mp F a.1 b) = mp E a (i₁ T b)) → (∀ (T T' : P × Q) (a : T ⟶ T') (b : G.obj T.2), i₂ T' (mp G a.2 b) = mp E a (i₂ T b)) → (∀ T, Function.Bijective (Algebra.TensorProduct.productMap (i₁ T) (i₂ T))) → ∀ (n : ℕ) (x : Fin n → Z1 F) (y : Fin n → Z1 G) (f : C1 E), (∀ (T T' T'' : P × Q) (a : T ⟶ T') (b : T' ⟶ T''), d1 E f T T' T'' a b = ∑ i, mp E b (i₁ T' ((x i).1 _ _ a.1)) * i₂ T'' ((y i).1 _ _ b.2)) → ∑ i, GlobalTheory.CatCoh.H1.mk F (x i) ⊗ₜ[K] GlobalTheory.CatCoh.H1.mk G (y i) = 0 := by
  first | exact @GlobalTheory.CatCoh.KunnethOne.sum_tmul_eq_zero_of_cup | exact GlobalTheory.CatCoh.KunnethOne.sum_tmul_eq_zero_of_cup | (intros; apply GlobalTheory.CatCoh.KunnethOne.sum_tmul_eq_zero_of_cup <;> assumption)
