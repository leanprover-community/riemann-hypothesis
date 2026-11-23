module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueField
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
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

theorem _root_.GlobalTheory.T.finrank_homology_resolutions_residueField : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  first | exact @GlobalTheory.AbCoh.finrank_homology_base_change_resolutions | exact GlobalTheory.AbCoh.finrank_homology_base_change_resolutions | (intros; apply GlobalTheory.AbCoh.finrank_homology_base_change_resolutions <;> assumption)
