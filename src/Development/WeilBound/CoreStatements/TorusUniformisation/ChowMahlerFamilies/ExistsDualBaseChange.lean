module

public import Mathlib.LinearAlgebra.Dual.BaseChange
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.DualBaseChange

theorem dual_isBaseChange {R : Type} [CommRing R] {A : Type} [Field A] [Algebra R A]
    [IsFractionRing R A] {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] {W : Type} [AddCommGroup W] [Module R W] [Module A W]
    [IsScalarTower R A W] {j : V →ₗ[R] W} (hb : IsBaseChange A j) :
    IsBaseChange A hb.toDual := by
  have : Module.FinitePresentation R V := Module.finitePresentation_of_projective R V
  rw [← isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) A]
  refine ⟨(isLocalizedModule_id (nonZeroDivisors R) (Module.Dual A W) A).map_units, ?_, ?_⟩
  · intro φ
    obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
      (nonZeroDivisors R) (Algebra.linearMap R A) ((φ.restrictScalars R) ∘ₗ j)
    refine ⟨(h, s), ?_⟩
    apply hb.algHom_ext
    intro v
    have := LinearMap.congr_fun hs v
    rw [hb.toDual_comp_apply]
    exact this.symm
  · intro u₁ u₂ h
    refine ⟨1, ?_⟩
    congr 1
    ext v
    apply IsFractionRing.injective R A
    rw [← hb.toDual_comp_apply, ← hb.toDual_comp_apply, h]

end PositivityTheory.Xgn.DualBaseChange

theorem PositivityTheory.Xgn.exists_dual_base_change : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) := by
  intro Ω _ O _ _ R _ L _ _ _ _ Li _ _ toLi hb
  exact ⟨hb.toDual, PositivityTheory.Xgn.DualBaseChange.dual_isBaseChange hb,
    fun u v => hb.toDual_comp_apply u v⟩
