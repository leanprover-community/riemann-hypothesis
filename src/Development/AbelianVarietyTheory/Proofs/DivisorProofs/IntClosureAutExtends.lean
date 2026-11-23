module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
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
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem intClosure_aut_extends : ∀ (o₁ Ω₁ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (z₁ : M₁.Z), letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ σ : (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[M₁.Z.presheaf.stalk z₁] (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂), ∃ σ' : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, σ' (b : Ω₂) = ((σ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : Ω₂) := by
  intro o₁ Ω₁ _ _ _ Ω₂ _ _ _ M₁ z₁ σ
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₁ := (M₁.stalkHom z₁).toAlgebra
  haveI : IsDomain (M₁.Z.presheaf.stalk z₁) := (M₁.stalkHom_injective z₁).isDomain _
  haveI : FaithfulSMul (M₁.Z.presheaf.stalk z₁) Ω₁ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M₁.stalkHom_injective z₁)
  haveI : IsFractionRing (M₁.Z.presheaf.stalk z₁) Ω₁ := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M₁.O z₁) x
    refine ⟨(M₁.stalkEquiv z₁).symm a, (M₁.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : M₁.O z₁, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₁ ((M₁.stalkEquiv z₁).symm c) = c := fun c => by
      change M₁.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic Ω₁ Ω₂ := inferInstance
  refine ⟨(galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ, fun b => ?_⟩
  have := algebraMap_galRestrict_apply (M₁.Z.presheaf.stalk z₁)
    ((galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ) b
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UPoinc
