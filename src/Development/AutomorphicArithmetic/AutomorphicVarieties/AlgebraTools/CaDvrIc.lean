module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.integralClosure_complete_dvr :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      (F K : Type) [Field F] [Field K] [Algebra A F] [IsFractionRing A F] [Algebra F K] [Algebra A K]
      [IsScalarTower A F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
      (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra B K] [IsScalarTower A B K] [IsIntegralClosure B A K],
      Module.Finite A B ∧ Module.Free A B ∧ IsFractionRing B K ∧
      ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B ∧ IsLocalHom (algebraMap A B) ∧
        (Finite (ResidueField A) → Finite (ResidueField B)) := by
  intro A _ _ _ _ F K _ _ _ _ _ _ _ _ _ B _ _ _ _ _ _
  have hinjK : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective A F)
  have hinj : Function.Injective (algebraMap A B) := by
    rw [IsScalarTower.algebraMap_eq A B K, RingHom.coe_comp] at hinjK
    exact hinjK.of_comp
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI hfin : Module.Finite A B := IsIntegralClosure.finite A F K B
  haveI hfree : Module.Free A B := Module.free_of_finite_type_torsion_free'
  have hfr : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension A F K B
  haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure A F K
  haveI hdvr : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsIntegralClosure.equiv A (integralClosure A K) K B)
  haveI hloc : IsLocalHom (algebraMap A B) := inferInstance
  refine ⟨hfin, hfree, hfr, hdvr, GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite A B,
    hloc, fun h => ?_⟩
  exact IsLocalRing.ResidueField.finite_of_finite h
