module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOfQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FibreNe
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IsOrdProjZeroOfIsNilpotent

@[expose] public section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig :
    ∀ {Λ T K M : Type*} [CommRing Λ] [CommRing T] [Algebra Λ T] [Field K] [Algebra Λ K] [AddCommGroup M] [Module Λ M] [Module T M] [IsScalarTower Λ T M] [Module.Finite Λ M] [FaithfulSMul T M] (x : T →ₐ[Λ] K), ∃ y : K ⊗[Λ] M, y ≠ 0 ∧ ∀ t : T, (Algebra.lsmul Λ Λ M t).baseChange K y = x t • y := by
  intro Λ T K M _ _ _ _ _ _ _ _ _ _ _ x
  letI : Algebra T K := x.toRingHom.toAlgebra
  haveI : IsScalarTower Λ T K := IsScalarTower.of_algebraMap_eq fun r => (x.commutes r).symm
  haveI : Module.Finite T M := Module.Finite.of_restrictScalars_finite Λ T M
  have hne : Nontrivial (K ⊗[T] M) := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe
  let φ : K ⊗[Λ] M →ₗ[K] K ⊗[T] M := TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.restrictScalarsₗ Λ T M (K ⊗[T] M) K).comp
      (TensorProduct.AlgebraTensorModule.mk T K K M))
  have hφt : ∀ (k : K) (m : M), φ (k ⊗ₜ[Λ] m) = k ⊗ₜ[T] m := by
    intro k m
    simp [φ]
  let A : T → Module.End K (K ⊗[Λ] M) := fun t => (Algebra.lsmul Λ Λ M t).baseChange K
  have hA : ∀ (t : T) (k : K) (m : M), A t (k ⊗ₜ[Λ] m) = k ⊗ₜ[Λ] (t • m) := by
    intro t k m
    simp [A]
  have hc : ∀ s t, Commute (A s) (A t) := by
    intro s t
    show A s * A t = A t * A s
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [Module.End.mul_apply, Module.End.mul_apply, hA, hA, hA, hA, smul_comm]
    | add a b ha hb =>
      rw [Module.End.mul_apply, Module.End.mul_apply] at ha hb ⊢
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hφA : ∀ t y, φ (A t y) = x t • φ y := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [hA, hφt, hφt, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), smul_add]
  have hφ0 : φ ≠ 0 := by
    intro h0
    have hall : ∀ p : K ⊗[T] M, p = 0 := by
      intro p
      induction p using TensorProduct.induction_on with
      | zero => rfl
      | tmul k m => rw [← hφt, h0, LinearMap.zero_apply]
      | add a b ha hb => rw [ha, hb, add_zero]
    obtain ⟨p, hp⟩ := exists_ne (0 : K ⊗[T] M)
    exact hp (hall p)
  exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot A hc (fun t => x t) φ hφ0 hφA
