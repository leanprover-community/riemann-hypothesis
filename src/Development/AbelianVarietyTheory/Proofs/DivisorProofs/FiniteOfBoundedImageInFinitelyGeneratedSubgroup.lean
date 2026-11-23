module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Data.Pi.Interval
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem finite_of_bounded_image_closure_finset :
    ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (Φ : V →+ E),
      (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) →
      ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) →
        ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  intro V E _ _ _ _ _ Φ hΦ S Y hY R hR
  set M : Submodule ℤ V := Submodule.span ℤ (S : Set V) with hMdef
  have hMY : Y ⊆ (M : Set V) := by
    intro y hy
    have := hY hy
    rw [← Submodule.span_int_eq_addSubgroupClosure] at this
    exact this
  haveI : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet
  haveI : Module.IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℚ V
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ M
  set n := Module.finrank ℤ M
  let e : Fin n → V := fun j => (b j : V)
  have heZ : LinearIndependent ℤ e := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 heZ
  have heR := hΦ n e heQ
  let T : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ (fun j => Φ (e j))
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 heR)
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hT

  let f : V → (Fin n → ℤ) := fun y => if h : y ∈ M then fun j => b.repr ⟨y, h⟩ j else 0
  have hfy : ∀ y (h : y ∈ M), f y = fun j => b.repr ⟨y, h⟩ j := fun y h => by simp [f, h]
  have hinj : Set.InjOn f Y := by
    intro y hy z hz hyz
    have h1 := hMY hy
    have h2 := hMY hz
    rw [hfy y h1, hfy z h2] at hyz
    have : b.repr ⟨y, h1⟩ = b.repr ⟨z, h2⟩ := by
      ext j; exact congrFun hyz j
    have := b.repr.injective this
    simpa using congrArg Subtype.val this
  have hΦy : ∀ y (h : y ∈ M), Φ y = T (fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)) := by
    intro y h
    have hs' : y = ∑ j, b.repr ⟨y, h⟩ j • e j := by
      have := congrArg (Subtype.val : M → V) (b.sum_repr ⟨y, h⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [hs']

    simp [T, Fintype.linearCombination_apply, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  set N : ℤ := ⌈(K : ℝ) * R⌉
  have hsub : f '' Y ⊆ Set.Icc (fun _ => -N) (fun _ => N) := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hMY hy
    rw [hfy y h]
    set c : Fin n → ℝ := fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)
    have hc : ‖c‖ ≤ (K : ℝ) * R := by
      have h1 := ZeroHomClass.bound_of_antilipschitz T hK c
      rw [← hΦy y h] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hR y hy) K.2)
    have hcj : ∀ j, |c j| ≤ (K : ℝ) * R := fun j => by
      have h0 : ‖c j‖ ≤ ‖c‖ := norm_le_pi_norm c j
      rw [Real.norm_eq_abs] at h0
      exact h0.trans hc
    constructor <;> intro j
    · have h3 : -((K : ℝ) * R) ≤ c j := (abs_le.1 (hcj j)).1
      have h4 : (-(N : ℝ)) ≤ c j := le_trans (neg_le_neg (Int.le_ceil _)) h3
      have h5 : ((-N : ℤ) : ℝ) ≤ ((b.repr ⟨y, h⟩ j : ℤ) : ℝ) := by push_cast; exact h4
      exact Int.cast_le.1 h5
    · have h4 : c j ≤ (N : ℝ) := ((abs_le.1 (hcj j)).2).trans (Int.le_ceil _)
      exact Int.cast_le.1 h4
  exact Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset hsub) hinj

end GlobalTheory
