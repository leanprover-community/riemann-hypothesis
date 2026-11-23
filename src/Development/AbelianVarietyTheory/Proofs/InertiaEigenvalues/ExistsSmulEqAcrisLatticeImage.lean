module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DenomCris

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem cc_one : WittVector.constantCoeff (1 : Ainf l) ≠ 0 := by
  obtain ⟨e, -, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI : Nontrivial (Per.Fl l) := ⟨e, 1, hne⟩
  rw [map_one]
  exact one_ne_zero

theorem cc_mul {x y : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (hy : WittVector.constantCoeff y ≠ 0) :
    WittVector.constantCoeff (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

theorem cc_pow {x : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (n : ℕ) :
    WittVector.constantCoeff (x ^ n) ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact cc_one
  | succ n ih => rw [pow_succ]; exact cc_mul ih hx

theorem exists_mul_eq_toOB (r : OB l O) : ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ a : OCr l O,
    ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) * r = toOB l O a := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul o y =>
    obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
    obtain ⟨n, a, ha⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne y
    refine ⟨(Per.tm e - 1) ^ n, cc_pow (GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne) n, o ⊗ₜ a, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change o ⊗ₜ[ℤ_[l]] (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Ainf l) (Per.Acris l) ((Per.tm e - 1) ^ n)) * y) =
      o ⊗ₜ[ℤ_[l]] algebraMap (Per.Acris l) (Per.Bcris l) a
    rw [map_pow, map_pow, mul_comm, ha]
  | add r₁ r₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) * a₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) * a₂, ?_⟩
    have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
        (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) * ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hm, map_add (f := _), map_mul (toOB l O), map_mul (toOB l O), hc, hc, ← e₁, ← e₂]
    ring

theorem exists_smul_eq_TWincl : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T), ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ β : TW (OCr l O) T, ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) • b = TWincl (toOB l O) T β := by
  intro l _ O K _ _ _ _ _ _ G _ _ T b
  have hsm : ∀ (r : OCr l O) (z : TW (OCr l O) T),
      TWincl (toOB l O) T (r • z) = toOB l O r • TWincl (toOB l O) T z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x t => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add (f := _), h₁, h₂, map_add (f := _), smul_add]
  have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
      (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul r t =>
    obtain ⟨s, hs, a, e⟩ := exists_mul_eq_toOB r
    exact ⟨s, hs, a ⊗ₜ t, by rw [TensorProduct.smul_tmul', smul_eq_mul, e]; rfl⟩
  | add b₁ b₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, β₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, β₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) • β₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) • β₂, ?_⟩
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) *
          ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [map_add (f := _), hsm, hsm, hc, hc, ← e₁, ← e₂, smul_smul, smul_smul, hm, smul_add, mul_comm (_ ⊗ₜ[ℤ_[l]] _)]

end GlobalTheory.DenomCris
