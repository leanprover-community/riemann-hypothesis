module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isTop_exists_and_eq (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) :
    IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧
      ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  intro h
  refine ⟨h.exists_isTop, fun τ hτ y hy => ?_⟩
  obtain ⟨b, hb⟩ := h.exists_basis
  set u : Fin d → K := fun j => (algebraMap F K (x j.succ / x 0))⁻¹
  have hu : ∀ j, u j ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  have hp : (∏ j, u j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hu j
  have hv : vol0 k K x = (∏ j, u j) • ExteriorAlgebra.ιMulti K d b := by
    rw [← AlternatingMap.map_smul_univ]
    simp only [vol0, hb, u]

  have key : ∀ c : K, c • vol0 k K x = τ (c • vol0 k K x) • vol0 k K x := by
    intro c
    rw [map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have e : ExteriorAlgebra.ιMulti K d m = (b.det m * (∏ j, u j)⁻¹) • vol0 k K x := by
      rw [hv, smul_smul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
      intro φ
      have h2 := congrArg (fun g => g m)
        (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)))
      simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h2
      rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_self]
    rw [e]
    exact key _
  | zero => simp
  | add a c _ _ ha hc => rw [map_add (f := _), add_smul, ← ha, ← hc]
  | smul r a _ ha => rw [map_smul, smul_eq_mul, mul_smul, ← ha]

end GlobalTheory.PD
