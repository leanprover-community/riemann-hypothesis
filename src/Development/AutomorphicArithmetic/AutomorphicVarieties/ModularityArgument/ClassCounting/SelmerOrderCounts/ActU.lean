module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
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
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.h90 :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (l : ℕ), IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → ∀ x y : Fˣ, actU γ x = x * y ^ l → Algebra.norm L (y : F) = 1 → ∃ (x₀ : Lˣ) (z : Fˣ), x = Units.map (algebraMap L F : L →* F) x₀ * z ^ l := by
  intro L F _ _ _ _ _ γ l hG hγ x y hx hy
  haveI : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite ℚ L F
  haveI : IsCyclic (F ≃ₐ[L] F) := ⟨⟨γ, hγ⟩⟩
  obtain ⟨w, hw⟩ := groupCohomology.exists_div_of_norm_eq_one hγ hy
  have hx' : γ (x : F) = (x : F) * (y : F) ^ l := by
    have := congrArg (fun u : Fˣ => (u : F)) hx
    simpa [actU] using this
  have hw0 : (w : F) ≠ 0 := w.ne_zero
  have hgw0 : γ (w : F) ≠ 0 := by simp
  have hfix : γ ((x : F) * (w : F) ^ l) = (x : F) * (w : F) ^ l := by
    rw [map_mul, map_pow, hx', ← hw, mul_assoc, ← mul_pow, div_mul_cancel₀ _ hgw0]
  have hall : ∀ σ : F ≃ₐ[L] F, σ ((x : F) * (w : F) ^ l) = (x : F) * (w : F) ^ l := by
    intro σ
    have hle : Subgroup.zpowers γ ≤ MulAction.stabilizer (F ≃ₐ[L] F) ((x : F) * (w : F) ^ l) := by
      rw [Subgroup.zpowers_le]
      exact hfix
    exact hle (hγ σ)
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hall
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (mul_ne_zero x.ne_zero (pow_ne_zero l hw0)) ha.symm
  refine ⟨Units.mk0 a ha0, w⁻¹, ?_⟩
  ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0, ha,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hw0, one_pow, mul_one]
