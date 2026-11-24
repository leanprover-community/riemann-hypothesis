module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Extension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

instance valuation_hasExtension : (valuation K).HasExtension (valuation L) where
  val_isEquiv_comap a b := by
    rw [Valuation.comap_apply, Valuation.comap_apply, ← Valuation.vle_iff_le,
      ← Valuation.vle_iff_le, ValuativeExtension.vle_iff_vle]

@[simp]
theorem coe_algebraMap_integer (x : 𝒪[K]) :
    ((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L) = algebraMap K L (x : K) :=
  rfl

theorem algebraMap_integer_injective : Function.Injective (algebraMap 𝒪[K] 𝒪[L]) :=
  Valuation.HasExtension.algebraMap_injective

theorem algebraMap_mem_integer_iff (x : K) : algebraMap K L x ∈ 𝒪[L] ↔ x ∈ 𝒪[K] := by
  simp only [Valuation.mem_integer_iff]
  exact Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) x

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

theorem continuous_algebraMap : Continuous (algebraMap K L) := by
  refine continuous_of_continuousAt_zero (algebraMap K L) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)]
  intro γ _
  obtain ⟨δ, hδ0, hδ1⟩ := IsNontrivial.exists_lt_one (R := K)
  obtain ⟨a, rfl⟩ := valuation_surjective δ
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hδ0
  have hb : valuation L (algebraMap K L a) < 1 := by
    exact (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr hδ1
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hb γ
  refine ⟨Units.mk0 (valuation K (a ^ n)) (by simp [ha0]), trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢
  calc valuation L (algebraMap K L x) < valuation L (algebraMap K L (a ^ n)) := by
        rw [← (valuation L).vlt_iff_lt, ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt]
        exact hx
    _ = valuation L (algebraMap K L a) ^ n := by simp
    _ < γ := hn

instance continuousSMul : ContinuousSMul K L :=
  continuousSMul_of_algebraMap K L (continuous_algebraMap K L)

end Topological

end GroundTheory.LocalField
