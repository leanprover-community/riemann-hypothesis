module

public import GroundTheory.LocalFields.Different
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ n hn z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := by
    have : ϖ ≠ 0 := hϖ.ne_zero
    exact_mod_cast this
  set I : Ideal 𝒪[M] := Ideal.span {algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n)} with hI
  have hImap : I = (𝓂[F] ^ n).map (algebraMap 𝒪[F] 𝒪[M]) := by
    rw [hI, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]
  have hIeq : I = 𝓂[M] ^ ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n) := by
    rw [hImap, Ideal.map_pow, map_maximalIdeal, pow_mul]
  have hle : differentIdeal 𝒪[F] 𝒪[M] ≤ I := by
    rw [differentIdeal_eq_maximalIdeal_pow, hIeq]
    exact Ideal.pow_le_pow_right hn
  have hIne : I ≠ ⊥ := by
    rw [hI, ne_eq, Ideal.span_singleton_eq_bot]
    intro h
    have : ((algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n) : 𝒪[M]) : M) = 0 := by rw [h]; rfl
    rw [coe_algebraMap_integer] at this
    rw [SubmonoidClass.coe_pow, map_pow] at this
    exact pow_ne_zero n ((_root_.map_ne_zero _).mpr hϖ0) this
  have key := (differentialIdeal_le_iff (K := F) (L := M) hIne).mp hle
  set x : M := algebraMap F M ((ϖ : F) ^ n) with hx
  have hx0 : x ≠ 0 := by
    rw [hx]; exact (_root_.map_ne_zero _).mpr (pow_ne_zero _ hϖ0)
  have hIfrac : ((I : FractionalIdeal (nonZeroDivisors 𝒪[M]) M)) = FractionalIdeal.spanSingleton (nonZeroDivisors 𝒪[M]) x := by
    rw [hI, FractionalIdeal.coeIdeal_span_singleton]
    congr 1
  have hmem : x⁻¹ * (z : M) ∈ (((I⁻¹ : FractionalIdeal (nonZeroDivisors 𝒪[M]) M) : Submodule 𝒪[M] M)) := by
    rw [hIfrac, FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_spanSingleton]
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  have htr : Algebra.trace F M (x⁻¹ * (z : M)) ∈ (1 : Submodule 𝒪[F] F) :=
    key ⟨_, hmem, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp htr
  refine ⟨ϖ ^ n * a, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ) n), ?_⟩
  have hz : (z : M) = x * (x⁻¹ * (z : M)) := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [hz, hx, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [← ha]
  rfl

end GlobalTheory.PMon.Ram
