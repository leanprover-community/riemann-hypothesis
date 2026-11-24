module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplier
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.TorsMemVal

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

theorem mem_of_val (V : ValuationSubring ℂ) {n u Ω x : ℂ} (k : ℕ) (hn : V.valuation n = 1)
    (hu : V.valuation u = V.valuation Ω) (h : n ^ k * x / Ω ^ k ∈ V) : x / u ^ k ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu] at h
  rwa [map_div₀, map_pow]

theorem main : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → ∀ z w, z ∉ L.lattice → w ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (N : ℂ) * w ∈ L.lattice → L.derivWeierstrassP z / u ^ 3 ∈ V ∧ (L.weierstrassP z - L.weierstrassP w) / u ^ 2 ∈ V := by
  intro L β u V N hβ hβi hu hN z w hz hw hNz hNw
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (n := 12) (by norm_num)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN
    · exact h
  have huΩ : V.valuation u = V.valuation Ω := by
    rw [← hΩ, map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have h := GlobalTheory.WpFam.LatTorsVal.main L β Ω N hβ hβi (hΩ.trans (latticeCurve_Δ L)) hN0
  exact ⟨mem_of_val V 3 hN huΩ (mem_of_isIntegral V (h.1 z hNz).2),
    mem_of_val V 2 hN huΩ (mem_of_isIntegral V (h.2 z w hz hw hNz hNw))⟩

end GlobalTheory.CMModel.TorsMemVal
