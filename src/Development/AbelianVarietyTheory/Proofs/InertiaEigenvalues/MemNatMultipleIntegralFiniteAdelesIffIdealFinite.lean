module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RSJ

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem valued_natCast_apply (E : Type) [Field E] [NumberField E] (N : ℕ)
    (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v) = v.valuation E (N : E) := by
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N]
  exact valuedAdicCompletion_eq_valuation' v (N : E)

theorem natLat_iff_mem_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) →
      ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  intro E _ _ N hN J hJ x
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hc0 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (N : E) ≠ 0 :=
    fun v => (Valuation.ne_zero_iff _).2 hN0
  have hc : ∀ v : HeightOneSpectrum (𝓞 E),
      exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) = v.valuation E (N : E) := by
    intro v
    rw [hJ, GroundTheory.Global.count_spanSingleton v hN0, neg_neg, exp_log (hc0 v)]
  rw [GroundTheory.Global.mem_idealFiniteAdeles]
  simp only [hc]
  have hunit : (N : FiniteAdeleRing (𝓞 E) E) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N, ← map_mul, mul_inv_cancel₀ hN0,
      map_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ v
    change Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v * z v) ≤ _
    rw [map_mul, valued_natCast_apply]
    have : Valued.v (z v) ≤ 1 := by
      have h := hz v
      rwa [mem_adicCompletionIntegers] at h
    calc v.valuation E (N : E) * Valued.v (z v) ≤ v.valuation E (N : E) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hx
    refine ⟨algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ * x, fun v => ?_, ?_⟩
    · rw [mem_adicCompletionIntegers]
      change Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) v * x v) ≤ 1
      rw [map_mul]
      change Valued.v (((N : E)⁻¹ : E) : v.adicCompletion E) * Valued.v (x v) ≤ 1
      rw [valuedAdicCompletion_eq_valuation' v, map_inv₀]
      exact (GroundTheory.Global.inv_mul_le_one_iff_withZero (hc0 v)).2 (hx v)
    · rw [← mul_assoc, hunit, one_mul]

end GlobalTheory.RSJ
