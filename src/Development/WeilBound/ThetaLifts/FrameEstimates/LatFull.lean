module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.IntMvPolynomialCoeffAbsSumMulLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latFull_of : LatTor → Minor → LatFull := by
  intro hT hM F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' m
  obtain ⟨N, hN⟩ := hT F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  refine ⟨N + m * (n + 1), fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hN C hC
  obtain ⟨c, hc, h⟩ := hM F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  refine ⟨((c ^ (m * (n + 1)))⁻¹).toNNReal * K, fun s hs t ht => ?_⟩
  let i : fullRank E n d → (Set.univ : Set (Matrix (Fin n) (Fin d) E)) := fun x => ⟨x.1, trivial⟩
  have hi : Function.Injective i := fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
  let g : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (maj τ C N (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ))
  calc _ ≤ ∑' x, ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := h s hs t ht x.1 x.2
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        unfold maj
        split_ifs with hx
        · have h2 := pow_le_pow_left₀ (by positivity) (h1 hx) (m * (n + 1))
          rw [mul_pow, ← Real.exp_nat_mul,
            show ((m * (n + 1) : ℕ) : ℝ) * (viol s t / (n + 1)) = m * viol s t by push_cast; field_simp] at h2
          rw [pow_add, mul_inv, mul_comm, Real.exp_neg, ← mul_inv (c ^ _)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2) (by positivity)
        · simp
    _ ≤ ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) *
          (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans (hK s hs t ht)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.coe_mul]
        change _ = ENNReal.ofReal _ * _ * _
        ring

end PositivityTheory.ThKEst

end
