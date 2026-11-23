module

import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.HasDerivAtDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GeneratorWeights

variable {n : ℕ}

theorem sg_cases (ε : Fin n → Bool) (p : Fin n × Fin n) : sg ε p = 1 ∨ sg ε p = -1 := by
  unfold sg
  split_ifs <;> simp

theorem wt_ge (p : Fin n × Fin n) : 1 / 2 ≤ wt p := by
  unfold wt
  split_ifs <;> norm_num

theorem wt_le (p : Fin n × Fin n) : wt p ≤ 1 := by
  unfold wt
  split_ifs <;> norm_num

theorem gen_mem (ε : Fin n → Bool) (p : Fin n × Fin n) : inG ε (gen ε p) := by
  apply Formalism.L2.SG.Pf.admitted.AdmissibleVectors.inG_gen <;> assumption

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

theorem sum_eq (hC : Calc ε σ D) {c : ℝ} (hc : ∀ v ∈ D, Cas ε σ v = (c : ℂ) • v) {v : H} (hv : v ∈ D) :
    ∑ p : Fin n × Fin n, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 = c * ‖v‖ ^ 2 := by
  have hgen : ∀ p, inG ε (gen ε p) := gen_mem ε
  have key : ⟪Cas ε σ v, v⟫_ℂ =
      ∑ p, ((wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    unfold Cas
    rw [inner_neg_left, sum_inner, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_smul_left, hC.skew _ (hgen p) _ (hC.mem _ (hgen p) v hv) v hv,
      inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have h2 : ((c * ‖v‖ ^ 2 : ℝ) : ℂ) =
      ((∑ p, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← key, hc v hv, inner_smul_left, inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  exact (Complex.ofReal_inj.1 h2).symm

end GeneratorWeights

open GeneratorWeights in
theorem c4 : CasimirScalarBounded := by
  intro n ε H _ _ _ σ D hC c hc W C hW
  set K : ℝ := 2 * ((Fintype.card (Fin n × Fin n) : ℝ) * C ^ 2 + |c|) with hK
  refine ⟨max C (Real.sqrt K), fun p v hvD hvW => ?_⟩
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  by_cases hp : ε p.1 = ε p.2
  · exact (hW p hp v hvW).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)
  · have hsum := sum_eq hC hc hvD
    have hsgp : sg ε p = -1 := by simp [sg, hp]
    have hterm : ∀ q, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
      intro q
      have h3 := wt_le q
      have h4 := wt_ge q
      rcases sg_cases ε q with h | h
      · have hq : ε q.1 = ε q.2 := by
          by_contra hne
          simp [sg, hne] at h
          norm_num at h
        have h1 := hW q hq v hvW
        have h2 : ‖dS σ (gen ε q) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        rw [h, mul_one]
        have h5 : wt q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ 1 * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        nlinarith [h2, h5]
      · rw [h]
        have h5 : 0 ≤ wt q * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        nlinarith [sq_nonneg (C * ‖v‖), h5]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun q => wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2) (Finset.mem_univ p)
    have hrest : ∑ q ∈ Finset.univ.erase p, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤
        (Fintype.card (Fin n × Fin n) : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
      calc _ ≤ ∑ q ∈ Finset.univ.erase p, C ^ 2 * ‖v‖ ^ 2 :=
            Finset.sum_le_sum fun q _ => hterm q
        _ = ((Finset.univ.erase p).card : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Finset.card_erase_le.trans (le_of_eq Finset.card_univ)))
            (by positivity)
    have hwp := wt_ge p
    rw [hsgp] at hsplit
    have e2 : (1 / 2) * ‖dS σ (gen ε p) v‖ ^ 2 ≤ wt p * ‖dS σ (gen ε p) v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hwp (sq_nonneg _)
    have e3 : -c * ‖v‖ ^ 2 ≤ |c| * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_abs c) (sq_nonneg _)
    have hsq : ‖dS σ (gen ε p) v‖ ^ 2 ≤ K * ‖v‖ ^ 2 := by
      rw [hK]
      nlinarith [hsplit, hsum, hrest, e2, e3]
    have hK0 : 0 ≤ K := by positivity
    have hle : ‖dS σ (gen ε p) v‖ ≤ Real.sqrt K * ‖v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (dS σ (gen ε p) v)), ← Real.sqrt_sq hv0,
        ← Real.sqrt_mul hK0]
      exact Real.sqrt_le_sqrt hsq
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hv0)

end Formalism.L2.SG.Pf.admitted
