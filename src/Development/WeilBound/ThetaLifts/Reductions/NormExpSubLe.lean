module

import CompanionTheory.ThickeningEstimates.LieGroupReduction.NormExpSubLe
public import Development.WeilBound.ThetaLifts.Reductions.IsoOfIntegral
public import Development.WeilBound.ThetaLifts.Reductions.HasDerivAtSchwartzToL2
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.CartanFactorisation.EqOfInner

@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKR.LL

variable {l : Type} [Fintype l]

def mq (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I

theorem mq_apply (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) : mq S f x = ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I * f x := by
  have h2 : Function.HasTemperateGrowth fun x : Eu l => -π * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : Eu l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I :=
    (ofRealCLM.hasTemperateGrowth.comp h2).mul (Function.HasTemperateGrowth.const _)
  rw [mq, smulLeftCLM_apply_apply h3, smul_eq_mul]

theorem norm_exp_sub_le (a b : ℝ) : ‖exp ((a : ℂ) * I) - exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have : exp ((a : ℂ) * I) - exp ((b : ℂ) * I) = exp ((b : ℂ) * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem exists_lip {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : ℝ → F} {S' : F} {t₀ : ℝ}
    (h : HasDerivAt S S' t₀) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in 𝓝 t₀, ‖S t - S t₀‖ ≤ K * |t - t₀| := by
  obtain ⟨K, hK, h⟩ := h.isBigO_sub.exists_nonneg
  exact ⟨K, hK, h.bound⟩

theorem ld_ph {S : ℝ → Eu l →L[ℝ] Eu l} {S' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt S S' t₀) :
    LD (fun t => ph (S t)) (fun f => mq S' (ph (S t₀) f)) t₀ := fun f => by
  obtain ⟨K, hK, hb⟩ := exists_lip h
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C, hC, hf⟩ := exists_decay f (N + 2)
  refine hasDerivAt_schwartz_to_L2 (C := π * K * C) (fun x => ?_) ?_
  · simp only [ph_apply, mq_apply]
    have h1 : HasDerivAt (fun t => S t x) (S' x) t₀ := by simpa using h.clm_apply (hasDerivAt_const t₀ x)
    have h2 : HasDerivAt (fun t => ⟪x, S t x⟫) ⟪x, S' x⟫ t₀ := (innerSL ℝ x).hasFDerivAt.comp_hasDerivAt t₀ h1
    exact (((h2.const_mul (-π)).ofReal_comp.mul_const I).cexp.mul_const (f x)).congr_deriv (by ring)
  · filter_upwards [hb] with t ht x
    rw [← hN]
    simp only [ph_apply]
    rw [← sub_mul, norm_mul]
    have h1 : |-π * ⟪x, S t x⟫ - -π * ⟪x, S t₀ x⟫| ≤ π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) := by
      rw [← mul_sub, ← inner_sub_right, abs_mul, abs_neg, abs_of_pos Real.pi_pos, ← ContinuousLinearMap.sub_apply]
      refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) Real.pi_pos.le
      have h2 := (S t - S t₀).le_opNorm x
      calc ‖x‖ * ‖(S t - S t₀) x‖ ≤ ‖x‖ * ((K * |t - t₀|) * ‖x‖) := by
            refine mul_le_mul_of_nonneg_left (h2.trans ?_) (norm_nonneg _)
            gcongr
        _ = ‖x‖ ^ 2 * (K * |t - t₀|) := by ring
        _ ≤ _ := by gcongr; simp
    calc _ ≤ (1 + ‖x‖) ^ N * (π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) * ‖f x‖) := by
          gcongr
          exact (norm_exp_sub_le _ _).trans h1
      _ = π * K * ((1 + ‖x‖) ^ (N + 2) * ‖f x‖) * |t - t₀| := by ring
      _ ≤ _ := by gcongr; exact hf x

def vf (H : Eu l →L[ℝ] Eu l) (f : Sch l) : Sch l :=
  bilinLeftCLM (ContinuousLinearMap.id ℝ (Eu l →L[ℝ] ℂ)) H.hasTemperateGrowth (fderivCLM ℝ (Eu l) ℂ f)

theorem vf_apply (H : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) : vf H f x = fderiv ℝ f x (H x) := rfl

theorem ld_dil_one {H : ℝ → Eu l →L[ℝ] Eu l} {H' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt H H' t₀) (h0 : H t₀ = 1)
    (f : Sch l) {F : ℝ → Sch l} (hF : ∀ᶠ t in 𝓝 t₀, ∀ x, F t x = f (H t x)) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l (vf H' f)) t₀ := by
  apply CompanionTheory.ThKR.LL.ld_dil_one <;> assumption

theorem ld_dil {B : ℝ → Eu l →L[ℝ] Eu l} {B' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt B B' t₀) (h0 : IsUnit (B t₀)) :
    LD (fun t => dil (B t)) (fun f => vf (Ring.inverse (B t₀) * B') (dil (B t₀) f)) t₀ := fun f => by
  refine ld_dil_one (h.const_mul (Ring.inverse (B t₀))) (Ring.inverse_mul_cancel _ h0) _ ?_
  set_option synthInstance.maxHeartbeats 200000 in
    filter_upwards [h.continuousAt.eventually (Units.isOpen.mem_nhds h0)] with t ht x
  rw [dil_apply ht, dil_apply h0, ← ContinuousLinearMap.mul_apply, ← mul_assoc, Ring.mul_inverse_cancel _ h0, one_mul]

theorem ld_big {Ai B C : ℝ → Eu l →L[ℝ] Eu l} {Ai' B' C' : Eu l →L[ℝ] Eu l} {c : ℝ → ℝ} {c' t₀ : ℝ}
    (hA : HasDerivAt Ai Ai' t₀) (hB : HasDerivAt B B' t₀) (hC : HasDerivAt C C' t₀) (hc : HasDerivAt c c' t₀)
    (h : ∀ᶠ t in 𝓝 t₀, IsUnit (Ai t) ∧ c t ^ 2 = |(Ai t).det|) :
    ∃ Q, LD (fun t => big (Ai t) (B t) (C t) (c t)) Q t₀ ∧ (Ai t₀ = 1 → B t₀ = 0 → C t₀ = 0 → c t₀ = 1 → ∀ f,
      Q f = mq C' f + vf Ai' f + fou l (mq (-B') (fouInv l f)) + (c' : ℂ) • f) := by
  have h1 := (ld_ph (hA.mul hB).neg).mul (LD.const (fouInv l) t₀) (.of_forall fun t => iso_ph _)
  have h2 := (LD.const (fou l) t₀).mul h1 (.of_forall fun t => iso_fou)
  have h3 := ((ld_dil hA h.self_of_nhds.1).smul hc.ofReal_comp).mul h2 (h.mono fun t ht => iso_dil ht.1 ht.2)
  have h4 := (ld_ph (hC.mul hA)).mul h3 (.of_forall fun t => iso_ph _)
  refine ⟨_, h4, fun e1 e2 e3 e4 f => ?_⟩
  have e5 : fou l (fouInv l f) = f := by
    rw [← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]
  simp [e1, e2, e3, e4, ph_zero, dil_one, e5]
  abel

end PositivityTheory.ThKR.LL
