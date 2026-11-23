module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CkModel
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.ModelFunctionsMultiply
import Aesop.Frontend.Tactic
import Aesop.Main
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd.CkM

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

theorem blkMinor_diag_mul (ε : Fin n → Bool) (c : Fin n) (d : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    blkMinor ε c (diagonal d * X) =
      (∏ q ∈ univ.filter (fun q : Fin n => ε q = ε c ∧ q ≤ c), d q) * blkMinor ε c X := by
  unfold blkMinor
  have hx : (diagonal d * X).submatrix (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n))
      (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n)) =
      diagonal (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => d q) *
        X.submatrix (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n))
          (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n)) := by
    ext r s
    simp [Matrix.diagonal_mul]
  rw [hx, det_mul, det_diagonal]
  congr 1
  exact (Finset.prod_subtype (univ.filter (fun q : Fin n => ε q = ε c ∧ q ≤ c)) (by simp) d).symm

theorem model_function_diag_mul (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (d : Fin n → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    f0 ε m (diagonal d * X) = (∏ a, d a ^ (m a).toNat) * f0 ε m X := by
  unfold f0
  simp_rw [blkMinor_diag_mul, mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm' (s' := fun q => univ.filter (fun c : Fin n => ε q = ε c ∧ q ≤ c)) (t' := univ)
    (by intro c q; simp)]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have h := hwmf_tele ε m _ q rfl
  have h2 : ((∑ c ∈ univ.filter (fun c : Fin n => ε q = ε c ∧ q ≤ c), (mexp ε m c).toNat : ℕ) : ℤ) = m q := by
    rw [Nat.cast_sum, ← h]
    exact Finset.sum_congr rfl fun c _ => Int.toNat_of_nonneg (mexp_nonneg ε hm c)
  omega

theorem vsp_diag {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    (y : KG ε) (d : Fin n → ℂ) (hy : toMK y = diagonal d) (x : KG ε) :
    f (y * x) = (∏ a, d a ^ (m a).toNat) * f x := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    show f0K ε m (y * x * k) = _ * f0K ε m (x * k)
    unfold f0K
    rw [show toMK (y * x * k) = diagonal d * toMK (x * k) by
      rw [mul_assoc]; show toMK y * toMK (x * k) = _; rw [hy]]
    exact model_function_diag_mul ε hm d _
  | zero => simp
  | add f g _ _ hf hg => simp [Pi.add_apply, hf, hg, mul_add]
  | smul c f _ hf => simp [Pi.smul_apply, hf, smul_eq_mul]; ring

def ev (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m →ₗ[ℂ] ℂ := (LinearMap.proj (1 : KG ε)).comp (mvFnL ε m)

theorem ev_apply {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : ev ε m f = f.fn 1 := rfl

theorem cpart1_Eaa (ε : Fin n → Bool) (a : Fin n) : cpart1 ε (bdPart ε (single a a (1 : ℂ))) = 0 := by
  ext i j
  rw [cpart1_bdPart_apply]
  by_cases h : ε i = ε j
  · rw [if_pos h]
    simp only [single_apply]
    split_ifs <;> aesop
  · simp [h]

theorem cpart2_Eaa (ε : Fin n → Bool) (a : Fin n) :
    cpart2 ε (bdPart ε (single a a (1 : ℂ))) = (-Complex.I) • single a a (1 : ℂ) := by
  ext i j
  rw [cpart2_bdPart_apply]
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = i
    · subst hj; simp [single_apply]; ring
    · simp [single_apply, hj, Ne.symm hj]
  · by_cases hj : j = a
    · subst hj; simp [single_apply, hi, Ne.symm hi]
    · simp [single_apply, hi, hj, Ne.symm hi, Ne.symm hj]

theorem exp_Eaa (a : Fin n) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • ((-Complex.I) • single a a (1 : ℂ))) =
      diagonal (fun c => if c = a then Complex.exp (-(Complex.I * t)) else 1) := by
  have e : (t : ℂ) • ((-Complex.I) • single a a (1 : ℂ)) =
      diagonal (fun c => if c = a then -(Complex.I * t) else 0) := by
    ext i j
    by_cases hi : i = a <;> by_cases hj : j = a
    · subst hi; subst hj; simp [diagonal_apply, single_apply]; ring
    · subst hi; simp [diagonal_apply, single_apply, Ne.symm hj]
    · subst hj; simp [diagonal_apply, single_apply, Ne.symm hi, hi]
    · simp [diagonal_apply, single_apply, hi, hj, Ne.symm hi, Ne.symm hj]
  rw [e, Matrix.exp_diagonal]
  congr 1
  funext c
  by_cases h : c = a <;> simp [h, ← Complex.exp_eq_exp_ℂ]

theorem ev_dTau_Eaa {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) (f : MV ε m) :
    ev ε m (dTau ε m (single a a 1) f) = ((m a : ℤ) : ℂ) * ev ε m f := by
  apply CompanionTheory.RgFd.CkM.ev_dTau_Eaa <;> assumption

theorem model_op {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (k : KG ε) :
    (modelKType ε hm).op k = tauC ε m k := rfl

theorem model_dτ {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    (modelKType ε hm).dτ = dTau ε m := rfl

theorem model_w {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) : (modelKType ε hm).w = wN ε m := rfl

def uEv (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m :=
  (InnerProductSpace.toDual ℂ (MV ε m)).symm (LinearMap.toContinuousLinearMap (ev ε m))

theorem inner_uEv {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : ⟪uEv ε m, f⟫_ℂ = ev ε m f := by
  rw [uEv, InnerProductSpace.toDual_symm_apply]
  rfl

theorem uEv_wt {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (single a a 1) (uEv ε m) = (((m a : ℤ) : ℝ) : ℂ) • uEv ε m := by
  refine ext_inner_right ℂ fun f => ?_
  have hU := KType.kUnit (modelKType ε hm) a a rfl (uEv ε m) f
  simp only [kunits, model_dτ, ContinuousLinearMap.coe_coe] at hU
  have hU' : ⟪dTau ε m (single a a 1) (uEv ε m), f⟫_ℂ = ⟪uEv ε m, dTau ε m (single a a 1) f⟫_ℂ := hU
  rw [hU', inner_uEv, ev_dTau_Eaa hm, inner_smul_left, inner_uEv]
  simp

theorem not_cone_neg_root {a b : Fin n} (hab : a < b) (c : Fin n → Fin n → ℕ) (hc : ∀ a' b', c a' b' ≠ 0 → a' < b')
    (h : Pi.single b (1 : ℝ) - Pi.single a 1 = ∑ a', ∑ b', (c a' b' : ℝ) • root a' b') : False := by
  apply CompanionTheory.RgFd.CkM.not_cone_neg_root <;> assumption

theorem uEv_hw {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    dTau ε m (single a b 1) (uEv ε m) = 0 := by
  apply CompanionTheory.RgFd.CkM.uEv_hw <;> assumption

theorem evaluation_longest_weyl_one {ε : Fin n → Bool} {m : Fin n → ℤ} : ev ε m (w0 ε m) = 1 := by
  rw [ev_apply]; exact highest_weight_fn_K_one ε m

theorem uEv_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    uEv ε m = ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) • wN ε m := by
  have hne : uEv ε m ≠ 0 := by
    intro h
    have := inner_uEv (w0 ε m)
    rw [h, inner_zero_left, evaluation_longest_weyl_one] at this
    exact zero_ne_one this
  obtain ⟨-, c, hc⟩ := HW.KType.hw_unique (modelKType ε hm) hne
    ⟨fun a => by rw [kunits, model_dτ]; exact uEv_wt hm a, fun a b hab he => by
      rw [kunits, model_dτ]; exact uEv_hw hm hab he⟩
  rw [model_w] at hc
  have hc' : uEv ε m = c • wN ε m := hc
  have hcv : starRingEnd ℂ c = ev ε m (wN ε m) := by
    rw [← inner_uEv, hc', inner_smul_left, inner_self_eq_norm_sq_to_K, norm_wN]; simp
  have hev : ev ε m (wN ε m) = ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) := by
    rw [wN, map_smul, evaluation_longest_weyl_one, smul_eq_mul, mul_one]
  have : c = ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) := by
    have h2 := congrArg (starRingEnd ℂ) hcv
    rw [Complex.conj_conj, hev, Complex.conj_ofReal] at h2
    exact h2
  rw [hc', this]

theorem ckModel : PositivityTheory.RgFd.CkModel := by
  intro n ε m hm k
  unfold PositivityTheory.RgFd.cK
  rw [model_op, model_w]
  show ‖⟪wN ε m, tauC ε m k (wN ε m)⟫_ℂ‖ = _
  have hw0 : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.2 (highest_weight_vector_ne_zero ε m)
  have h1 : ⟪wN ε m, tauC ε m k (wN ε m)⟫_ℂ = ((‖w0 ε m‖ : ℝ) : ℂ) * ⟪uEv ε m, tauC ε m k (wN ε m)⟫_ℂ := by
    rw [uEv_eq hm, inner_smul_left, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw0]
    simp
  rw [h1, inner_uEv, ev_apply, tauC_fn]
  show ‖((‖w0 ε m‖ : ℝ) : ℂ) * (wN ε m).fn (1 * k)‖ = _
  rw [one_mul, wN, MV.fn_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw0]
  simp [w0, MV.fn, MV.mk]

end PositivityTheory.RgFd.CkM
