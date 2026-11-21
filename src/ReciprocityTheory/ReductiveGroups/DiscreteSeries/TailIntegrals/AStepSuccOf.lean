import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergRankOneDecomposition
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DetEqMulMinorOfColZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Phi2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FixOfPerp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormBaseVectorRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
import Mathlib

section
noncomputable section

set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section grp
variable (k r' : ℕ)

theorem mat_ext_lev {A B : Mat k (1 + r')} (h0 : A *ᵥ e0 k r' = B *ᵥ e0 k r')
    (h1 : A *ᵥ es0 k r' = B *ᵥ es0 k r') (h2 : ∀ v, A *ᵥ liftVec k 1 r' v = B *ᵥ liftVec k 1 r' v) : A = B := by
  have key : ∀ q : Fin (2 * (1 + r') + k + 1), A *ᵥ Pi.single q 1 = B *ᵥ Pi.single q 1 := by
    intro q
    by_cases hq0 : q.val = 0
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = e0 k r' := by
        have hq : q = eI k (1 + r') (a0 r') := Fin.ext (by simp [eI, a0, hq0])
        rw [hq]
        rfl
      rw [he, h0]
    by_cases hql : q.val = 2 * (1 + r') + k
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = es0 k r' := by
        have hq : q = esI k (1 + r') (a0 r') := Fin.ext (by simp [esI, a0, hql])
        rw [hq]
        rfl
      rw [he, h1]
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) =
          liftVec k 1 r' (Pi.single ⟨q.val - 1, by omega⟩ 1) := by
        funext p
        simp only [liftVec, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [he, h2]
  ext p q
  have h := congrFun (key q) p
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h

theorem lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift]

theorem lev_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_lev
  · simp only [levi_fixes_base_vector, Matrix.one_mulVec]
  · simp only [levi_fixes_last_basis, Matrix.one_mulVec]
  · intro v
    simp only [lev_lift, Matrix.one_mulVec]

theorem lev_conjT (g : Mat k r') : (ιLev k 1 r' g)ᴴ = ιLev k 1 r' gᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, ιLev]
  split_ifs <;> (try subst_vars) <;> simp_all [Matrix.conjTranspose_apply]

theorem lev_mem {g : Mat k r'} (hg : g ∈ GV k r') : ιLev k 1 r' g ∈ GV k (1 + r') := by
  have hg' : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r')
  rw [lev_conjT]
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, Hpk_mulVec_e0, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, hermMatrix_last_basis, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, Hpk_lift]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem rankOne_levi_comm (c : ℂ) (g : Mat k r') : w0 k r' c * ιLev k 1 r' g = ιLev k 1 r' g * w0 k r' c := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, long_weyl_sends_base_to_dual, Matrix.mulVec_smul, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, rankOneMatrix_last_basis, Matrix.mulVec_smul, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, rankOneMatrix_lift]

theorem lev_K {κ : Mat k r'} (hκ : κ ∈ Kset k r') : ιLev k 1 r' κ ∈ Kset k (1 + r') := by
  refine ⟨lev_mem k r' hκ.1, ?_⟩
  rw [lev_conjT, ← lev_mul, hκ.2, lev_one]

end grp

section gn
variable {n : ℕ}

theorem normSq_sum_eq_trace (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem gN_unitary (k r : ℕ) {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  have h1 := normSq_sum_eq_trace (κ * X)
  have h2 := normSq_sum_eq_trace X
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul] at h1
  exact_mod_cast h1.trans h2.symm

theorem gN_cont (k r : ℕ) : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _
    fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

end gn

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace ThFin

theorem ga_nn (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : 0 ≤ Ga k r l Y := by
  unfold Ga
  open scoped ComplexOrder in
  have key : ∀ {m : ℕ} (W : Fin m → Fin (2 * r + k + 1) → ℂ),
      0 ≤ (Matrix.of fun a b => star (W a) ⬝ᵥ W b).det.re := by
    intro m W
    have h : (Matrix.of fun a b => star (W a) ⬝ᵥ W b) =
        (Matrix.of fun i a => W a i)ᴴ * Matrix.of fun i a => W a i := by
      ext a b
      simp [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
    rw [h]
    exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg).1
  exact key _

theorem dot_unit {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (u v : Fin n → ℂ) :
    star (U *ᵥ u) ⬝ᵥ (U *ᵥ v) = star u ⬝ᵥ v := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem ga_unit (k r : ℕ) (l : Fin (r + 1)) {U : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : Uᴴ * U = 1) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => U *ᵥ Y a) = Ga k r l Y := by
  unfold Ga
  simp only [dot_unit hU]

private lemma conjTranspose_Hpk_eq_Hpk (k r' : ℕ) : (Hpk k r')ᴴ = Hpk k r' := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | rfl | norm_num

private lemma Hpk_sq_eq_one (k r' : ℕ) : Hpk k r' * Hpk k r' = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hσ : (if (i : ℕ) < r' ∨ r' + k < (i : ℕ) then 2 * r' + k - i else (i : ℕ)) < 2 * r' + k + 1 := by
    split_ifs <;> omega
  rw [Finset.sum_eq_single ⟨_, hσ⟩]
  · simp only [Hpk, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | rfl | norm_num
  · intro l _ hl
    have h0 : Hpk k r' i l = 0 := by
      simp only [Hpk, Matrix.of_apply, ne_eq, Fin.ext_iff] at hl ⊢
      split_ifs at hl ⊢ <;> first | (exfalso; omega) | rfl
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hpk_mem (k r' : ℕ) : Hpk k r' ∈ GV k r' := by
  simp only [GV, UH, Set.mem_setOf_eq]
  rw [conjTranspose_Hpk_eq_Hpk, Hpk_sq_eq_one, Matrix.one_mul]

theorem lev_conjT (k r' : ℕ) : (ιLev k 1 r' (Hpk k r'))ᴴ = ιLev k 1 r' (Hpk k r') := by
  have hc := conjTranspose_Hpk_eq_Hpk k r'
  ext p q
  rw [Matrix.conjTranspose_apply]
  unfold ιLev
  try dsimp only
  split_ifs <;> first | ((conv_rhs => rw [← hc]); rfl) | (simp; done) | (subst_vars; contradiction)

theorem lev_sq (k r' : ℕ) : ιLev k 1 r' (Hpk k r') * ιLev k 1 r' (Hpk k r') = 1 := by
  apply mat_eq_of_mulVec
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have e : (fun j => (ιLev k 1 r' (Hpk k r') *ᵥ v) (levPos k 1 r' j)) =
      Hpk k r' *ᵥ fun j => v (levPos k 1 r' j) := by
    funext j
    rw [RankOneLeviIdentities.ιLev_mulVec, dif_pos ⟨Nat.le_add_left 1 j.val, by
      show j.val + 1 < 2 * r' + k + 1 + 1; omega⟩]
    congr 1
  ext p
  rw [RankOneLeviIdentities.ιLev_mulVec]
  split_ifs with h
  · rw [e, Hpk_mulVec_mulVec]
    exact congrArg v (Fin.ext (show p.val - 1 + 1 = p.val by omega))
  · rw [RankOneLeviIdentities.ιLev_mulVec, dif_neg h]

theorem lev_inv (k r' : ℕ) : (ιLev k 1 r' (Hpk k r'))⁻¹ = ιLev k 1 r' (Hpk k r') :=
  Matrix.inv_eq_left_inv (lev_sq k r')

theorem mv3 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A * A = 1) (v : Fin n → ℂ) :
    (A * B * A) *ᵥ (A *ᵥ v) = A *ᵥ (B *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (A * B), hA, Matrix.mul_one, ← Matrix.mulVec_mulVec]

theorem heis_eq (hCL : HeisConjLev) (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    heis0 k r' (y, s) =
      ιLev k 1 r' (Hpk k r') * heis0 k r' (Hpk k r' *ᵥ y, s) * ιLev k 1 r' (Hpk k r') := by
  have h := hCL k r' (Hpk k r') (hpk_mem k r') (y, s)
  rw [lev_inv] at h
  dsimp only at h
  rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, lev_sq, Matrix.one_mul, Matrix.mul_assoc, lev_sq,
    Matrix.mul_one]

def tm (k r' : ℕ) (x : HPar k r') : HPar k r' := (Hpk k r' *ᵥ (-x.1), -x.2)

theorem ga_yx (hCL : HeisConjLev) (hInv : HeisInv) (k r' : ℕ) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (Yx k r' x) = Del k (1 + r') l (heis0 k r' (tm k r' x)) ^ 2 := by
  have hY : ∀ a, Yx k r' x a =
      ιLev k 1 r' (Hpk k r') *ᵥ (heis0 k r' (tm k r' x) *ᵥ phiV k (1 + r') a) := by
    intro a
    unfold Yx phi2 tm
    rw [hInv k r' x, heis_eq hCL k r' (-x.1) (-x.2), mv3 _ _ (lev_sq k r')]
  have hY' : Yx k r' x = fun a =>
      ιLev k 1 r' (Hpk k r') *ᵥ (heis0 k r' (tm k r' x) *ᵥ phiV k (1 + r') a) := funext hY
  have hU : (ιLev k 1 r' (Hpk k r'))ᴴ * ιLev k 1 r' (Hpk k r') = 1 := by rw [lev_conjT, lev_sq]
  rw [hY', ga_unit k (1 + r') l hU]
  unfold Del
  rw [Real.sq_sqrt (ga_nn _ _ _ _)]

theorem sgn_mp (k r' : ℕ) (i : Fin (2 * r' + k + 1)) :
    MeasurePreserving (fun z : ℂ => (-GS.sgnI k r' i) * z) volume volume := by
  unfold GS.sgnI
  split_ifs
  · simp only [neg_neg, one_mul]
    exact MeasurePreserving.id volume
  · simp only [neg_mul, one_mul]
    exact Measure.measurePreserving_neg volume

theorem hpk_neg_mp (k r' : ℕ) :
    MeasurePreserving (fun v : Fin (2 * r' + k + 1) → ℂ => Hpk k r' *ᵥ (-v)) volume volume := by
  have hP := volume_preserving_arrowCongr' (GS.sigE k r') (MeasurableEquiv.refl ℂ)
    (MeasurePreserving.id volume)
  have hS := volume_preserving_pi (f := fun (i : Fin (2 * r' + k + 1)) (z : ℂ) => (-GS.sgnI k r' i) * z)
    fun i => sgn_mp k r' i
  have e : (fun v : Fin (2 * r' + k + 1) → ℂ => Hpk k r' *ᵥ (-v)) =
      (fun (v : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) => (-GS.sgnI k r' i) * v i) ∘
        MeasurableEquiv.arrowCongr' (GS.sigE k r') (MeasurableEquiv.refl ℂ) := by
    funext v i
    simp only [Function.comp_apply, Pi.neg_apply, GS.hpk_mulVec, neg_mul, mul_neg]
    rfl
  rw [e]
  exact hS.comp hP

theorem tm_mp (k r' : ℕ) : MeasurePreserving (tm k r') volume volume :=
  (hpk_neg_mp k r').prod (Measure.measurePreserving_neg volume)

theorem lsq_cont {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => Lsq x l := by
  unfold Lsq
  exact continuous_const.add (continuous_finset_sum _ fun j _ => Continuous.if_const _
    (((continuous_apply j).comp continuous_fst).norm.pow 2) continuous_const)

theorem de_cont {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l := by
  unfold de
  refine Real.continuous_sqrt.comp (((lsq_cont l).mul ?_).add ?_)
  · unfold rhoSq
    exact ((lsq_cont _).add (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2)).add
      (continuous_finset_sum _ fun j _ => Continuous.if_const _
        (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2) continuous_const)
  · have h2 : Continuous fun x : Xp p m => ∑ j : Fin p, if (l : ℕ) ≤ (j : ℕ) then x.2.1 j * star (x.1 j) else 0 :=
      continuous_finset_sum _ fun j _ => Continuous.if_const _
        (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
          ((continuous_apply j).comp continuous_fst).star) continuous_const
    unfold bco
    fun_prop

def chF (p m : ℕ) (ν : Fin (p + 1) → ℝ) (y : Xp p m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de y l ^ (-(s0N p m l + ν l)))

theorem chF_meas (p m : ℕ) (ν : Fin (p + 1) → ℝ) : Measurable (chF p m ν) := by
  unfold chF
  exact Finset.measurable_prod _ fun l _ => ENNReal.measurable_ofReal.comp ((de_cont l).measurable.pow_const _)

end ThFin

theorem th_fin (hB2 : InductiveHeisenbergInputs) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k) (t : Fin (1 + r' + 1) → ℝ)
    (hν : CHCond (1 + r') fun l => t l - s0N (1 + r') (k - 1) l) :
    (∫⁻ x : HPar k r', ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2))) < ∞ := by
  obtain ⟨-, -, -, -, -, hCL, -, hInv, -⟩ := hB2
  obtain ⟨hF1, hF2⟩ := hF k r' hk
  have hpt : ∀ x : HPar k r', (∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2))) =
      ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l)
        (hcoord k r' (ThFin.tm k r' x)) := by
    intro x
    unfold ThFin.chF
    refine Finset.prod_congr rfl fun l _ => ?_
    have hd : 0 ≤ de (hcoord k r' (ThFin.tm k r' x)) l := Real.sqrt_nonneg _
    have he : ((2 : ℕ) : ℝ) * (-t l / 2) =
        -(s0N (1 + r') (k - 1) l + (t l - s0N (1 + r') (k - 1) l)) := by
      push_cast; ring
    rw [ThFin.ga_yx hCL hInv k r' x l, hF1, ← Real.rpow_natCast, ← Real.rpow_mul hd, he]
  calc (∫⁻ x : HPar k r', ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2)))
      = ∫⁻ x : HPar k r', ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l)
          (hcoord k r' (ThFin.tm k r' x)) := lintegral_congr hpt
    _ = ∫⁻ y, ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l) y :=
        (hF2.comp (ThFin.tm_mp k r')).lintegral_comp (ThFin.chF_meas _ _ _)
    _ < ∞ := hCH (1 + r') (k - 1) _ hν

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

theorem scale_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    (hr : (Module.finrank ℝ E : ℝ) < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → 0 < b →
      ∫⁻ x, ENNReal.ofReal ((a + b * ‖x‖) ^ (-r)) ∂μ ≤
        ENNReal.ofReal (K * a ^ (-r) * (a / b) ^ (Module.finrank ℝ E : ℝ)) := by
  have hg := integrable_one_add_norm (μ := μ) hr
  refine ⟨∫ x, (1 + ‖x‖) ^ (-r) ∂μ, integral_nonneg fun x => by positivity, fun a b ha hb => ?_⟩
  have ht : 0 < a / b := div_pos ha hb
  have ha' := ha.ne'
  have hb' := hb.ne'
  have hpt : ∀ x : E, (a + b * ‖x‖) ^ (-r) = a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r) := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
      ← Real.mul_rpow ha.le (by positivity : (0 : ℝ) ≤ 1 + (a / b)⁻¹ * ‖x‖)]
    congr 1
    first | (field_simp; done) | (field_simp; ring)
  have hF : Integrable (fun x => a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r)) μ :=
    (hg.comp_smul (inv_ne_zero ht.ne')).const_mul (a ^ (-r))
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall fun x =>
    mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (by positivity) _))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul, Measure.integral_comp_smul (μ := μ) (f := fun y => (1 + ‖y‖) ^ (-r)) (R := (a / b)⁻¹),
    smul_eq_mul, inv_pow, inv_inv, abs_of_pos (pow_pos ht _), Real.rpow_natCast]
  exact le_of_eq (by ring)

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section entries
variable (k r' : ℕ)

theorem entry_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) : M p q = (M *ᵥ bvec q) p := by
  rw [bvec, mulVec_single_one]; rfl

theorem dual_base_vector_eq_single : es0 k r' = bvec (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1)) := by
  funext p
  rw [last_basis_apply, bvec, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 (Fin.ext h1)) | (exfalso; exact h1 (congrArg Fin.val h2))

theorem heis_liftVec (hHA : HeisAct) (x : HPar k r') (z : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ liftVec k 1 r' z =
      liftVec k 1 r' z - herm (Hpk k (1 + r')) (liftVec k 1 r' z) (liftVec k 1 r' x.1) • e0 k r' := by
  rw [show heis0 k r' x = heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) from rfl, hHA, hermitian_form_base_vector_right,
    liftVec_out k r' z _ (Or.inr rfl), zero_smul, add_zero]

theorem heisenberg_dual_base_vector_formula (hHA : HeisAct) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  rw [show heis0 k r' x = heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) from rfl, hHA, hermitian_dual_base_vector_left,
    liftVec_out k r' x.1 _ (Or.inl rfl), star_zero, zero_smul, sub_zero, hermitian_form_base_vector_right, last_basis_apply, if_pos rfl,
    one_smul]
  exact (add_assoc _ _ _).symm

variable (c : ℂ) (g : Mat k r') (x : HPar k r')

theorem conj_gg (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, bvec_lev, ιLev_liftVec, heis_liftVec k r' hHA,
    reflection_mulVec_levelPos, Pi.sub_apply, Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, if_neg (by rw [levPos_val]; omega),
    smul_zero, sub_zero, bvec, mulVec_single_one]
  rfl

theorem conj_y (hHA : HeisAct) (i : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) ⟨2 * (1 + r') + k, by omega⟩ = x.1 i := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, levelEmbedding_mulVec_es0, heisenberg_dual_base_vector_formula k r' hHA, reflection_mulVec_levelPos,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, last_basis_apply,
    if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega)]
  simp

theorem conj_cb (hHA : HeisAct) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ =
      c * hb k r' x.1 x.2 := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, levelEmbedding_mulVec_es0, heisenberg_dual_base_vector_formula k r' hHA, rankOneMatrix_last_coord,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, liftVec_out k r' x.1 _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, last_basis_apply,
    if_neg (by simp only; omega), if_pos rfl]
  simp

theorem un_col (hHA : HeisAct) (j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g *ᵥ (heis0 k r' x *ᵥ bvec (levPos k 1 r' j)) =
      liftVec k 1 r' (g *ᵥ bvec j) -
        herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' x.1) • e0 k r' := by
  rw [bvec_lev, heis_liftVec k r' hHA, mulVec_sub, mulVec_smul, ιLev_liftVec, levi_embedding_mulVec_e0]

theorem un_gg (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, un_col k r' g x hHA, reflection_mulVec_levelPos, Pi.sub_apply,
    Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, if_neg (by rw [levPos_val]; omega), smul_zero, sub_zero, bvec,
    mulVec_single_one]
  rfl

theorem un_row (hHA : HeisAct) (j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ⟨2 * (1 + r') + k, by omega⟩ (levPos k 1 r' j) =
      -(c * herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' x.1)) := by
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, un_col k r' g x hHA, rankOneMatrix_last_coord, Pi.sub_apply,
    Pi.smul_apply, liftVec_out k r' _ _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, if_pos rfl]
  simp

theorem un_cb (hHA : HeisAct) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ =
      c * hb k r' x.1 x.2 := by
  have hv : ιLev k 1 r' g *ᵥ (heis0 k r' x *ᵥ es0 k r') =
      es0 k r' + liftVec k 1 r' (g *ᵥ x.1) + hb k r' x.1 x.2 • e0 k r' := by
    rw [heisenberg_dual_base_vector_formula k r' hHA, mulVec_add, mulVec_add, mulVec_smul, levelEmbedding_mulVec_es0, ιLev_liftVec, levi_embedding_mulVec_e0]
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, hv,
    rankOneMatrix_last_coord, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
    liftVec_out k r' _ _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, last_basis_apply, if_neg (by simp only; omega), if_pos rfl]
  simp

end entries

section bounds
variable (k r' : ℕ)

theorem exists_perm (y : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    ∃ j : Fin (2 * r' + k + 1),
      ‖herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' y)‖ = ‖y i‖ := by
  by_cases hA : i.val + 1 < 1 + r' ∨ 1 + r' + k < i.val + 1
  · refine ⟨⟨2 * (1 + r') + k - (i.val + 1) - 1, by omega⟩, ?_⟩
    rw [herm_bvec, norm_star, hpk_mulVec', if_pos (by rw [levPos_val]; simp only; omega), liftVec_apply,
      dif_pos (by simp only [levPos_val]; omega)]
    exact congrArg (fun t => ‖y t‖) (Fin.ext (by simp only [levPos_val]; omega))
  · refine ⟨i, ?_⟩
    rw [herm_bvec, norm_star, hpk_mulVec', if_neg (by rw [levPos_val]; omega)]
    split_ifs <;> simp [liftVec_lev]

theorem gN_nonneg' {n : ℕ} (M : Mat k n) : 0 ≤ gN M := Real.sqrt_nonneg _

theorem gN_entry {n : ℕ} (M : Mat k n) (p q : Fin (2 * n + k + 1)) : ‖M p q‖ ≤ gN M := by
  rw [← Real.sqrt_sq (norm_nonneg (M p q)), Complex.sq_norm]
  unfold gN
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (M p q) ≤ ∑ j, Complex.normSq (M p j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (M p j)) (fun j _ => Complex.normSq_nonneg _)
          (Finset.mem_univ q)
    _ ≤ ∑ i, ∑ j, Complex.normSq (M i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (M i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ p)

theorem gN_sub (M : Mat k (1 + r')) (g : Mat k r')
    (h : ∀ i j, M (levPos k 1 r' i) (levPos k 1 r' j) = g i j) : gN g ≤ gN M := by
  unfold gN
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (g i j)
      = ∑ i, ∑ j, Complex.normSq (M (levPos k 1 r' i) (levPos k 1 r' j)) := by simp only [h]
    _ ≤ ∑ i, ∑ q, Complex.normSq (M (levPos k 1 r' i) q) :=
        Finset.sum_le_sum fun i _ => sum_lev_le k r' (fun q => Complex.normSq (M (levPos k 1 r' i) q))
          fun q => Complex.normSq_nonneg _
    _ ≤ ∑ p, ∑ q, Complex.normSq (M p q) :=
        sum_lev_le k r' (fun p => ∑ q, Complex.normSq (M p q))
          fun p => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _

theorem hb_im (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : (hb k r' y s).im = s := by simp [hb]

theorem cs_le (c : ℂ) (x : HPar k r') (M : Mat k (1 + r'))
    (h : M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ = c * hb k r' x.1 x.2) :
    ‖c‖ * |x.2| ≤ gN M := by
  calc ‖c‖ * |x.2| ≤ ‖c‖ * ‖hb k r' x.1 x.2‖ := by
        gcongr
        have := Complex.abs_im_le_norm (hb k r' x.1 x.2)
        rwa [hb_im] at this
    _ = ‖M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩‖ := by rw [h, norm_mul]
    _ ≤ gN M := gN_entry k _ _ _

variable (c : ℂ) (g : Mat k r') (x : HPar k r')

theorem pt_conj (hHA : HeisAct) :
    gN g ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ∧
      ‖x.1‖ ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ∧
      ‖c‖ * |x.2| ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) := by
  refine ⟨gN_sub k r' _ g (conj_gg k r' c g x hHA), ?_, cs_le k r' c x _ (conj_cb k r' c g x hHA)⟩
  refine (pi_norm_le_iff_of_nonneg (gN_nonneg' k _)).2 fun i => ?_
  rw [← conj_y k r' c g x hHA i]
  exact gN_entry k _ _ _

theorem pt_un (hHA : HeisAct) :
    gN g ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * ‖x.1‖ ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * |x.2| ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
  refine ⟨gN_sub k r' _ g (un_gg k r' c g x hHA), ?_, cs_le k r' c x _ (un_cb k r' c g x hHA)⟩
  rw [← norm_smul]
  refine (pi_norm_le_iff_of_nonneg (gN_nonneg' k _)).2 fun i => ?_
  obtain ⟨j, hj⟩ := exists_perm k r' x.1 i
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, ← hj, ← norm_mul, ← norm_neg, ← un_row k r' c g x hHA j]
  exact gN_entry k _ _ _

end bounds

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem pt_bound {N a u v p q : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : a ≤ N) (h2 : u ≤ N) (h3 : v ≤ N) :
    N ^ (-(p + q)) ≤ 2 ^ (p + q) * ((a + u) ^ (-p) * (a + v) ^ (-q)) := by
  have hN : 0 < N := lt_of_lt_of_le ha h1
  have hau : 0 < a + u := by linarith
  have hav : 0 < a + v := by linarith
  have hmono : ∀ {x e : ℝ}, 0 < x → x ≤ 2 * N → 0 ≤ e → (2 * N) ^ (-e) ≤ x ^ (-e) := by
    intro x e hx hxN he
    rw [Real.rpow_neg (by linarith), Real.rpow_neg hx.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx e) (Real.rpow_le_rpow hx.le hxN he)
  have e1 : (2 * N) ^ (-p) ≤ (a + u) ^ (-p) := hmono hau (by linarith) hp
  have e2 : (2 * N) ^ (-q) ≤ (a + v) ^ (-q) := hmono hav (by linarith) hq
  have key : 2 ^ (p + q) * ((2 * N) ^ (-p) * (2 * N) ^ (-q)) = N ^ (-(p + q)) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < 2 * N), Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le,
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), show p + q + (-p + -q) = (0:ℝ) by ring,
      Real.rpow_zero, one_mul, neg_add]
  rw [← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (by positivity) (by positivity)) (by positivity)

theorem liftVec_cont (k r' : ℕ) : Continuous fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y := by
  apply continuous_pi
  intro p
  simp only [liftVec]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

def heisM (k r' : ℕ) : HPar k r' → Mt k (1 + r') := fun x => heis0 k r' x

theorem heisenberg_map_continuous (k r' : ℕ) : Continuous (heisM k r') := by
  have hl := liftVec_cont k r'
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [heisM, heis0, heisG, hb, herm, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Pi.star_apply]
  fun_prop

theorem heisenberg_at_zero (k r' : ℕ) : heis0 k r' (0, 0) = 1 := by
  have hz : liftVec k 1 r' 0 = 0 := by
    funext p
    simp only [liftVec, Pi.zero_apply]
    split_ifs <;> rfl
  ext i j
  simp [heis0, heisG, hb, herm, hz, Matrix.vecMulVec]

theorem ιLev_inv_mul (hCL : HeisConjLev) (k r' : ℕ) (g : Mat k r') (hg : g ∈ GV k r') :
    (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := by
  have h := hCL k r' g hg (0, 0)
  simp only [heisenberg_at_zero, mul_one, Matrix.mulVec_zero] at h
  first
  | exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h)
  | exact mul_eq_one_comm.mp h
  | exact (Matrix.mul_eq_one_comm).1 h

theorem gN_cont (k n : ℕ) : Continuous fun M : Mat k n => gN M := by
  simp only [gN]
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem int_conj (hCL : HeisConjLev) (hCM : HeisConjLevMeas) (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r')
    (hg : g ∈ GV k r') :
    ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A)) := by
  have hinv : (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := ιLev_inv_mul hCL k r' g hg
  have hgN := gN_cont k (1 + r')
  have hcm : Continuous fun M : Mt k (1 + r') => w0 k r' c * Matrix.of M * ιLev k 1 r' g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hH : Measurable fun M : Mt k (1 + r') =>
      ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) :=
    ((hgN.comp hcm).measurable.pow_const _).ennreal_ofReal
  have hcc : Continuous (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hconj : Measurable (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) := hcc.measurable
  have hheis : Measurable (heisM k r') := (heisenberg_map_continuous k r').measurable
  have hL : ∀ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      (fun M : Mt k (1 + r') => ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
        (conjM (ιLev k 1 r' g) (heis0 k r' x)) := by
    intro x
    have e : w0 k r' c * Matrix.of (conjM (ιLev k 1 r' g) (heis0 k r' x)) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x := by
      change w0 k r' c * (ιLev k 1 r' g * heis0 k r' x * (ιLev k 1 r' g)⁻¹) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x
      simp only [mul_assoc, hinv, mul_one]
    simp only [e]
  calc ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))
      = ∫⁻ x : HPar k r', (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) (heis0 k r' x)) := lintegral_congr fun x => hL x
    _ = ∫⁻ M, (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) M) ∂(μHeis k r') := (lintegral_map (hH.comp hconj) hheis).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A))
          ∂((μHeis k r').map (conjM (ιLev k 1 r' g))) := (lintegral_map hH hconj).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) ∂(μHeis k r') := by
          rw [hCM k r' g hg]
    _ = ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * Matrix.of (heis0 k r' x : Mt k (1 + r')) * ιLev k 1 r' g) ^ (-A)) :=
          lintegral_map hH hheis
    _ = _ := rfl

theorem int_prod (k r' : ℕ) {A p q K₁ K₂ e₁ e₂ : ℝ} (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b * ‖y‖) ^ (-p)) ≤
      ENNReal.ofReal (K₁ * a ^ (-p) * (a / b) ^ e₁))
    (hK₂ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ s : ℝ, ENNReal.ofReal ((a + b * ‖s‖) ^ (-q)) ≤
      ENNReal.ofReal (K₂ * a ^ (-q) * (a / b) ^ e₂))
    (F : HPar k r' → ℝ≥0∞) {a b₁ b₂ : ℝ} (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hF : ∀ x : HPar k r', F x ≤
      ENNReal.ofReal (2 ^ A * ((a + b₁ * ‖x.1‖) ^ (-p) * (a + b₂ * ‖x.2‖) ^ (-q)))) :
    ∫⁻ x, F x ≤ ENNReal.ofReal (2 ^ A * (K₁ * a ^ (-p) * (a / b₁) ^ e₁) * (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
  have hf₁ : Measurable fun y : Fin (2 * r' + k + 1) → ℂ => ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hf₂ : Measurable fun s : ℝ => ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hX : 0 ≤ K₁ * a ^ (-p) * (a / b₁) ^ e₁ :=
    mul_nonneg (mul_nonneg hK₁0 (Real.rpow_nonneg ha.le _)) (Real.rpow_nonneg (div_pos ha hb₁).le _)
  have h2A : (0 : ℝ) ≤ 2 ^ A := by positivity
  calc ∫⁻ x, F x ≤ ∫⁻ x : HPar k r', ENNReal.ofReal (2 ^ A) *
        (ENNReal.ofReal ((a + b₁ * ‖x.1‖) ^ (-p)) * ENNReal.ofReal ((a + b₂ * ‖x.2‖) ^ (-q))) := by
        refine lintegral_mono fun x => (hF x).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul h2A, ENNReal.ofReal_mul (Real.rpow_nonneg
          (add_nonneg ha.le (mul_nonneg hb₁.le (norm_nonneg _))) _)]
    _ = ENNReal.ofReal (2 ^ A) * ((∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p))) *
          ∫⁻ s : ℝ, ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_prod_mul (μ := (volume : Measure (Fin (2 * r' + k + 1) → ℂ)))
          (ν := (volume : Measure ℝ)) hf₁.aemeasurable hf₂.aemeasurable
    _ ≤ ENNReal.ofReal (2 ^ A) * (ENNReal.ofReal (K₁ * a ^ (-p) * (a / b₁) ^ e₁) *
          ENNReal.ofReal (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
        gcongr
        · exact hK₁ a b₁ ha hb₁
        · exact hK₂ a b₂ ha hb₂
    _ = _ := by
        rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul h2A]
        congr 1
        ring

theorem eInt_bound' (hGL : GNLower) (hHA : HeisAct) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) ≤
        ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
          gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hd] at hA ⊢
  have hd3 : (3 : ℝ) ≤ d := by rw [hd]; norm_cast; omega
  have hE : (Module.finrank ℝ (Fin (2 * r' + k + 1) → ℂ) : ℝ) = d - 1 := by
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hd]; push_cast; ring
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = d - 1 + (A - d) / 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 + (A - d) / 2 := ⟨_, rfl⟩
  have hpq : p + q = A := by rw [hp, hq]; ring
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := scale_int (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) (r := p)
    (by rw [hE, hp]; linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := scale_int (volume : Measure ℝ) (r := q)
    (by simp only [Module.finrank_self, Nat.cast_one]; rw [hq]; linarith)
  rw [hE] at hK₁
  simp only [Module.finrank_self, Nat.cast_one] at hK₂
  refine ⟨2 ^ A * K₁ * K₂, fun c hc g hg => ?_⟩
  have ha : 0 < gN g := lt_of_lt_of_le zero_lt_one (hGL k r' g hg)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have B1 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))) ha hc0 hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_un k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      have := pt_bound ha (mul_nonneg hc0.le (norm_nonneg _)) (mul_nonneg hc0.le (norm_nonneg _))
        hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  have B2 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A))) ha one_pos hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_conj k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      rw [← one_mul ‖x.1‖] at h2
      have := pt_bound ha (by positivity) (mul_nonneg hc0.le (norm_nonneg _)) hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  rw [← int_conj hCL hCM k r' A c g hg] at B2
  have ea : gN g ^ (d - A) = gN g ^ (-p) * gN g ^ (d - 1) * gN g ^ (-q) * gN g ^ (1 : ℝ) := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha, ← Real.rpow_add ha]
    congr 1
    linarith
  have E1 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / ‖c‖) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖ ^ (-d) * gN g ^ (d - A) := by
    have ec : ‖c‖ ^ (-d) = ‖c‖ ^ (-(d - 1)) * ‖c‖ ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; ring
    rw [Real.div_rpow ha.le hc0.le, Real.div_rpow ha.le hc0.le, ea, ec, Real.rpow_neg hc0.le,
      Real.rpow_neg hc0.le]
    ring
  have E2 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / 1) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖⁻¹ * gN g ^ (d - A) := by
    rw [div_one, Real.div_rpow ha.le hc0.le, ea, Real.rpow_one, Real.rpow_one]
    ring
  rcases le_total (‖c‖ ^ (-d)) ‖c‖⁻¹ with h | h
  · rw [min_eq_left h, ← E1]; exact B1
  · rw [min_eq_right h, ← E2]; exact B2

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def EInt (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r') : ℝ≥0∞ :=
  ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))

theorem eInt_bound (hGL : GNLower) (hHA : HeisAct) (hHC : HeisClosed) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      EInt k r' A c g ≤ ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  exact ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.eInt_bound' hGL hHA hCL hCM k r' A hA

theorem cInt_fin (n : ℕ) (σ : ℝ) (h1 : 1 < σ) (h2 : σ < 2 * (n : ℝ) + 1) :
    (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
      ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹)) < ∞ := by
  have hF0 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioc 0 1) := by
    refine Integrable.mono'
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 * (n : ℝ) - σ)
        (by linarith)).1 ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := hy.1
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) hA) hy0.le
        _ = y ^ (2 * (n : ℝ) - σ) := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one]
  have hF1 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -σ) (by linarith) zero_lt_one) ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := zero_lt_one.trans hy
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y ^ (-((2 * n + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_left _ _) hA) hy0.le
        _ = y ^ (-σ) := by
          rw [← mul_assoc, mul_comm y, ← Real.rpow_add_one hy0.ne', ← Real.rpow_add hy0]
          congr 1
          push_cast
          ring
  have hY : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hF0.union hF1
  have hI : Integrable (fun c : ℂ => ‖c‖ ^ (2 * (n : ℝ) - σ) *
      min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) volume := by
    first
      | exact (integrable_fun_norm_addHaar volume
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
      | exact (integrable_fun_norm_addHaar (μ := volume)
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
  calc (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
        ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹))
      = ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ) *
          min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) :=
        lintegral_congr fun c => (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm
    _ < ∞ := hI.lintegral_lt_top

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem heisenbergFacts_of_inductiveInput (h : InductiveHeisenbergInputs) : OneStepInt ∧ OneStepCoord ∧ HeisConjLev ∧ HeisInv ∧ HeisMem ∧ HeisHaar ∧
    HaarGExists ∧ HeisAct ∧ GNLower ∧ HeisClosed ∧ HeisConjLevMeas := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27⟩ := h
  exact ⟨h1, h2, h6, h8, h10, h12, h26, h27, h16, h11, h7⟩

section cont
variable (k r' : ℕ)

theorem lift_cont : Continuous (liftVec k 1 r') := by
  refine continuous_pi fun p => ?_
  unfold liftVec
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]; exact continuous_apply _
  · simp only [dif_neg hp]; exact continuous_const

theorem heisenberg_map_continuous : Continuous (heis0 k r') := by
  have h1 : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (lift_cont k r').comp continuous_fst
  unfold heis0 heisG hb herm
  fun_prop

theorem lev_cont : Continuous (fun g : Mat k r' => ιLev k 1 r' g) := by
  refine continuous_matrix fun p q => ?_
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq]; exact continuous_id.matrix_elem _ _
    · simp only [dif_pos hp, dif_neg hq]; exact continuous_const
  · simp only [dif_neg hp]; exact continuous_const

theorem Dl_cont (r : ℕ) (l : Fin (r + 1)) : Continuous (fun g : Mt k r => Dl k r l (Matrix.of g)) := by
  unfold Dl herm
  fun_prop

theorem FsE_meas (r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable (fun g : Mt k r => FsE k r s (Matrix.of g)) := by
  unfold FsE
  exact Finset.measurable_prod _ fun l _ =>
    ((Dl_cont k r l).measurable.nnnorm.coe_nnreal_ennreal).pow_const _

theorem EInt_meas (A : ℝ) (c : ℂ) : Measurable (fun g : Mt k r' => EInt k r' A c (Matrix.of g)) := by
  unfold EInt
  have h1 := heisenberg_map_continuous k r'
  have h2 := lev_cont k r'
  have h3 := gN_cont k (1 + r')
  refine Measurable.lintegral_prod_right'
    (f := fun p : Mt k r' × HPar k r' =>
      ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2) ^ (-A))) ?_
  exact ((by fun_prop : Continuous fun p : Mt k r' × HPar k r' =>
    gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2)).measurable.pow_const _).ennreal_ofReal

theorem heis_left (hHH : HeisHaar) (F : Mt k (1 + r') → ℝ≥0∞) (hF : Measurable F) (z : HPar k r') :
    ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ x, F (heis0 k r' x) := by
  have hc : @Continuous (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := heisenberg_map_continuous k r'
  have hm : @Measurable (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := hc.measurable
  have hl : Measurable (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r')) :=
    (by unfold lmulM; fun_prop : Continuous (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r'))).measurable
  calc ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ n, F (lmulM (heis0 k r' z) n) ∂(μHeis k r') := by
        rw [μHeis]; exact (lintegral_map (hF.comp hl) hm).symm
    _ = ∫⁻ n, F n ∂((μHeis k r').map (lmulM (heis0 k r' z))) := (lintegral_map hF hl).symm
    _ = ∫⁻ n, F n ∂(μHeis k r') := by rw [(hHH k r').left _ ⟨z, rfl⟩]
    _ = ∫⁻ x, F (heis0 k r' x) := by rw [μHeis]; exact lintegral_map hF hm

theorem EInt_K (A : ℝ) (c : ℂ) {κ : Mat k r'} (hκ : κ ∈ Kset k r') (g : Mat k r') :
    EInt k r' A c (κ * g) = EInt k r' A c g := by
  unfold EInt
  refine lintegral_congr fun x => ?_
  have e : w0 k r' c * ιLev k 1 r' (κ * g) * heis0 k r' x =
      ιLev k 1 r' κ * (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
    rw [lev_mul, ← Matrix.mul_assoc (w0 k r' c), rankOne_levi_comm]; simp only [Matrix.mul_assoc]
  rw [e, gN_unitary k (1 + r') (lev_K k r' hκ).2]

end cont

section inner
variable (k r' : ℕ)

def Dx (x : HPar k r') : ℝ := Real.sqrt (Ga k (1 + r') 0 (Yx k r' x))

def Psi (s : Fin (1 + r' + 1) → ℝ) (x : HPar k r') : ℝ :=
  ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)

def Qf (A : ℝ) (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (c : ℂ) : ℝ≥0∞ :=
  ∫⁻ g, EInt k r' A c (Matrix.of g) * FsE k r' s1 (Matrix.of g) ∂μ₁

theorem inner_eq (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A : ℝ) (s : Fin (1 + r' + 1) → ℝ)
    (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (x : HPar k r') (c : ℂ) (hc : c ≠ 0) :
    ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁ =
      ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
  obtain ⟨-, -, hHCL, -, -, hHH, -, -, -, -, -⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨κ, hκ, m, hm, z, hdec, hga⟩ := heisenberg_rankOne_decomposition hB2 hIW k r' hk x c hc
  have hG0 := (yx_ga hB2 hIW k r' hk x).1
  have hdec' : (heis0 k r' x)⁻¹ * w0 k r' c =
      κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m * heis0 k r' z := hdec
  have hpt : ∀ g : Mt k r', Matrix.of g ∈ GV k r' →
      ∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A)) =
        EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) := by
    intro g hg
    obtain ⟨z2, hz2⟩ : ∃ z2 : HPar k r', z2 = ((Matrix.of g)⁻¹ *ᵥ z.1, z.2) := ⟨_, rfl⟩
    have hcomm : heis0 k r' z * ιLev k 1 r' (Matrix.of g) = ιLev k 1 r' (Matrix.of g) * heis0 k r' z2 := by
      have h1 := hHCL k r' (Matrix.of g) hg z2
      have h2 : ((Matrix.of g *ᵥ z2.1, z2.2) : HPar k r') = z := by
        rw [hz2]; dsimp only; rw [mulVec_mulVec, UH_mul_inv k r' hg, one_mulVec]
      rw [h2] at h1
      rw [← h1, Matrix.mul_assoc, UH_inv_mul k (1 + r') (lev_mem k r' hg), Matrix.mul_one]
    have hmat : ∀ x', oneStep k r' x c (Matrix.of g) x' =
        κ * (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * (heis0 k r' z2 * heis0 k r' x')) := by
      intro x'
      unfold oneStep
      rw [hdec', Matrix.mul_assoc (κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m) (heis0 k r' z)
        (ιLev k 1 r' (Matrix.of g)), hcomm, lev_mul]
      simp only [Matrix.mul_assoc]
    simp only [hmat, gN_unitary k (1 + r') hκ.2]
    have h3 := gN_cont k (1 + r')
    have hF : Measurable fun n : Mt k (1 + r') =>
        ENNReal.ofReal (gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n) ^ (-A)) :=
      ((by fun_prop : Continuous fun n : Mt k (1 + r') =>
        gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n)).measurable.pow_const
          _).ennreal_ofReal
    exact heis_left k r' hHH _ hF z2
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by
    rw [ae_iff]; exact hμ₁.conc
  have hl : Measurable (lmulM m : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m : Mt k r' → Mt k r')).measurable
  have hli : Measurable (lmulM m⁻¹ : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m⁻¹ : Mt k r' → Mt k r')).measurable
  have hG : Measurable (fun g : Mt k r' => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
      FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g)) :=
    (EInt_meas k r' A _).mul ((FsE_meas k r' (fun l => s (sc r' l))).comp hli)
  have e : ∀ g : Mt k r', m⁻¹ * (m * Matrix.of g) = Matrix.of g := fun g => by
    rw [← Matrix.mul_assoc, UH_inv_mul k r' hm, Matrix.one_mul]
  calc ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁
      = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of (lmulM m g)) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of (lmulM m g)) ∂μ₁ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hconc] with g hg
        rw [hpt g hg]
        show _ = EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * (m * Matrix.of g))
        rw [e]
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂(μ₁.map (lmulM m)) := (lintegral_map hG hl).symm
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂μ₁ := by rw [hμ₁.left m hm]
    _ = ENNReal.ofReal (fsR k r' (fun l => s (sc r' l)) m) *
          Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) :=
        hT k r' (fun l => s (sc r' l)) μ₁ (fun g => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g)) hk hμ₁
          (EInt_meas k r' A _) (fun κ' hκ' g => EInt_K k r' A _ hκ' (Matrix.of g)) m hm
    _ = ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
        congr 1; congr 1
        unfold fsR Psi
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [eq_div_of_mul_eq hG0.ne' (hga l)]

end inner

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section chain
variable (k r' : ℕ)

def mw (c : ℂ) : ℝ := min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹

theorem mw_nonneg (c : ℂ) : 0 ≤ mw k r' c :=
  le_min (Real.rpow_nonneg (norm_nonneg _) _) (inv_nonneg.mpr (norm_nonneg _))

theorem mw_meas : Measurable (mw k r') := by
  unfold mw
  exact (measurable_norm.pow_const _).min measurable_norm.inv

theorem weight_eq (s : Fin (1 + r' + 1) → ℝ) (c : ℂ) (hc : c ≠ 0) :
    ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) * ∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l) =
      ENNReal.ofReal (‖c‖ ^ (2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l)) := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h1 : ∀ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l) = ENNReal.ofReal (‖c‖ ^ (-s l)) := fun l => by
    have e : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖c‖ := by rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
    rw [e, ENNReal.ofReal_rpow_of_pos hpos]
  simp only [h1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _)]
  congr 1
  rw [← Real.rpow_sum_of_pos hpos, ← Real.rpow_natCast, ← Real.rpow_add hpos]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib]; ring

theorem Qf_le (A C0 : ℝ)
    (hC0 : ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r', EInt k r' A c g ≤ ENNReal.ofReal (C0 * mw k r' c *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)))
    (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (c : ℂ) (hc : c ≠ 0) :
    Qf k r' A s1 μ₁ c ≤
      ENNReal.ofReal (|C0| * mw k r' c) * JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) s1 := by
  unfold Qf JInt
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by rw [ae_iff]; exact hμ₁.conc
  filter_upwards [hconc] with g hg
  rw [← mul_assoc]
  gcongr ?_ * _
  refine (hC0 c hc _ hg).trans ?_
  have hG : 0 ≤ gN (Matrix.of g) ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A) :=
    Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) _
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (mw_nonneg k r' c)),
    show -(A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A by ring]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (mw_nonneg k r' c)) hG

theorem scale_c (aw D : ℝ) (hD : 0 < D) :
    ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' (c * (D : ℂ))) =
      ENNReal.ofReal (D ^ (-(aw + 2))) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) := by
  have hF : Measurable fun c : ℂ => ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) :=
    (measurable_norm.pow_const _).ennreal_ofReal.mul (mw_meas k r').ennreal_ofReal
  have h1 : ∀ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' (c * (D : ℂ))) =
      ENNReal.ofReal (D ^ (-aw)) * (ENNReal.ofReal (‖D • c‖ ^ aw) * ENNReal.ofReal (mw k r' (D • c))) := by
    intro c
    have e : c * (D : ℂ) = D • c := by rw [Complex.real_smul, mul_comm]
    rw [e, norm_smul, Real.norm_of_nonneg hD.le, Real.mul_rpow hD.le (norm_nonneg _), ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _), ← mul_assoc, ← Real.rpow_add hD, neg_add_cancel,
      Real.rpow_zero, one_mul]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ c : ℂ, ENNReal.ofReal (‖D • c‖ ^ aw) * ENNReal.ofReal (mw k r' (D • c)) =
      ENNReal.ofReal (D ^ (-2 : ℝ)) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) := by
    rw [← lintegral_map hF (measurable_const_smul D), Measure.map_addHaar_smul volume hD.ne',
      lintegral_smul_measure]
    congr 2
    rw [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hD 2)), Real.rpow_neg hD.le,
      Real.rpow_two]
  rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _), ← Real.rpow_add hD]
  congr 3; ring

theorem inner_c_le (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A C0 : ℝ)
    (hC0 : ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r', EInt k r' A c g ≤ ENNReal.ofReal (C0 * mw k r' c *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)))
    (s : Fin (1 + r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) [SFinite μ₁] (hμ₁ : IsHaarOn (GV k r') μ₁)
    (c : ℂ) (hc : c ≠ 0) :
    ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
      ∫⁻ p : (HPar k r' × HPar k r') × Mt k r',
        ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
          FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2))
        ∂((volume : Measure (HPar k r' × HPar k r')).prod μ₁) ≤
    ENNReal.ofReal (‖c‖ ^ (2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l)) *
      ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
        (ENNReal.ofReal (|C0| * mw k r' (c * (Dx k r' x : ℂ))) *
          JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l))) := by
  obtain ⟨-, -, -, hHI, hHM, -, -, hHA, -, -, -⟩ := heisenbergFacts_of_inductiveInput hB2
  have hos : ∀ (x : HPar k r') (g : Mat k r') (x' : HPar k r'),
      oneStep k r' x c g x' = heis0 k r' (-x.1, -x.2) * w0 k r' c * ιLev k 1 r' g * heis0 k r' x' := by
    intro x g x'; unfold oneStep; rw [hHI]
  have hK : (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) ≠ ⊤ := ENNReal.prod_ne_top fun l _ => by
    rw [← ENNReal.coe_rpow_of_ne_zero (nnnorm_ne_zero_iff.mpr hc)]; exact ENNReal.coe_ne_top
  obtain ⟨H, hHdef⟩ : ∃ H : (HPar k r' × HPar k r') × Mt k r' → ℝ≥0∞, H = fun p =>
      ENNReal.ofReal (gN (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) ^ (-A)) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) := ⟨_, rfl⟩
  have h3 := gN_cont k (1 + r')
  have h2 := lev_cont k r'
  have h1 := heisenberg_map_continuous k r'
  have hHm : Measurable H := by
    have hc1 : Continuous fun p : (HPar k r' × HPar k r') × Mt k r' =>
        gN (heis0 k r' (-p.1.1.1, -p.1.1.2) * w0 k r' c * ιLev k 1 r' (Matrix.of p.2) * heis0 k r' p.1.2) := by
      fun_prop
    have e : H = fun p => ENNReal.ofReal (gN (heis0 k r' (-p.1.1.1, -p.1.1.2) * w0 k r' c *
        ιLev k 1 r' (Matrix.of p.2) * heis0 k r' p.1.2) ^ (-A)) *
          FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) := by
      rw [hHdef]; funext p; rw [hos]
    rw [e]
    exact (hc1.measurable.pow_const _).ennreal_ofReal.mul ((FsE_meas k r' _).comp measurable_snd)
  have hstep1 : ∀ p : (HPar k r' × HPar k r') × Mt k r',
      ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
        FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) =
          (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * H p := by
    intro p
    have hf : FsE k (1 + r') s (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) =
        (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) :=
      FsE_oneStep k r' hHA hHM p.1.1 p.1.2 c (Matrix.of p.2) s
    show ENNReal.ofReal (gN (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) ^ (-A)) *
        FsE k (1 + r') s (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) = _
    rw [hf, hHdef]
    ring
  simp_rw [hstep1]
  rw [lintegral_const_mul' _ _ hK, ← mul_assoc, weight_eq k r' s c hc]
  gcongr
  rw [lintegral_prod _ hHm.aemeasurable,
    show (volume : Measure (HPar k r' × HPar k r')) = (volume : Measure (HPar k r')).prod volume from rfl,
    lintegral_prod _ hHm.lintegral_prod_right'.aemeasurable]
  refine lintegral_mono fun x => ?_
  have hsw : Measurable (Function.uncurry fun (x' : HPar k r') (g : Mt k r') => H ((x, x'), g)) :=
    hHm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hsw.aemeasurable]
  have hmx : ∀ g : Mt k r', Measurable fun x' : HPar k r' =>
      ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A)) := by
    intro g
    have e : (fun x' : HPar k r' => ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) =
        fun x' => ENNReal.ofReal (gN (heis0 k r' (-x.1, -x.2) * w0 k r' c * ιLev k 1 r' (Matrix.of g) *
          heis0 k r' x') ^ (-A)) := by
      funext x'; rw [hos]
    rw [e]
    exact ((by fun_prop : Continuous fun x' : HPar k r' => gN (heis0 k r' (-x.1, -x.2) * w0 k r' c *
      ιLev k 1 r' (Matrix.of g) * heis0 k r' x')).measurable.pow_const _).ennreal_ofReal
  have hin : ∀ g : Mt k r', ∫⁻ x', H ((x, x'), g) =
      (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) := by
    intro g; simp only [hHdef]; exact lintegral_mul_const _ (hmx g)
  simp_rw [hin]
  rw [inner_eq k r' hB2 hIW hT hk A s μ₁ hμ₁ x c hc]
  gcongr
  have hG0 := (yx_ga hB2 hIW k r' hk x).1
  have hD : 0 < Dx k r' x := Real.sqrt_pos.mpr hG0
  exact Qf_le k r' A C0 hC0 _ μ₁ hμ₁ _ (mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hD.ne'))

end chain

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem chcond_of {p : ℕ} (ν e : Fin (p + 1) → ℝ) (he : ∀ l, 0 < e l)
    (h0 : ν 0 = e 0 + 2 * ∑ l ∈ Finset.univ.erase 0, e l) (hl : ∀ l, l ≠ 0 → ν l = -e l) : CHCond p ν := by
  have key : ∀ S : Finset (Fin (p + 1)), 0 ∉ S → ∑ j ∈ S, ν j = -∑ j ∈ S, e j := fun S hS => by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => hl j (fun h => hS (h ▸ hj))
  have hsplit : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Iic l, ν j = ν 0 + ∑ j ∈ (Finset.Iic l).erase 0, ν j :=
    fun l => (Finset.add_sum_erase _ _ (Finset.mem_Iic.mpr (by simp))).symm
  have hE : ∀ l : Fin (p + 1), ∑ j ∈ (Finset.Iic l).erase 0, e j ≤ ∑ j ∈ Finset.univ.erase 0, e j :=
    fun l => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset_erase _ (Finset.subset_univ _))
      (fun j _ _ => (he j).le)
  have hX : ∀ l : Fin (p + 1), 0 ≤ ∑ j ∈ (Finset.Iic l).erase 0, e j :=
    fun l => Finset.sum_nonneg fun j _ => (he j).le
  have h0S : ∀ l : Fin (p + 1), (0 : Fin (p + 1)) ∉ (Finset.Iic l).erase 0 := fun l => by simp
  refine ⟨fun l => ?_, fun l _ => ?_⟩
  · rw [hsplit, key _ (h0S l), h0]
    linarith [hE l, hX l, he 0]
  · have hIoi : (0 : Fin (p + 1)) ∉ Finset.Ioi l := by simp
    have hpart : ∑ j ∈ Finset.univ.erase 0, e j =
        ∑ j ∈ (Finset.Iic l).erase 0, e j + ∑ j ∈ Finset.Ioi l, e j := by
      rw [← Finset.sum_union]
      · congr 1
        ext j
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi, Finset.mem_univ, and_true]
        constructor
        · intro h
          by_cases hjl : j ≤ l
          · exact Or.inl ⟨h, hjl⟩
          · exact Or.inr (not_le.mp hjl)
        · rintro (⟨h, _⟩ | h)
          · exact h
          · exact (lt_of_le_of_lt (by simp : (0 : Fin (p + 1)) ≤ l) h).ne'
      · rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi] at hj1 hj2
        exact absurd hj1.2 (not_le.mpr hj2)
    rw [hsplit, key _ (h0S l), key _ hIoi, h0]
    linarith [hpart, hX l, he 0]

section fin
variable (k r' : ℕ)

theorem sum_sc (f : Fin (1 + r' + 1) → ℝ) : ∑ l, f l = f 0 + ∑ l : Fin (r' + 1), f (sc r' l) := by
  rw [Fin.sum_univ_succ]
  have e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i) := fun i => Fin.ext (by simp [sc])
  simp only [e]
  rw [Fin.sum_congr' (fun j => f (sc r' j)) (by omega : 1 + r' = r' + 1)]

theorem sum_erase0 (f : Fin (1 + r' + 1) → ℝ) : ∑ l ∈ Finset.univ.erase 0, f l = ∑ l : Fin (r' + 1), f (sc r' l) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_sc]; ring

theorem sum_levelExponents_shifted : ∑ l : Fin (r' + 1), s0 k (1 + r') (sc r' l) = 2 * (r' : ℝ) + k := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin r', s0 k (1 + r') (sc r' (Fin.castSucc i)) = 2 := fun i => by
    have := i.isLt
    exact if_pos (by simp only [sc, Fin.val_castSucc]; omega)
  have h2 : s0 k (1 + r') (sc r' (Fin.last r')) = k := by
    exact if_neg (by simp only [sc, Fin.val_last]; omega)
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem levelExponent_first_eq_two : s0 k (1 + r') 0 = 2 := by
  exact if_pos (by simp)

theorem exponentShift_eq_levelExponent (hk : 1 ≤ k) (l : Fin (1 + r' + 1)) : s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
  unfold s0N s0
  split_ifs
  · rfl
  · rw [Nat.cast_sub hk]; push_cast; ring

theorem sc_ne_zero (l : Fin (r' + 1)) : sc r' l ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp [sc] at this

theorem th_ident (s : Fin (1 + r' + 1) → ℝ) (aw : ℝ) (x : HPar k r') (hG0 : 0 < Ga k (1 + r') 0 (Yx k r' x))
    (hGl : ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x)) :
    ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) =
      ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^
        (-(if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) / 2)) := by
  have hPsi : 0 ≤ Psi k r' s x := Finset.prod_nonneg fun l _ => Real.rpow_nonneg (div_nonneg (hGl _) hG0.le) _
  rw [← ENNReal.ofReal_mul hPsi, ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hGl l) _)]
  congr 1
  rw [Fin.prod_univ_succ, if_pos rfl]
  have e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i) := fun i => Fin.ext (by simp [sc])
  simp only [e, sc_ne_zero, if_false]
  rw [Fin.prod_congr' (fun j => Ga k (1 + r') (sc r' j) (Yx k r' x) ^ (-s (sc r' j) / 2)) (by omega : 1 + r' = r' + 1)]
  unfold Psi Dx
  have hP : ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)
      = (∏ l : Fin (r' + 1), Ga k (1 + r') (sc r' l) (Yx k r' x) ^ (-s (sc r' l) / 2)) *
        Ga k (1 + r') 0 (Yx k r' x) ^ (∑ l : Fin (r' + 1), s (sc r' l) / 2) := by
    rw [Real.rpow_sum_of_pos hG0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Real.div_rpow (hGl _) hG0.le, div_eq_mul_inv, ← Real.rpow_neg hG0.le]
    congr 2; ring
  have hD : Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) ^ (-(aw + 2)) = Ga k (1 + r') 0 (Yx k r' x) ^ (-(aw + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hG0.le]; congr 1; ring
  rw [hP, hD, mul_assoc, ← Real.rpow_add hG0, mul_comm]
  congr 2
  rw [← Finset.sum_div]; ring

end fin

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section
noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aStep_fin (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k)
    (hA' : AAt k r') : AAt k (1 + r') := by
  intro s hs μG hμG A hA
  obtain ⟨hOSI, -, hHCL, hHI, -, -, hHGE, hHA, hGNL, hHC, hHCLM⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨μ₁, hμ₁⟩ := hHGE k r'
  have : IsFiniteMeasureOnCompacts μ₁ := ⟨fun K hK => hμ₁.finite_compact K hK⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg r'
  have hs1 : SAdm k r' (fun l => s (sc r' l)) := fun l => by
    have h := hs (sc r' l)
    have e : s0 k (1 + r') (sc r' l) = s0 k r' l := by
      unfold s0 sc; split_ifs <;> first | rfl | (exfalso; simp_all; omega)
    rw [e] at h; exact h
  have hAB : AB k r' ≤ A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := by
    unfold AB at hA ⊢; push_cast at hA ⊢; nlinarith
  have hdA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A := by
    unfold AB at hA; push_cast at hA ⊢; nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hr0]
  have hJ1 := hA' _ hs1 μ₁ hμ₁ _ hAB
  obtain ⟨J1, hJ1d⟩ : ∃ J1, J1 = JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l)) := ⟨_, rfl⟩
  rw [← hJ1d] at hJ1
  obtain ⟨C0, hC0⟩ := eInt_bound hGNL hHA hHC hHCL hHCLM k r' hk A hdA
  obtain ⟨C, -, hOS⟩ := hOSI k r' μG μ₁ hμG hμ₁
  have hfm : Measurable (fun g : Mt k (1 + r') =>
      ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k (1 + r') s (Matrix.of g)) :=
    ((by unfold gN; fun_prop : Continuous fun g : Mt k (1 + r') => gN (Matrix.of g)).measurable.pow_const
      _).ennreal_ofReal.mul (FsE_meas k (1 + r') s)
  unfold JInt
  rw [hOS _ hfm]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  obtain ⟨aw, haw⟩ : ∃ aw : ℝ, aw = 2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l := ⟨_, rfl⟩
  have hc0 : ∀ᵐ c : ℂ, c ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton 0
  have hYc : Continuous fun x : HPar k r' => Yx k r' x := by
    have e : (fun x : HPar k r' => Yx k r' x) = fun x a => heis0 k r' (-x.1, -x.2) *ᵥ phi2 k r' a := by
      funext x a; unfold Yx; rw [hHI]
    rw [e]; have := heisenberg_map_continuous k r'; fun_prop
  have hGac : ∀ l, Continuous fun x : HPar k r' => Ga k (1 + r') l (Yx k r' x) := by
    intro l; unfold Ga; fun_prop
  have hDm : Measurable fun x => Dx k r' x := by unfold Dx; exact (hGac 0).sqrt.measurable
  have hPm : Measurable fun x => Psi k r' s x := by
    unfold Psi
    exact Finset.measurable_prod _ fun l _ => ((hGac _).measurable.div (hGac 0).measurable).pow_const _
  have hFm : Measurable (Function.uncurry fun (c : ℂ) (x : HPar k r') => ENNReal.ofReal (‖c‖ ^ aw) *
      (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ))))) :=
    ((measurable_norm.comp measurable_fst).pow_const _).ennreal_ofReal.mul
      ((hPm.comp measurable_snd).ennreal_ofReal.mul ((mw_meas k r').comp
        (measurable_fst.mul (Complex.measurable_ofReal.comp (hDm.comp measurable_snd)))).ennreal_ofReal)
  have hS0 : ∑ l, s0 k (1 + r') l = 2 * (1 + (r' : ℝ)) + k := by
    rw [sum_sc, levelExponent_first_eq_two, sum_levelExponents_shifted]; ring
  have hlt : ∑ l, s l < ∑ l, s0 k (1 + r') l :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun l _ => by linarith [(hs l).1]
  have hge : ∑ l, (s0 k (1 + r') l - 1 / 10) ≤ ∑ l, s l := Finset.sum_le_sum fun l _ => by linarith [(hs l).2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hge
  push_cast at hge
  have hK1 : ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) < ⊤ := by
    have h := cInt_fin (2 * r' + k + 1) (∑ l, s l) (by linarith) (by push_cast; linarith)
    have e : (4 * r' + 2 * k + 3 : ℕ) = 2 * (2 * r' + k + 1) + 1 := by ring
    unfold mw; rw [e, haw]; exact h
  have hCHc : CHCond (1 + r') fun l =>
      (if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) - s0N (1 + r') (k - 1) l := by
    refine chcond_of _ (fun l => s0 k (1 + r') l - s l) (fun l => by linarith [(hs l).1]) ?_ ?_
    · simp only [if_pos rfl]
      rw [sum_erase0, exponentShift_eq_levelExponent k r' hk, levelExponent_first_eq_two, Finset.sum_sub_distrib, sum_levelExponents_shifted, haw, sum_sc r' s]
      push_cast; ring
    · intro l hl0
      simp only [if_neg hl0]
      rw [exponentShift_eq_levelExponent k r' hk]; ring
  have hTh : ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (th_fin hB2 hF hCH k r' hk _ hCHc)
    have hg := yx_ga hB2 hIW k r' hk x
    exact th_ident k r' s aw x hg.1 hg.2
  calc ∫⁻ c, ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
        ∫⁻ p : (HPar k r' × HPar k r') × Mt k r',
          ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
            FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μ₁)
      ≤ ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (|C0| * mw k r' (c * (Dx k r' x : ℂ))) * J1) := by
        refine lintegral_mono_ae (hc0.mono fun c hc => ?_)
        have h := inner_c_le k r' hB2 hIW hT hk A C0 hC0 s μ₁ hμ₁ c hc
        rw [← hJ1d, ← haw] at h; exact h
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) *
          (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ)))) := by
        rw [← lintegral_lintegral_swap hFm.aemeasurable,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun c => ?_
        rw [← lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ aw)) _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_mul (abs_nonneg _)]; ring
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) *
            ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) := by
        congr 1
        refine lintegral_congr fun x => ?_
        have hD : 0 < Dx k r' x := Real.sqrt_pos.mpr (yx_ga hB2 hIW k r' hk x).1
        rw [← scale_c k r' aw _ hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun c => ?_; ring
    _ = ENNReal.ofReal |C0| * J1 * ((∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) *
          ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2)))) := by
        congr 1
        rw [← lintegral_const_mul' _ _ hK1.ne]
        refine lintegral_congr fun x => ?_; ring
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ1) (ENNReal.mul_lt_top hK1 hTh)

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem aStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) : AStepSucc := by
  intro k r r' hr hk hA
  subst hr
  exact StepA.aStep_fin hB2 hIW hT hF hCH k r' hk hA

end ReciprocityTheory.ChartRestriction.DS.Xi
end
