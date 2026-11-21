import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConstPinOfStd

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyCV

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace

section Weight

variable {r : ℕ}

theorem prod_Icc_range (x : ℕ → ℝ) : ∀ n : ℕ,
    ∏ l ∈ Finset.Icc 1 n, ∏ i ∈ Finset.range l, x i = ∏ i ∈ Finset.range n, x i ^ (n - i)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.prod_Icc_succ_top (by omega), prod_Icc_range x n, Finset.prod_range_succ (fun i => x i ^ (n + 1 - i)),
      Finset.prod_range_succ x n]
    have h : ∏ i ∈ Finset.range n, x i ^ (n + 1 - i) =
        (∏ i ∈ Finset.range n, x i ^ (n - i)) * ∏ i ∈ Finset.range n, x i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    rw [h, show n + 1 - n = 1 by omega, pow_one]
    ring

def xN (c : Fin (r + 1) → ℂ) (i : ℕ) : ℝ := if h : i < r + 1 then ‖c ⟨i, h⟩‖ else 1

theorem norm_dl_diag (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    ‖Formalism.L2.SG.RealObj.Dl (Matrix.diagonal c) l‖ = ∏ i ∈ Finset.range l, xN c i := by
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal, norm_prod,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (i : ℕ) < r + 1 := lt_of_lt_of_le i.2 hl
  simp only [xN, dif_pos hi, Function.comp_apply]
  rfl

theorem xN_last (c : Fin (r + 1) → ℂ) : xN c r = ‖c (Fin.last r)‖ := by
  unfold xN
  rw [dif_pos (by omega)]
  rfl

theorem gv_diag (T T' : ℝ) (c : Fin (r + 1) → ℂ) :
    Gv T T' (Matrix.diagonal c) = (∏ i ∈ Finset.range r, xN c i) ^ 2 * (‖c (Fin.last r)‖ ^ 2 - T * T') := by
  unfold Gv
  rw [norm_dl_diag c (r + 1) le_rfl, norm_dl_diag c r (by omega), Finset.prod_range_succ, xN_last]
  ring

theorem jac_diag (c : Fin (r + 1) → ℂ) :
    JacV (Matrix.diagonal c) = ∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i) := by
  unfold JacV modC
  rw [← prod_Icc_range (fun i => xN c i ^ 4) r]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Finset.mem_Icc] at hl
  rw [norm_dl_diag c l (by omega), Finset.prod_pow]
  ring

def phiC (lam : Fin r → ℝ) (c : Fin (r + 1) → ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((lam a : ℝ) : ℂ) * c ⟨a.val, by have := a.2; omega⟩, c ⟨r, by omega⟩)

theorem bc_prod (k : ℕ) (hk : 1 ≤ k) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) (c : Fin (r + 1) → ℂ) :
    ∏ a : Fin r, ‖(phiC lam c).1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) =
      (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) *
        (((∏ i ∈ Finset.range r, xN c i) ^ 2) ^ (k - 1) * ∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i)) := by
  have h1 : ∀ a : Fin r, ‖(phiC lam c).1 a‖ = lam a * xN c a := fun a => by
    have ha : (a : ℕ) < r + 1 := by have := a.2; omega
    simp only [phiC, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hlam a), xN, dif_pos ha]
  simp only [h1, mul_pow, Finset.prod_mul_distrib]
  congr 1
  show ∏ a : Fin r, (fun i : ℕ => xN c i ^ (2 * (2 * (r - i) + k + 1 - 2))) a = _
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => xN c i ^ (2 * (2 * (r - i) + k + 1 - 2))) r,
    ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  omega

end Weight

section AE

instance sf2 : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
  have h : ((2 : ℝ≥0∞) • (volume : Measure ℂ)) = ((2 : ℝ≥0) • (volume : Measure ℂ)) := by
    rw [ENNReal.smul_def]; simp
  rw [h]; infer_instance

variable {r : ℕ}

def GoodC (T T' : ℝ) : Set (Fin (r + 1) → ℂ) :=
  {c | (∀ l, c l ≠ 0) ∧ 0 < Gv T T' (Matrix.diagonal c)}

def dcC : Measure (Fin (r + 1) → ℂ) := Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def kapC (k : ℕ) (lam : Fin r → ℝ) : ℝ := ∏ a : Fin r, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)))⁻¹

theorem kapC_nonneg (k : ℕ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) : 0 ≤ kapC k lam := Finset.prod_nonneg fun a _ => inv_nonneg.2 (pow_nonneg (hlam a).le _)

theorem null_set (T T' : ℝ) :
    dcC (r := r) {c | ¬ ((∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T')} = 0 := by
  have hsub : {c : Fin (r + 1) → ℂ | ¬ ((∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T')} ⊆
      (⋃ i, Function.eval i ⁻¹' ({0} : Set ℂ)) ∪
        Function.eval (Fin.last r) ⁻¹' {z : ℂ | ‖z‖ ^ 2 = T * T'} := by
    intro c hc
    simp only [Set.mem_setOf_eq, not_and_or, not_forall, not_not] at hc
    rcases hc with ⟨i, hi⟩ | h
    · exact Or.inl (Set.mem_iUnion.2 ⟨i, hi⟩)
    · exact Or.inr h
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun i => ?_) ?_)
  · refine Measure.pi_eval_preimage_null _ ?_
    rw [Measure.smul_apply, measure_singleton, smul_zero]
  · refine Measure.pi_eval_preimage_null _ ?_
    rw [Measure.smul_apply]
    have hs : {z : ℂ | ‖z‖ ^ 2 = T * T'} ⊆ Metric.sphere 0 (Real.sqrt (T * T')) := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz
      simp only [mem_sphere_iff_norm, sub_zero]
      rw [← hz, Real.sqrt_sq (norm_nonneg z)]
    rw [measure_mono_null hs (Measure.addHaar_sphere volume 0 _), smul_zero]

theorem ae_weight (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a)
    (F : (Fin r → ℂ) × ℂ → ℝ) :
    ∀ᵐ c ∂(dcC (r := r)), (GoodC T T').indicator
        (fun c => ENNReal.ofReal (Gv T T' (Matrix.diagonal c) ^ (k - 1) * JacV (Matrix.diagonal c) * F (phiC lam c))) c =
      ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' (phiC lam c) * F (phiC lam c))) := by
  have hmem : {c : Fin (r + 1) → ℂ | (∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T'} ∈ ae (dcC (r := r)) := by
    rw [mem_ae_iff]
    have := null_set (r := r) T T'
    simpa [Set.compl_setOf] using this
  filter_upwards [hmem] with c hc
  obtain ⟨hc0, hcT⟩ := hc
  have hP : 0 < ∏ i ∈ Finset.range r, xN c i := by
    refine Finset.prod_pos fun i hi => ?_
    rw [Finset.mem_range] at hi
    unfold xN
    rw [dif_pos (by omega)]
    exact norm_pos_iff.2 (hc0 _)
  have hP2 : 0 < (∏ i ∈ Finset.range r, xN c i) ^ 2 := by positivity
  have hns : Complex.normSq (phiC lam c).2 = ‖c (Fin.last r)‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; rfl
  have hlamne : (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (hlam a).ne'
  have hkap : kapC k lam * (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) = 1 := by
    unfold kapC
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => inv_mul_cancel₀ (pow_ne_zero _ (hlam a).ne')
  by_cases hg : c ∈ GoodC T T'
  · rw [Set.indicator_of_mem hg]
    have hG := hg.2
    rw [gv_diag] at hG
    have hpos : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' := pos_of_mul_pos_right hG hP2.le
    unfold Formalism.QuantumDeterminants.bcWeight
    rw [if_pos (by rw [hns]; linarith), bc_prod k hk lam hlam c, hns, gv_diag, jac_diag]
    congr 1
    rw [mul_pow]
    calc ((∏ i ∈ Finset.range r, xN c i) ^ 2) ^ (k - 1) * (‖c (Fin.last r)‖ ^ 2 - T * T') ^ (k - 1) *
          (∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i)) * F (phiC lam c)
        = (kapC k lam * (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)))) *
          (((∏ i ∈ Finset.range r, xN c i) ^ 2) ^ (k - 1) * (‖c (Fin.last r)‖ ^ 2 - T * T') ^ (k - 1) *
          (∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i)) * F (phiC lam c)) := by rw [hkap, one_mul]
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hg]
    have hng : ¬ 0 < Gv T T' (Matrix.diagonal c) := fun h => hg ⟨hc0, h⟩
    rw [gv_diag] at hng
    have hle : ‖c (Fin.last r)‖ ^ 2 - T * T' ≤ 0 := by
      by_contra h
      exact hng (mul_pos hP2 (lt_of_not_ge h))
    have hlt : ‖c (Fin.last r)‖ ^ 2 < T * T' := lt_of_le_of_ne (by linarith) hcT
    unfold Formalism.QuantumDeterminants.bcWeight
    rw [if_neg (by rw [hns]; linarith)]
    simp

end AE

section Map

variable {r : ℕ}

def muS (lam : Fin r → ℝ) (i : Fin (r + 1)) : ℝ := if h : (i : ℕ) < r then lam ⟨i, h⟩ else 1

theorem muS_pos (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) (i : Fin (r + 1)) : 0 < muS lam i := by
  unfold muS
  split_ifs
  · exact hlam _
  · exact one_pos

def e1 (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) : (Fin (r + 1) → ℂ) ≃ᵐ (Fin (r + 1) → ℂ) :=
  MeasurableEquiv.piCongrRight fun i => MeasurableEquiv.smul₀ (muS lam i) (muS_pos lam hlam i).ne'

def e2 : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℂ) (Fin.last r)).trans MeasurableEquiv.prodComm

def PhiE (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
  (e1 lam hlam).trans e2

theorem phiE_apply (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) (c : Fin (r + 1) → ℂ) :
    PhiE lam hlam c = phiC lam c := by
  refine Prod.ext ?_ ?_
  · funext a
    simp only [PhiE, e1, e2, MeasurableEquiv.coe_trans, Function.comp_apply]
    simp
    show (muS lam (Fin.castSucc a) • c (Fin.castSucc a) : ℂ) = _
    have h : muS lam (Fin.castSucc a) = lam a := by simp [muS]
    rw [h, Complex.real_smul]
    rfl
  · simp only [PhiE, e1, e2, MeasurableEquiv.coe_trans, Function.comp_apply]
    simp
    show (muS lam (Fin.last r) • c (Fin.last r) : ℂ) = _
    have h : muS lam (Fin.last r) = 1 := by simp [muS]
    rw [h, one_smul]
    rfl

def cN (lam : Fin r → ℝ) (i : Fin (r + 1)) : ℝ≥0 := Real.toNNReal (2 * ((muS lam i) ^ 2)⁻¹)

theorem map_scaled_coordinates_pi (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) :
    (dcC (r := r)).map (e1 lam hlam) = Measure.pi fun i => (cN lam i) • (volume : Measure ℂ) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (e1 lam hlam).measurable (MeasurableSet.univ_pi hs)]
  have hpre : (e1 lam hlam) ⁻¹' Set.univ.pi s = Set.univ.pi fun i => (fun z : ℂ => muS lam i • z) ⁻¹' s i := by
    ext c
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  rw [hpre, dcC, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hμ := muS_pos lam hlam i
  rw [Measure.smul_apply, Measure.smul_apply, ← Measure.map_apply (measurable_const_smul (muS lam i)) (hs i),
    Measure.map_addHaar_smul volume hμ.ne', Measure.smul_apply, Complex.finrank_real_complex]
  rw [abs_of_nonneg (by positivity)]
  simp only [smul_eq_mul, cN]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [show ((Real.toNNReal (2 * (muS lam i ^ 2)⁻¹) : ℝ≥0∞)) = ENNReal.ofReal (2 * (muS lam i ^ 2)⁻¹) from rfl,
    ENNReal.ofReal_mul (by norm_num)]
  simp

theorem pi_smul_const (c : Fin (r + 1) → ℝ≥0) :
    Measure.pi (fun i => c i • (volume : Measure ℂ)) =
      (∏ i, (c i : ℝ≥0∞)) • Measure.pi (fun _ : Fin (r + 1) => (volume : Measure ℂ)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem map_coordinate_change_volume : (Measure.pi fun _ : Fin (r + 1) => (volume : Measure ℂ)).map (e2 (r := r)) = volume := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r)
  have h2 := Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
    (ν := Measure.pi fun _ : Fin r => (volume : Measure ℂ))
  exact (h2.comp h1).map_eq

theorem map_phiE (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) :
    (dcC (r := r)).map (PhiE lam hlam) = (∏ i, (cN lam i : ℝ≥0∞)) • (volume : Measure ((Fin r → ℂ) × ℂ)) := by
  rw [PhiE, MeasurableEquiv.coe_trans, ← Measure.map_map (e2 (r := r)).measurable (e1 lam hlam).measurable, map_scaled_coordinates_pi,
    pi_smul_const, Measure.map_smul, map_coordinate_change_volume]

theorem const_eq (k : ℕ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) :
    (∏ i : Fin (r + 1), 2 * ((muS lam i) ^ 2)⁻¹) * kapC k lam =
      2 ^ (r + 1) * ∏ a : Fin r, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ := by
  rw [Fin.prod_univ_castSucc]
  have hc : ∀ a : Fin r, muS lam (Fin.castSucc a) = lam a := fun a => by simp [muS]
  have hl : muS lam (Fin.last r) = 1 := by simp [muS]
  simp only [hc, hl, one_pow, inv_one, mul_one]
  unfold kapC
  have hM : ∀ a : Fin r, (lam a ^ 2)⁻¹ * (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)))⁻¹ =
      (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ := fun a => by
    rw [← mul_inv, ← pow_add]
    congr 2
    unfold Formalism.QuantumDeterminants.Mdim
    have := a.2
    omega
  rw [← Finset.prod_congr rfl (fun a _ => hM a), Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_succ]
  ring

theorem goodC_meas (T T' : ℝ) : MeasurableSet (GoodC (r := r) T T') := by
  have h1 : MeasurableSet {cv : Fin (r + 1) → ℂ | ∀ l, cv l ≠ 0} := by
    have : {cv : Fin (r + 1) → ℂ | ∀ l, cv l ≠ 0} = ⋂ l, {cv | cv l ≠ 0} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun l => (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_pi_apply l)
  have hc : Continuous (fun cv : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal cv)) := by
    have hd : Continuous (fun cv : Fin (r + 1) → ℂ => Matrix.diagonal cv) := continuous_id.matrix_diagonal
    have hD : ∀ l, Continuous (fun cv : Fin (r + 1) → ℂ => Formalism.L2.SG.RealObj.Dl (Matrix.diagonal cv) l) :=
      fun l => (Formalism.L2.SG.RealObj.InfCut.dl_cont l).comp hd
    unfold Gv
    exact ((hD _).norm.pow 2).sub (continuous_const.mul ((hD _).norm.pow 2))
  exact h1.inter (measurableSet_lt measurable_const hc.measurable)

end Map

theorem cv_core {r : ℕ} (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a)
    (F : (Fin r → ℂ) × ℂ → ℝ) :
    ∫⁻ c in GoodC (r := r) T T',
        ENNReal.ofReal (Gv T T' (Matrix.diagonal c) ^ (k - 1) * JacV (Matrix.diagonal c) * F (phiC lam c))
        ∂(dcC (r := r)) =
      ENNReal.ofReal (2 ^ (r + 1) * ∏ a : Fin r, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹) *
        ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q) := by
  rw [← lintegral_indicator (goodC_meas T T'), lintegral_congr_ae (ae_weight k hk T T' lam hlam F)]
  have hfun : (fun c => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' (phiC lam c) * F (phiC lam c)))) =
      fun c => (fun q => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q))) (PhiE lam hlam c) := by
    funext c
    rw [phiE_apply]
  rw [hfun, ← lintegral_map_equiv (fun q => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q)))
    (PhiE lam hlam), map_phiE, lintegral_smul_measure]
  simp_rw [ENNReal.ofReal_mul (kapC_nonneg k lam hlam)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [show (∏ i, (cN lam i : ℝ≥0∞)) = ENNReal.ofReal (∏ i, 2 * ((muS lam i) ^ 2)⁻¹) from by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by have := muS_pos lam hlam i; positivity)]; rfl,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => by have := muS_pos lam hlam i; positivity),
    const_eq k lam hlam]

theorem cv_inst {D : D7} (u u' : D.what₂.Word) (m : ℕ) (hm : m = D.R.rS) (lam : Fin m → ℝ) (hlam : ∀ a, 0 < lam a)
    (F : (Fin m → ℂ) × ℂ → ℝ) :
    ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv *
        F ((fun a => ((lam a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩, cv ⟨D.R.rS, by omega⟩))) ∂(dcV (D := D)) =
      ENNReal.ofReal (2 ^ (m + 1) * ∏ a : Fin m, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k m a - 1)))⁻¹) *
        ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight D.R.k m (Tw (D := D) u) (Tw (D := D) u') q * F q) := by
  subst hm
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have h := cv_core D.R.k hk1 (Tw (D := D) u) (Tw (D := D) u') lam hlam F
  exact h

theorem changeVar_of_pos {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u')
    (hr : P.S.G.r = D.R.rS) (hg : 0 < P.S.g) : ChangeVar P hr := by
  intro hk hT v F _
  have hg' : (0 : ℝ) < P.S.g := by exact_mod_cast hg
  have hlam : ∀ a, 0 < lamA P a := fun a => by unfold lamA; positivity
  rw [(hT v).1, (hT v).2]
  unfold K0
  rw [hk]
  exact cv_inst u u' P.S.G.r hr (lamA P) hlam F

end Formalism.L2.SG.Pf.Carrier.EnergyCV
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyNF

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lintegral_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)] (F : ι → E → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    ∫⁻ x, ∏ i, F i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, F i y ∂(μ i) := by
  have hm : Measurable (fun x : ι → E => ∏ i, F i (x i)) :=
    Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)
  have key : ∀ s : Finset ι, ∀ x : ι → E,
      (∫⋯∫⁻_s, (fun x : ι → E => ∏ i, F i (x i)) ∂μ) x = (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ i ∈ sᶜ, F i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hm hi]
      simp_rw [ih]
      have hsplit : ∀ y, ∏ j ∈ sᶜ, F j (Function.update x i y j) = F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j) := by
        intro y
        have hic : i ∈ sᶜ := Finset.mem_compl.2 hi
        rw [← Finset.mul_prod_erase _ _ hic, Function.update_self, Finset.compl_insert]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp_rw [hsplit]
      have h2 : ∀ y, (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * (F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j)) =
          ((∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ j ∈ (insert i s)ᶜ, F j (x j)) * F i y := fun y => by ring
      simp_rw [h2]
      rw [lintegral_const_mul _ (hF i), Finset.prod_insert hi]
      ring
  rw [lintegral_eq_lmarginal_univ (fun _ => Classical.arbitrary E), key, Finset.compl_univ, Finset.prod_empty,
    mul_one]

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

theorem intCe_eq_prodE (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) :
    intCe X u u' 1 = ∏ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) := by
  obtain ⟨hpos, hLc⟩ := hL
  have hG : MeasurableSet (Good X u u') := by
    rw [good_eq_pi]; exact MeasurableSet.univ_pi fun _ => goodV_meas u u'
  have hpt : ∀ c ∈ Good X u u', ENNReal.ofReal (Formalism.L2.SG.RealObj.wt X u u' c * hilbertSchmidtSqGram X u u' 1 c) =
      ∏ v, ENNReal.ofReal (wtV u u' (c v) * L v (c v)) := by
    intro c hc
    have hcv : ∀ v, c v ∈ GoodV u u' := fun v => hc v
    rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ =>
      mul_nonneg (wtV_nonneg u u' (hcv v)) ((hpos v).2 _))]
    congr 1
    have hO : hilbertSchmidtSqGram X u u' 1 c = ∏ v, L v (c v) := by
      unfold hilbertSchmidtSqGram
      rw [hilbert_schmidt_tensor_product_factor]
      exact Finset.prod_congr rfl fun v _ => hLc c hc v
    rw [hO, Finset.prod_mul_distrib]
    rfl
  unfold intCe
  rw [setLIntegral_congr_fun hG hpt, good_eq_pi]
  have h2s : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
    have h : ((2 : ℝ≥0∞) • (volume : Measure ℂ)) = ((2 : NNReal) • (volume : Measure ℂ)) := by
      rw [ENNReal.smul_def]; simp
    rw [h]; infer_instance
  unfold dcInf
  rw [Measure.restrict_pi_pi]
  have hdc : SigmaFinite ((dcV (D := D)).restrict (GoodV u u')) := by unfold dcV; infer_instance
  rw [show (Measure.pi fun _ : Fin (D.R.rS + 1) => (2 : ℝ≥0∞) • (volume : Measure ℂ)) = dcV (D := D) from rfl]
  exact lintegral_pi_prod _ (fun v cv => ENNReal.ofReal (wtV u u' cv * L v cv))
    (fun v => ENNReal.measurable_ofReal.comp ((wtV_cont u u').measurable.mul (hpos v).1))

def PlaceEnergyE (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
    ENNReal.ofReal (K v) * Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))

theorem energyNorm_of_stepsE (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (K : InfinitePlace X.B.I.F → ℝ)
    (h1 : LocRep X u u' L) (h2 : PlaceEnergyE P L K) (h3 : ConstPin P ψ K) :
    P.EnergyNorm (IntNX X u u' ψ) := by
  set n : InfinitePlace X.B.I.F → ℝ :=
    fun v => (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal with hn
  have hC : IntC X u u' 1 = (∏ v, K v) * ∏ v, n v := by
    unfold IntC
    rw [intCe_eq_prodE L h1]
    rw [Finset.prod_congr rfl (fun v _ => h2 v)]
    rw [ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h3.1 v)]
  unfold Parts.EnergyNorm IntNX
  rw [hC]
  have hre : (∏ j, (Formalism.FourierDecayAlt.B.normSq (P.T j).base (P.f j)).toReal / P.Gam0) =
      (∏ v, n v) * (P.Gam0 ^ P.S.f)⁻¹ := by
    rw [← Equiv.prod_comp P.τ.symm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      ← Fintype.card_congr P.τ, Fintype.card_fin, div_eq_mul_inv]
  rw [hre, ← h3.2]
  ring

theorem placeEnergyE_of_steps (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (hPN : PlaceNorm P hr L) (hCV : ChangeVar P hr) :
    PlaceEnergyE P L (fun _ => EnergyConst.Kexp P) := by
  intro v
  rw [setLIntegral_congr_fun (goodV_meas u u') (fun cv hcv => by rw [hPN v cv hcv])]
  rw [hCV hk hT v (fun q => ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base q))‖ ^ 2) (fun q => by positivity)]
  rw [← Formalism.L2.SG.Pf.Carrier.EnergyKM.kMatch_holds P hg hrd hr hk hg0 hk1]
  rfl

theorem energyNorm_bookY_of_placeNormG_of_changeVar (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) (hCV : ChangeVar P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN := by
  obtain ⟨L, hL⟩ := Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.locRep_holds X u u'
  rw [intN_massDataY]
  exact energyNorm_of_stepsE P ψ L (fun _ => EnergyConst.Kexp P) hL
    (placeEnergyE_of_steps P hr hk hT hg hrd hg0 hk1 L (placeNorm_of_G P hr hPN L hL) hCV)
    (EnergyConst.constPin_of P ψ hC hMS hf)

theorem energy_norm_bound_second_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energyNorm_bookY_of_placeNormG_of_changeVar hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC hMS hPN
    (Formalism.L2.SG.Pf.Carrier.EnergyCV.changeVar_of_pos P hr hg0)

theorem energy_norm_bound_third_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : Formalism.L2.SG.LocVol.IsStdChar ψ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst2.LemmaMSStd X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energy_norm_bound_second_form hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC (hMS hψ hstd hC) hPN

end Formalism.L2.SG.Pf.Carrier.EnergyNF
end
end
