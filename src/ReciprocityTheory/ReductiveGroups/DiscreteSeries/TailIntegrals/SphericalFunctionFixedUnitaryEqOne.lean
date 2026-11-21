import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
import Mathlib

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def iW (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 0

def iK (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 (Fin.last k)

def Pk (k : ℕ) : Mat k 0 := Matrix.single (iK k) (iK k) 1

def U0 (k : ℕ) : Set (Mat k 0) := UWset k 0 (bvec (iK k))

lemma iW_ne_iK {k : ℕ} (hk : 1 ≤ k) : iW k ≠ iK k := by
  intro h
  have := congrArg Fin.val h
  simp [iW, iK, wI] at this
  omega

lemma hpk0 (k : ℕ) : Hpk k 0 = 1 - 2 • Pk k := by
  ext i j
  have hi := i.isLt
  have hle : i.val ≤ k := by omega
  by_cases hij : i = j
  · subst hij
    by_cases hik : i.val = k
    · simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik]
      norm_num
    · have hik' : k ≠ i.val := fun h => hik h.symm
      simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik, hik', hle]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hv]
    omega

lemma Pk_mul_self (k : ℕ) : Pk k * Pk k = Pk k := by
  simp [Pk]

lemma Pk_conjTranspose (k : ℕ) : (Pk k)ᴴ = Pk k := by
  simp [Pk]

lemma one_sub_mul_Pk (k : ℕ) : (1 - 2 • Pk k) * Pk k = -Pk k := by
  rw [sub_mul, one_mul, smul_mul_assoc, Pk_mul_self, two_smul]
  abel

lemma fixedUnitary_projection_identities {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) :
    hᴴ * h = 1 ∧ h * Pk k = Pk k ∧ hᴴ * Pk k = Pk k ∧ Pk k * h = Pk k := by
  obtain ⟨hU, -, hv⟩ := hh
  have hU' : hᴴ * Hpk k 0 * h = Hpk k 0 := hU
  have hcol : ∀ i, h i (iK k) = if i = iK k then 1 else 0 := by
    intro i
    have := congrFun hv i
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using this
  have hP : h * Pk k = Pk k := by
    ext i j
    by_cases hj : iK k = j
    · subst hj
      by_cases hi : i = iK k
      · subst hi
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol]
      · have hi' : iK k ≠ i := fun e => hi e.symm
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol, hi, hi']
    · simp [Pk, Matrix.mul_apply, Matrix.single_apply, hj]
  have hsP : hᴴ * Pk k = Pk k := by
    have e1 : hᴴ * Hpk k 0 * h * Pk k = Hpk k 0 * Pk k := by rw [hU']
    rw [Matrix.mul_assoc, hP, hpk0, Matrix.mul_assoc, one_sub_mul_Pk, Matrix.mul_neg] at e1
    exact neg_inj.mp e1
  have hPh : Pk k * h = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, hP, hsP, hPh⟩
  have e2 := hU'
  rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    hsP, hPh] at e2
  exact sub_left_inj.mp e2

lemma mem_fixedUnitary_of_unitary_fixes {k : ℕ} {R : Mat k 0} (hu : Rᴴ * R = 1) (hP : R * Pk k = Pk k) : R ∈ U0 k := by
  have hsP : Rᴴ * Pk k = Pk k := by
    calc Rᴴ * Pk k = Rᴴ * (R * Pk k) := by rw [hP]
      _ = Pk k := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hPR : Pk k * R = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, fun a => a.elim0, ?_⟩
  · show Rᴴ * Hpk k 0 * R = Hpk k 0
    rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu, Matrix.mul_smul, Matrix.smul_mul,
      hsP, hPR]
  · ext i
    have := congrFun (congrFun hP i) (iK k)
    simpa [Pk, Matrix.mul_apply, Matrix.single_apply, Matrix.mulVec, dotProduct, bvec,
      Pi.single_apply, eq_comm] using this

lemma fixedUnitary_conjTranspose_mem {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) : hᴴ ∈ U0 k := by
  obtain ⟨hu, -, hsP, -⟩ := fixedUnitary_projection_identities hh
  refine mem_fixedUnitary_of_unitary_fixes ?_ hsP
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hu

lemma fixedUnitary_apply_fixedIndex_left {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (j : Fin (2 * 0 + k + 1)) :
    h (iK k) j = if j = iK k then 1 else 0 := by
  have := congrFun (congrFun (fixedUnitary_projection_identities hh).2.2.2 (iK k)) j
  simpa [Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm] using this

lemma fixedUnitary_apply_fixedIndex_right {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (i : Fin (2 * 0 + k + 1)) :
    h i (iK k) = if i = iK k then 1 else 0 := by
  have := congrFun (congrFun (fixedUnitary_projection_identities hh).2.1 i) (iK k)
  simpa [Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm] using this

lemma fixedUnitary_mulVec_fixedIndex {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (y : Fin (2 * 0 + k + 1) → ℂ) :
    (h *ᵥ y) (iK k) = y (iK k) := by
  simp [Matrix.mulVec, dotProduct, fixedUnitary_apply_fixedIndex_left hh]

lemma fixedUnitary_preserves_normSq {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (y : Fin (2 * 0 + k + 1) → ℂ) :
    star (h *ᵥ y) ⬝ᵥ (h *ᵥ y) = star y ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (fixedUnitary_projection_identities hh).1,
    Matrix.one_mulVec]

lemma exists_fixedUnitary_sending_basis {k : ℕ} (hk : 1 ≤ k) (u : Fin (2 * 0 + k + 1) → ℂ) (hu0 : u (iK k) = 0)
    (hu1 : star u ⬝ᵥ u = 1) : ∃ R ∈ U0 k, R *ᵥ bvec (iW k) = u := by
  classical
  have hWK : iW k ≠ iK k := iW_ne_iK hk

  obtain ⟨μ, hμ1, hμr⟩ : ∃ μ : ℂ, star μ * μ = 1 ∧
      star (star μ * u (iW k)) = star μ * u (iW k) := by
    by_cases h0 : u (iW k) = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn : ((‖u (iW k)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hc : star (u (iW k)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      have hs : star ((‖u (iW k)‖ : ℝ) : ℂ) = ((‖u (iW k)‖ : ℝ) : ℂ) := Complex.conj_ofReal _
      have hval : star (u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ) := by
        rw [star_div₀, hs, div_mul_eq_mul_div, hc]
        field_simp
      refine ⟨u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ), ?_, ?_⟩
      · rw [star_div₀, hs, div_mul_div_comm, hc]
        field_simp
      · rw [hval, hs]

  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * 0 + k + 1) → ℂ, d = Function.update (fun _ => 1) (iW k) μ :=
    ⟨_, rfl⟩
  have hdW : d (iW k) = μ := by simp [hd]
  have hdo : ∀ i, i ≠ iW k → d i = 1 := by
    intro i hi
    simp [hd, hi]
  have hDu : (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases hi : i = iW k
    · subst hi
      simp [hdW]
      exact hμ1
    · simp [hdo i hi]
  have hDP : Matrix.diagonal d * Pk k = Pk k := by
    ext i j
    by_cases hi : i = iK k
    · subst hi
      simp [Matrix.diagonal_mul, hdo _ (Ne.symm hWK)]
    · simp [Matrix.diagonal_mul, Pk, Matrix.single_apply, Ne.symm hi]
  have hDe : Matrix.diagonal d *ᵥ bvec (iW k) = μ • bvec (iW k) := by
    ext i
    by_cases hi : i = iW k
    · subst hi
      simp [Matrix.mulVec_diagonal, hdW, bvec]
    · simp [Matrix.mulVec_diagonal, bvec, Pi.single_apply, hi]
  obtain ⟨x, hx⟩ : ∃ x : Fin (2 * 0 + k + 1) → ℂ, x = μ • bvec (iW k) := ⟨_, rfl⟩
  by_cases hxu : x = u
  · refine ⟨Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes hDu hDP, ?_⟩
    rw [hDe, ← hx, hxu]

  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * 0 + k + 1) → ℂ, w = x - u := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact sub_ne_zero.mpr hxu
  have hn : star w ⬝ᵥ w ≠ 0 := fun h => hw0 (dotProduct_star_self_eq_zero.mp h)
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = 2 * (star w ⬝ᵥ w)⁻¹ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Mat k 0, W = Matrix.vecMulVec w (star w) := ⟨_, rfl⟩
  have hWv : ∀ v, W *ᵥ v = (star w ⬝ᵥ v) • w := by
    intro v
    ext i
    simp only [hW, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hWW : W * W = (star w ⬝ᵥ w) • W := by
    ext i j
    simp only [hW, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hWh : Wᴴ = W := by
    ext i j
    simp [hW, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hnr : star (star w ⬝ᵥ w) = star w ⬝ᵥ w := by
    simp [dotProduct, star_sum, mul_comm]
  have hsr : star s = s := by
    rw [hs, star_mul', star_inv₀, hnr, star_ofNat]
  obtain ⟨Hh, hHh⟩ : ∃ Hh : Mat k 0, Hh = 1 - s • W := ⟨_, rfl⟩
  have hHhs : Hhᴴ = Hh := by
    rw [hHh, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hsr, hWh]
  have hsn : s * (s * (star w ⬝ᵥ w)) = 2 * s := by
    rw [hs]
    field_simp
  have hHH : Hh * Hh = 1 := by
    rw [hHh]
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm,
      hWW, smul_smul, smul_sub]
    have h2 : (s * (s * (star w ⬝ᵥ w))) • W = s • W + s • W := by
      rw [hsn, ← add_smul, ← two_mul]
    rw [h2]
    abel
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = star μ * u (iW k) := ⟨_, rfl⟩
  have hxv : ∀ v, star x ⬝ᵥ v = star μ * v (iW k) := by
    intro v
    rw [hx]
    simp only [dotProduct]
    rw [Finset.sum_eq_single (iW k)]
    · simp [bvec]
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hvx : ∀ v, star v ⬝ᵥ x = star (v (iW k)) * μ := by
    intro v
    rw [hx]
    simp only [dotProduct]
    rw [Finset.sum_eq_single (iW k)]
    · simp [bvec]
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hxx : star x ⬝ᵥ x = 1 := by
    rw [hvx, hx]
    simpa [bvec, mul_comm] using hμ1
  have hxu' : star x ⬝ᵥ u = α := by rw [hxv, hα]
  have hux : star u ⬝ᵥ x = α := by
    have h1 := hμr
    rw [star_mul, star_star] at h1
    rw [hvx, h1, ← hα]
  have hwx : star w ⬝ᵥ x = 1 - α := by
    rw [hw, star_sub, sub_dotProduct, hxx, hux]
  have hwn : star w ⬝ᵥ w = 2 - 2 * α := by
    rw [hw, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hxx, hxu', hux, hu1]
    ring
  have hn' : (2 - 2 * α : ℂ) ≠ 0 := hwn ▸ hn
  have hs1 : s * (1 - α) = 1 := by
    rw [hs, hwn]
    have : (1 - α : ℂ) ≠ 0 := by
      intro h
      apply hn'
      linear_combination 2 * h
    field_simp
  refine ⟨Hh * Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes ?_ ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hHhs, Matrix.mul_assoc, ← Matrix.mul_assoc Hh Hh, hHH,
      Matrix.one_mul, hDu]
  · have hwk : w (iK k) = 0 := by
      rw [hw, hx]
      simp [hu0, bvec, Pi.single_apply, Ne.symm hWK]
    have hWP : W * Pk k = 0 := by
      ext i j
      simp [hW, Pk, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.single_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      split_ifs with hl
      · rw [← hl.1, hwk]
        simp
      · rfl
    rw [Matrix.mul_assoc, hDP, hHh, sub_mul, Matrix.one_mul, smul_mul_assoc, hWP, smul_zero,
      sub_zero]
  · have hsm : (s • W) *ᵥ x = s • (W *ᵥ x) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [← Matrix.mulVec_mulVec, hDe, ← hx, hHh, Matrix.sub_mulVec, Matrix.one_mulVec, hsm, hWv, hwx, smul_smul, hs1, one_smul, hw, sub_sub_cancel]

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

def one1 : ℝ → ℝ := Set.indicator (Set.Icc (-1) 1) 1

def pw1 (β : ℝ) : ℝ → ℝ := Set.indicator (Set.Icc (-1) 1) (fun t => |t| ^ (-β))

lemma integrable_unitIndicator : Integrable one1 := by
  unfold one1
  first
  | exact (continuous_one.integrableOn_Icc).integrable_indicator measurableSet_Icc
  | exact (Continuous.integrableOn_Icc continuous_const).integrable_indicator measurableSet_Icc
  | exact (integrableOn_const.2 (Or.inr measure_Icc_lt_top)).integrable_indicator measurableSet_Icc

lemma integrable_powIndicator {β : ℝ} (hβ : β < 1) : Integrable (pw1 β) := by
  have hr : (-1 : ℝ) < -β := by linarith
  have h0 : IntervalIntegrable (fun t : ℝ => t ^ (-β)) volume 0 1 := by
    first
    | exact intervalIntegral.intervalIntegrable_rpow' hr
    | exact intervalIntegrable_rpow' hr
  have hpos : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h0 ⊢
    refine h0.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [abs_of_pos ht.1]
  have hneg : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa [abs_neg] using hpos.symm
  have hall : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 1 := hneg.trans hpos
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at hall
  unfold pw1
  exact hall.integrable_indicator measurableSet_Icc

lemma integrable_reim {p q : ℝ → ℝ} (hp : Integrable p) (hq : Integrable q) :
    Integrable (fun z : ℂ => p z.re * q z.im) := by
  have h : Integrable (fun z : ℝ × ℝ => p z.1 * q z.2) (volume.prod volume) := by
    first
    | exact Integrable.mul_prod hp hq
    | exact Integrable.prod_mul hp hq
    | exact Integrable.prod_smul hp hq
  have e := Complex.volume_preserving_equiv_real_prod
  have h2 := (e.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).2 h
  first
  | exact h2
  | (convert h2 using 1; funext z; rfl)
  | (convert h2 using 1; funext z; simp [Complex.measurableEquivRealProd])

lemma volume_axes : volume {z : ℂ | z.im = 0 ∨ z.re = 0} = 0 := by
  have e := Complex.volume_preserving_equiv_real_prod
  have h1 : volume {z : ℂ | z.im = 0} = 0 := by
    have hs : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ {0}) := by
      first
      | (ext z; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)
      | (ext z; simp [Complex.measurableEquivRealProd])
    rw [hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h2 : volume {z : ℂ | z.re = 0} = 0 := by
    have hs : {z : ℂ | z.re = 0} = Complex.measurableEquivRealProd ⁻¹' ({0} ×ˢ Set.univ) := by
      first
      | (ext z; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
      | (ext z; simp [Complex.measurableEquivRealProd])
    rw [hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hu : {z : ℂ | z.im = 0 ∨ z.re = 0} = {z : ℂ | z.im = 0} ∪ {z : ℂ | z.re = 0} := rfl
  rw [hu]
  exact measure_union_null h1 h2

lemma volume_bad (ι : Type*) [Fintype ι] :
    volume {x : ι → ℂ | ∃ i, (x i).im = 0 ∨ (x i).re = 0} = 0 := by
  have hs : {x : ι → ℂ | ∃ i, (x i).im = 0 ∨ (x i).re = 0} =
      ⋃ i, (fun x : ι → ℂ => x i) ⁻¹' {z : ℂ | z.im = 0 ∨ z.re = 0} := by
    ext x; simp
  rw [hs]
  refine measure_iUnion_null fun i => ?_
  rw [volume_pi]
  first
  | exact Measure.pi_eval_preimage_null _ volume_axes
  | exact Measure.pi_eval_preimage_null volume_axes
  | exact Measure.pi_eval_preimage_null (μ := fun _ => volume) volume_axes

lemma mp_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι ℂ) (hu : h.conjTranspose * h = 1) :
    MeasurePreserving (fun y : ι → ℂ => h.mulVec y) volume volume := by
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' h).restrictScalars ℝ
  have hfun : (fun y : ι → ℂ => h.mulVec y) = ⇑L := by
    funext y
    first
    | rfl
    | simp [L, Matrix.toLin'_apply]
  have hdetC : Complex.normSq h.det = 1 := by
    have h1 := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
    have h2 : ((Complex.normSq h.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      first
      | exact h1
      | (rw [starRingEnd_apply]; exact h1)
      | simpa using h1
    exact_mod_cast h2
  have hdet : LinearMap.det L = 1 := by
    first
    | (rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])
    | (show LinearMap.det ((Matrix.toLin' h).restrictScalars ℝ) = 1
       rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])
  have hmeas : Measurable (fun y : ι → ℂ => h.mulVec y) := by
    rw [hfun]
    exact L.continuous_of_finiteDimensional.measurable
  refine ⟨hmeas, ?_⟩
  rw [hfun]
  first
  | (rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]; simp)
  | (rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [hdet]; norm_num), hdet]; simp)

section Shell

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tW (q : ι) (x : ι → ℂ) : ℝ := Real.sqrt (∑ i, if i = q then 0 else Complex.normSq (x i))

def Bset (q : ι) : Set (ι → ℂ) := {x | 1 / 2 ≤ tW q x ∧ tW q x ≤ 1 ∧ ‖x q‖ ≤ 1}

def PsiF (p q : ι) (s : ℝ) (x : ι → ℂ) : ℝ≥0∞ := (‖1 - star (x p) / (tW q x : ℂ)‖₊ : ℝ≥0∞) ^ (-s)

def eF (p q i : ι) (z : ℂ) : ℝ := if i = q then 1 else if i = p then |z.im| else |z.re| * |z.im|

def gF (p q : ι) (β : ℝ) (i : ι) (z : ℂ) : ℝ :=
  if i = q then one1 z.re * one1 z.im else if i = p then one1 z.re * pw1 β z.im else pw1 β z.re * pw1 β z.im

lemma sum_split (q : ι) (f : ι → ℝ) : ∑ i, f i = f q + ∑ i, (if i = q then 0 else f i) := by
  have hs : ∀ i, f i = (if i = q then f i else 0) + (if i = q then 0 else f i) := by
    intro i
    split_ifs <;> simp
  calc ∑ i, f i = ∑ i, ((if i = q then f i else 0) + (if i = q then 0 else f i)) :=
        Finset.sum_congr rfl (fun i _ => hs i)
    _ = f q + ∑ i, (if i = q then 0 else f i) := by
        first
        | (rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp)
        | simp [Finset.sum_add_distrib]

lemma normSq_le_tW (q : ι) (x : ι → ℂ) (i : ι) (hi : i ≠ q) : Complex.normSq (x i) ≤ tW q x ^ 2 := by
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j)) := by
    intro j _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg hnn)]
  have h1 := Finset.single_le_sum hnn (Finset.mem_univ i)
  simpa [hi] using h1

lemma unitIndicator_eq {y : ℝ} (hy : |y| ≤ 1) : one1 y = 1 := by
  unfold one1
  rw [Set.indicator_of_mem (show y ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hy)]
  try rfl

lemma powIndicator_eq {β y : ℝ} (hy : |y| ≤ 1) : pw1 β y = |y| ^ (-β) := by
  unfold pw1
  rw [Set.indicator_of_mem (show y ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hy)]
  try rfl

lemma gF_integrable (p q : ι) {β : ℝ} (hβ : β < 1) (i : ι) : Integrable (gF p q β i) := by
  by_cases h1 : i = q
  · have he : gF p q β i = fun z => one1 z.re * one1 z.im := by
      funext z
      simp [gF, h1]
    rw [he]
    exact integrable_reim integrable_unitIndicator integrable_unitIndicator
  · by_cases h2 : i = p
    · have h1' : p ≠ q := by
        rw [← h2]
        exact h1
      have he : gF p q β i = fun z => one1 z.re * pw1 β z.im := by
        funext z
        simp [gF, h2, h1']
      rw [he]
      exact integrable_reim integrable_unitIndicator (integrable_powIndicator hβ)
    · have he : gF p q β i = fun z => pw1 β z.re * pw1 β z.im := by
        funext z
        simp [gF, h1, h2]
      rw [he]
      exact integrable_reim (integrable_powIndicator hβ) (integrable_powIndicator hβ)

end Shell

section Shell2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma psi_le {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) (hk1 : 1 ≤ k) {s : ℝ}
    (hs : 0 ≤ s) {x : ι → ℂ} (hx : x ∈ Bset q) (hg : ∀ i, (x i).im ≠ 0 ∧ (x i).re ≠ 0) :
    PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) := by
  classical
  obtain ⟨ht1, ht2, hxq⟩ := hx
  have htpos : 0 < tW q x := by linarith

  have hcoord : ∀ z : ℂ, Complex.normSq z ≤ 1 → |z.re| ≤ 1 ∧ |z.im| ≤ 1 := by
    intro z hz
    rw [Complex.normSq_apply] at hz
    constructor
    · nlinarith [sq_abs z.re, abs_nonneg z.re, mul_self_nonneg z.im]
    · nlinarith [sq_abs z.im, abs_nonneg z.im, mul_self_nonneg z.re]
  have hnsq : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := by
    intro z
    first
    | exact Complex.normSq_eq_norm_sq z
    | (rw [Complex.sq_norm])
    | (rw [Complex.normSq_eq_abs, Complex.norm_eq_abs])
  have hsmall : ∀ i, i ≠ q → Complex.normSq (x i) ≤ 1 := by
    intro i hi
    have h1 := normSq_le_tW q x i hi
    nlinarith [htpos]
  have hqsmall : Complex.normSq (x q) ≤ 1 := by
    rw [hnsq]
    nlinarith [norm_nonneg (x q)]

  have hnnj : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j)) := by
    intro j _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  have htsq : tW q x ^ 2 = ∑ j, (if j = q then 0 else Complex.normSq (x j)) := by
    unfold tW
    rw [Real.sq_sqrt (Finset.sum_nonneg hnnj)]
  have him : (1 - star (x p) / (tW q x : ℂ)).im = (x p).im / tW q x := by
    simp [Complex.div_ofReal_im]
    try ring
  have hA : |(x p).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
    have h1 : |(1 - star (x p) / (tW q x : ℂ)).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
      first
      | exact Complex.abs_im_le_norm _
      | exact Complex.abs_im_le_abs _
    rw [him, abs_div, abs_of_pos htpos] at h1
    have h2 : |(x p).im| ≤ |(x p).im| / tW q x := by
      first
      | (rw [le_div_iff₀ htpos]; nlinarith [abs_nonneg (x p).im])
      | (rw [le_div_iff htpos]; nlinarith [abs_nonneg (x p).im])
    linarith
  have hB : ∀ i, i ≠ p → i ≠ q → |(x i).re| * |(x i).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
    intro i hip hiq
    have hsum : Complex.normSq (x p) + Complex.normSq (x i) ≤ tW q x ^ 2 := by
      rw [htsq]
      have hsub : ∑ j ∈ ({p, i} : Finset ι), (if j = q then 0 else Complex.normSq (x j)) ≤
          ∑ j, (if j = q then 0 else Complex.normSq (x j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => hnnj j (Finset.mem_univ j))
      rw [Finset.sum_pair (Ne.symm hip), if_neg hpq, if_neg hiq] at hsub
      exact hsub
    have hw : ‖star (x p) / (tW q x : ℂ)‖ = ‖x p‖ / tW q x := by
      rw [norm_div, norm_star]
      first
      | (rw [Complex.norm_real, Real.norm_of_nonneg htpos.le])
      | (simp [abs_of_pos htpos]; done)
      | (simp [Complex.abs_of_nonneg htpos.le]; done)
    have htri : ‖(1 : ℂ)‖ - ‖star (x p) / (tW q x : ℂ)‖ ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, hw] at htri
    rw [hnsq (x p)] at hsum
    have hre2 : 2 * (|(x i).re| * |(x i).im|) ≤ Complex.normSq (x i) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_abs (x i).re, sq_abs (x i).im, sq_nonneg (|(x i).re| - |(x i).im|)]
    have hr0 := norm_nonneg (x p)
    have hni := Complex.normSq_nonneg (x i)
    have hrt : ‖x p‖ ≤ tW q x := by nlinarith
    have hm : |(x i).re| * |(x i).im| ≤ tW q x - ‖x p‖ := by
      nlinarith [mul_nonneg (sub_nonneg.2 hrt) (by linarith : (0 : ℝ) ≤ 2 - tW q x - ‖x p‖)]
    have hd : ‖x p‖ / tW q x ≤ 1 - tW q x + ‖x p‖ := by
      first
      | (rw [div_le_iff₀ htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])
      | (rw [div_le_iff htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])
    linarith
  have hpim : 0 < |(x p).im| := abs_pos.2 (hg p).1
  have hu : 0 < ‖1 - star (x p) / (tW q x : ℂ)‖ := lt_of_lt_of_le hpim hA
  have hP : PsiF p q s x = ENNReal.ofReal (‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-s)) := by
    unfold PsiF
    rw [← ENNReal.ofReal_rpow_of_pos hu]
    congr 1
    first
    | exact (ofReal_norm_eq_coe_nnnorm _).symm
    | (rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm])
    | exact (enorm_eq_nnnorm _).symm.trans (ofReal_norm_eq_enorm _).symm
    | (simp; rfl)
  rw [hP]
  apply ENNReal.ofReal_le_ofReal
  have hk0 : (0 : ℝ) < k := by
    have hk0' : 0 < k := by omega
    exact_mod_cast hk0'
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hβ0 : 0 ≤ s / k := div_nonneg hs hk0.le
  have key : ∀ a : ℝ, 0 < a → a ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ →
      ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ a ^ (-(s / k)) := by
    intro a ha hau
    first
    | exact Real.rpow_le_rpow_of_nonpos ha hau (by linarith)
    | (rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]
       exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))
    | (rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]
       exact inv_le_inv_of_le (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))
  have hfac : ∀ i, i ≠ q → ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ gF p q (s / k) i (x i) := by
    intro i hiq
    obtain ⟨hr1, hi1⟩ := hcoord (x i) (hsmall i hiq)
    by_cases hip : i = p
    · rw [hip] at hr1 hi1 ⊢
      have he : gF p q (s / k) p (x p) = |(x p).im| ^ (-(s / k)) := by
        rw [show gF p q (s / k) p (x p) = one1 (x p).re * pw1 (s / k) (x p).im by simp [gF, hpq],
          unitIndicator_eq hr1, powIndicator_eq hi1, one_mul]
      rw [he]
      exact key _ hpim hA
    · have he : gF p q (s / k) i (x i) = (|(x i).re| * |(x i).im|) ^ (-(s / k)) := by
        rw [show gF p q (s / k) i (x i) = pw1 (s / k) (x i).re * pw1 (s / k) (x i).im by
          simp [gF, hiq, hip], powIndicator_eq hr1, powIndicator_eq hi1, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      rw [he]
      exact key _ (mul_pos (abs_pos.2 (hg i).2) (abs_pos.2 (hg i).1)) (hB i hip hiq)
  have hq1 : gF p q (s / k) q (x q) = 1 := by
    obtain ⟨hr1, hi1⟩ := hcoord (x q) hqsmall
    rw [show gF p q (s / k) q (x q) = one1 (x q).re * one1 (x q).im by simp [gF], unitIndicator_eq hr1, unitIndicator_eq hi1, one_mul]
  have hsplit := Finset.mul_prod_erase Finset.univ (fun i => gF p q (s / k) i (x i)) (Finset.mem_univ q)
  try simp only at hsplit
  rw [← hsplit, hq1, one_mul]
  have hcard : (Finset.univ.erase q).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, hk]
    simp
  calc ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-s)
      = ∏ i ∈ Finset.univ.erase q, ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) := by
        rw [Finset.prod_const, hcard, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
        congr 1
        first
        | (rw [neg_mul, div_mul_cancel₀ _ hkne])
        | (rw [neg_mul, div_mul_cancel₀ hkne])
        | (field_simp; done)
        | (field_simp; ring)
    _ ≤ ∏ i ∈ Finset.univ.erase q, gF p q (s / k) i (x i) := by
        apply Finset.prod_le_prod
        · intro i _
          exact Real.rpow_nonneg hu.le _
        · intro i hi
          exact hfac i (Finset.ne_of_mem_erase hi)

lemma measurableSet_Bset (q : ι) : MeasurableSet (Bset q) := by
  have hc : Continuous (tW q) := by
    unfold tW
    refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
    by_cases h : i = q
    · simp only [h, if_true]
      exact continuous_const
    · simp only [h, if_false]
      exact Complex.continuous_normSq.comp (continuous_apply i)
  have hn : Continuous (fun x : ι → ℂ => ‖x q‖) := continuous_norm.comp (continuous_apply q)
  unfold Bset
  exact (measurableSet_le measurable_const hc.measurable).inter
    ((measurableSet_le hc.measurable measurable_const).inter
      (measurableSet_le hn.measurable measurable_const))

lemma integrable_gprod (p q : ι) {β : ℝ} (hβ : β < 1) :
    Integrable (fun x : ι → ℂ => ∏ i, gF p q β i (x i)) := by
  first
  | exact Integrable.fintype_prod (f := fun i => gF p q β i) (fun i => gF_integrable p q hβ i)
  | exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i)
  | (rw [volume_pi]; exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i))
  | exact Integrable.fintype_prod_dep (fun i => gF_integrable p q hβ i)

lemma ae_good : ∀ᵐ x : ι → ℂ, ∀ i, (x i).im ≠ 0 ∧ (x i).re ≠ 0 := by
  rw [ae_iff]
  have h := volume_bad ι
  convert h using 2
  ext x
  simp only [Set.mem_setOf_eq, not_forall, not_and_or, ne_eq, not_not]

lemma lint_Bset_lt_top {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) (hk1 : 1 ≤ k)
    {s : ℝ} (hs : 0 ≤ s) (hsk : s < k) : ∫⁻ x in Bset q, PsiF p q s x < ∞ := by
  have hk0 : (0 : ℝ) < k := by
    have hk0' : 0 < k := by omega
    exact_mod_cast hk0'
  have hβ : s / k < 1 := by
    rw [div_lt_one hk0]
    exact hsk
  have hG := integrable_gprod p q hβ
  have hae : ∀ᵐ x : ι → ℂ, x ∈ Bset q →
      PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) := by
    filter_upwards [ae_good] with x hg hx
    exact psi_le hpq hk hk1 hs hx hg
  have h1 : ∫⁻ x in Bset q, PsiF p q s x ≤
      ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) :=
    lintegral_mono_ae ((ae_restrict_iff' (measurableSet_Bset q)).2 hae)
  have h2 : ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) ≤
      ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) :=
    setLIntegral_le_lintegral _ _
  have h3 : ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) < ∞ := by
    first
    | exact Integrable.lintegral_lt_top hG
    | exact HasFiniteIntegral.lintegral_lt_top hG.2
  exact lt_of_le_of_lt (h1.trans h2) h3

end Shell2

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dot_star_self (y : ι → ℂ) : star y ⬝ᵥ y = ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma tW_sq (q : ι) (x : ι → ℂ) :
    tW q x ^ 2 = ∑ i, Complex.normSq (x i) - Complex.normSq (x q) := by
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg])]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne',
    Finset.sum_erase_eq_sub (Finset.mem_univ q)]

lemma tW_mulVec {h : Matrix ι ι ℂ} (hu : hᴴ * h = 1) {q : ι}
    (hrow : ∀ j, h q j = if j = q then 1 else 0) (x : ι → ℂ) :
    tW q (h *ᵥ x) = tW q x ∧ (h *ᵥ x) q = x q := by
  have hq : (h *ᵥ x) q = x q := by
    simp [mulVec, dotProduct, hrow]
  refine ⟨?_, hq⟩
  have hn : ∑ i, Complex.normSq ((h *ᵥ x) i) = ∑ i, Complex.normSq (x i) := by
    have e : star (h *ᵥ x) ⬝ᵥ (h *ᵥ x) = star x ⬝ᵥ x := by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hu, vecMul_one]
    rw [dot_star_self, dot_star_self] at e
    exact_mod_cast e
  have h1 := tW_sq q (h *ᵥ x)
  have h2 := tW_sq q x
  rw [hn, hq, ← h2] at h1
  have n1 : 0 ≤ tW q (h *ᵥ x) := Real.sqrt_nonneg _
  have n2 : 0 ≤ tW q x := Real.sqrt_nonneg _
  exact (pow_left_inj₀ n1 n2 two_ne_zero).mp h1

lemma volume_Bset_ne_zero {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) :
    volume (Bset q) ≠ 0 := by
  have hc : Continuous (tW q) := by
    unfold tW
    refine Continuous.sqrt (continuous_finset_sum _ fun i _ => ?_)
    by_cases hi : i = q
    · simp only [hi, ↓reduceIte]; exact continuous_const
    · simp only [hi, ↓reduceIte]; exact Complex.continuous_normSq.comp (continuous_apply i)
  have hU : IsOpen {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} :=
    (isOpen_lt continuous_const hc).inter
      ((isOpen_lt hc continuous_const).inter
        (isOpen_lt (continuous_norm.comp (continuous_apply q)) continuous_const))
  let x0 : ι → ℂ := fun i => if i = p then ((3 / 4 : ℝ) : ℂ) else 0
  have hs : (∑ i, if i = q then (0 : ℝ) else Complex.normSq (x0 i)) = 9 / 16 := by
    rw [Finset.sum_eq_single p]
    · simp only [hpq, ↓reduceIte, x0, Complex.normSq_ofReal]; norm_num
    · intro b _ hb; simp [x0, hb]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  have ht : tW q x0 = 3 / 4 := by
    unfold tW
    rw [hs, show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx0 : x0 ∈ {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} := by
    refine ⟨by rw [ht]; norm_num, by rw [ht]; norm_num, ?_⟩
    simp [x0, Ne.symm hpq]
  have hsub : {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} ⊆ Bset q :=
    fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  intro h0
  exact (hU.measure_pos volume ⟨x0, hx0⟩).ne' (measure_mono_null hsub h0)

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

lemma enn_nnnorm (z : ℂ) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  first
  | exact (ofReal_norm_eq_enorm z).symm
  | (rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (norm_nonneg _)]; rfl)
  | simp

lemma ofReal_rpow_neg_anti {a b s : ℝ} (hs : 0 ≤ s) (hab : a ≤ b) :
    ENNReal.ofReal b ^ (-s) ≤ ENNReal.ofReal a ^ (-s) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hab) hs)

lemma continuous_tW {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι) : Continuous (tW q) := by
  show Continuous fun x : ι → ℂ => Real.sqrt (∑ i, if i = q then 0 else Complex.normSq (x i))
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ =>
    continuous_if_const _ (fun _ => continuous_const)
      (fun _ => Complex.continuous_normSq.comp (continuous_apply i)))

lemma measurable_PsiF {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι) (s : ℝ) :
    Measurable (PsiF p q s) := by
  have h1 : Measurable fun x : ι → ℂ => (1 : ℂ) - star (x p) / ((tW q x : ℝ) : ℂ) := by
    first
    | exact measurable_const.sub (((continuous_star.comp (continuous_apply p)).measurable).div
        (Complex.continuous_ofReal.comp (continuous_tW q)).measurable)
    | fun_prop
  show Measurable fun x : ι → ℂ => (‖(1 : ℂ) - star (x p) / ((tW q x : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ (-s)
  exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp h1)).pow_const _

variable {k : ℕ}

lemma inWb_iK (k : ℕ) : inWb k 0 (bvec (iK k)) := by
  intro i hi
  exfalso
  have := i.isLt
  rcases hi with h | h <;> omega

private lemma mulVec_bvec_eq_fun_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  first
  | simp [Matrix.mulVec, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, Matrix.dotProduct, bvec, Pi.single_apply]

private lemma star_bvec_dotProduct_eq_apply {n : ℕ} (j : Fin n) (w : Fin n → ℂ) : star (bvec j) ⬝ᵥ w = w j := by
  first
  | (rw [dotProduct, Finset.sum_eq_single j]
     · simp [bvec]
     · intro b _ hb; simp [bvec, Pi.single_apply, hb]
     · simp)
  | (rw [Matrix.dotProduct, Finset.sum_eq_single j]
     · simp [bvec]
     · intro b _ hb; simp [bvec, Pi.single_apply, hb]
     · simp)
  | simp [bvec]

lemma Tz_iK (k : ℕ) : 0 < Tz k 0 (bvec (iK k)) := by
  have hKK : Hpk k 0 (iK k) (iK k) = -1 := by
    simp [Hpk, iK, wI]
  have hh : herm (Hpk k 0) (bvec (iK k)) (bvec (iK k)) = -1 := by
    unfold herm
    rw [mulVec_bvec_eq_fun_apply, star_bvec_dotProduct_eq_apply]
    exact hKK
  unfold Tz
  rw [hh]
  norm_num

lemma ae_mem_fixedUnitary {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) : ∀ᵐ x ∂ν, (Matrix.of x : Mat k 0) ∈ U0 k := by
  first
  | exact ae_iff.2 hν.conc
  | (rw [ae_iff]; convert hν.conc using 1)

lemma haar_univ_lt_top (hCW : CompactW) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) : ν Set.univ < ∞ := by
  obtain ⟨U, hU⟩ : ∃ U : Set (Mt k 0), U = U0 k := ⟨_, rfl⟩
  have hK : IsCompact U := by rw [hU]; exact hCW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)
  have hc : ν Uᶜ = 0 := by rw [hU]; exact hν.conc
  have h1 : ν U < ∞ := hν.finite_compact _ hK
  have h2 := measure_union_le (μ := ν) U Uᶜ
  rw [Set.union_compl_self, hc, add_zero] at h2
  exact lt_of_le_of_lt h2 h1

lemma lint_lmul {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {a : Mat k 0} (ha : a ∈ U0 k)
    {F : Mt k 0 → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x, F (lmulM a x) ∂ν = ∫⁻ x, F x ∂ν := by
  have hm : Measurable (lmulM (k := k) (r := 0) a) := by
    have hc : Continuous (lmulM (k := k) (r := 0) a) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      show Continuous fun x : Mt k 0 => (a * Matrix.of x) i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact continuous_finset_sum _ fun l _ =>
        continuous_const.mul ((continuous_apply j).comp (continuous_apply l))
    exact hc.measurable
  rw [← lintegral_map hF hm, hν.left a ha]

private lemma iW_ne_iK' (hk : 1 ≤ k) : iW k ≠ iK k := by
  intro h
  have h' := congrArg Fin.val h
  simp [iW, iK, wI] at h'
  omega

lemma rot (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {φ : ℂ → ℝ≥0∞}
    (hφ : Measurable φ) (v : Fin (2 * 0 + k + 1) → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hvc : tW (iK k) v ^ 2 = Complex.normSq c) :
    ∫⁻ x, φ (((Matrix.of x)ᴴ *ᵥ v) (iW k)) ∂ν = ∫⁻ x, φ (star c * star (x (iW k) (iW k))) ∂ν := by
  have hWK := iW_ne_iK' hk
  have hcs : star c ≠ 0 := by
    intro h; apply hc; rw [← star_star c, h, star_zero]
  have hc2 : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hS0 : 0 ≤ ∑ i, (if i = iK k then (0:ℝ) else Complex.normSq (v i)) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg]
  have hS : (∑ i, if i = iK k then (0:ℝ) else Complex.normSq (v i)) = Complex.normSq c := by
    rw [← hvc]; unfold tW; rw [Real.sq_sqrt hS0]
  obtain ⟨u, hudef⟩ : ∃ u : Fin (2 * 0 + k + 1) → ℂ,
      u = fun i => if i = iK k then 0 else (star c)⁻¹ * v i := ⟨_, rfl⟩
  have hu0 : u (iK k) = 0 := by rw [hudef]; simp
  have hterm : ∀ i, star (u i) * u i =
      (((if i = iK k then (0:ℝ) else Complex.normSq (v i)) / Complex.normSq c : ℝ) : ℂ) := by
    intro i
    rw [show star (u i) * u i = ((Complex.normSq (u i) : ℝ) : ℂ) from
      (Complex.normSq_eq_conj_mul_self).symm]
    congr 1
    by_cases h : i = iK k
    · simp [hudef, h]
    · simp only [hudef, h, if_false]
      rw [Complex.normSq_mul, Complex.normSq_inv,
        show Complex.normSq (star c) = Complex.normSq c from Complex.normSq_conj c]
      ring
  have hu1 : star u ⬝ᵥ u = 1 := by
    first
    | simp only [dotProduct, Pi.star_apply, hterm]
    | simp only [Matrix.dotProduct, Pi.star_apply, hterm]
    rw [← Complex.ofReal_sum, ← Finset.sum_div, hS, div_self hc2, Complex.ofReal_one]
  obtain ⟨R, hR, hRe⟩ := exists_fixedUnitary_sending_basis hk u hu0 hu1
  have hRv : Rᴴ *ᵥ v = star c • bvec (iW k) + v (iK k) • bvec (iK k) := by
    have hv : v = star c • u + v (iK k) • bvec (iK k) := by
      funext i
      by_cases h : i = iK k
      · subst h; simp [hudef, bvec]
      · rw [hudef]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_neg h, bvec, Pi.single_apply,
          mul_zero, add_zero]
        rw [mul_inv_cancel_left₀ hcs]
    have h1 : Rᴴ *ᵥ u = bvec (iW k) := by
      rw [← hRe, Matrix.mulVec_mulVec, (fixedUnitary_projection_identities hR).1, Matrix.one_mulVec]
    have h2 : Rᴴ *ᵥ bvec (iK k) = bvec (iK k) := by
      rw [mulVec_bvec_eq_fun_apply]
      ext i
      rw [fixedUnitary_apply_fixedIndex_right (fixedUnitary_conjTranspose_mem hR) i]
      simp [bvec, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]
  have key : ∀ x : Mt k 0, (Matrix.of x : Mat k 0) ∈ U0 k →
      ((Matrix.of (lmulM R x))ᴴ *ᵥ v) (iW k) = star c * star (x (iW k) (iW k)) := by
    intro x hx
    have hx0 : x (iK k) (iW k) = 0 := by
      have h := fixedUnitary_apply_fixedIndex_left hx (iW k)
      rw [if_neg hWK] at h
      exact h
    show ((R * Matrix.of x)ᴴ *ᵥ v) (iW k) = _
    rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hRv, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_bvec_eq_fun_apply, mulVec_bvec_eq_fun_apply]
    simp [Matrix.conjTranspose_apply, hx0]
  have hcont : Continuous (fun x : Mt k 0 => ((Matrix.of x)ᴴ *ᵥ v) (iW k)) := by
    first
    | (simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
       exact continuous_finset_sum _ fun j _ =>
        (continuous_star.comp ((continuous_apply (iW k)).comp (continuous_apply j))).mul
          continuous_const)
    | (simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
       exact continuous_finset_sum _ fun j _ =>
        (continuous_star.comp ((continuous_apply (iW k)).comp (continuous_apply j))).mul
          continuous_const)
    | fun_prop
  have hmeasF : Measurable (fun x : Mt k 0 => φ (((Matrix.of x)ᴴ *ᵥ v) (iW k))) :=
    hφ.comp hcont.measurable
  calc ∫⁻ x, φ (((Matrix.of x)ᴴ *ᵥ v) (iW k)) ∂ν
      = ∫⁻ x, φ (((Matrix.of (lmulM R x))ᴴ *ᵥ v) (iW k)) ∂ν := (lint_lmul hν hR hmeasF).symm
    _ = ∫⁻ x, φ (star c * star (x (iW k) (iW k))) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_mem_fixedUnitary hν] with x hx
        rw [key x hx]

def C0 (k : ℕ) (s : ℝ) (ν : Measure (Mt k 0)) : ℝ≥0∞ :=
  ∫⁻ x, (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s) ∂ν

lemma norm_fixedUnitary_entry_le_one {h : Mat k 0} (hh : h ∈ U0 k) (i j : Fin (2 * 0 + k + 1)) : ‖h i j‖ ≤ 1 := by
  have h1 := congrFun (congrFun (fixedUnitary_projection_identities hh).1 j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
  have h2 : ∑ x, ((Complex.normSq (h x j) : ℝ) : ℂ) = 1 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  have h3 : ∑ x, Complex.normSq (h x j) = 1 := by exact_mod_cast h2
  have h4 : Complex.normSq (h i j) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun x => Complex.normSq (h x j))
      (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at h4
  nlinarith [norm_nonneg (h i j)]

private lemma norm_one_sub_le_two_mul_norm_one_sub_real_mul {w : ℂ} {ρ : ℝ} (hw : ‖w‖ ≤ 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ‖1 - w‖ ≤ 2 * ‖1 - (ρ : ℂ) * w‖ := by
  have hρw : ‖(ρ : ℂ) * w‖ = ρ * ‖w‖ := by
    rw [norm_mul]
    first
    | rw [Complex.norm_real, Real.norm_of_nonneg h0]
    | rw [Complex.norm_of_nonneg h0]
    | simp [abs_of_nonneg h0]
  have e : (1 : ℂ) - w = (1 - (ρ : ℂ) * w) + ((ρ : ℂ) - 1) * w := by ring
  have hA1 : ‖(1 : ℂ) - w‖ ≤ ‖1 - (ρ : ℂ) * w‖ + ‖((ρ : ℂ) - 1) * w‖ := by
    rw [e]; exact norm_add_le _ _
  have hA2 : ‖((ρ : ℂ) - 1) * w‖ = (1 - ρ) * ‖w‖ := by
    have e2 : (ρ : ℂ) - 1 = ((ρ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, e2]
    first
    | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
    | (simp only [Complex.norm_real, Real.norm_eq_abs]; rw [abs_of_nonpos (by linarith)]; ring)
    | (rw [Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_nonpos (by linarith)]; ring)
  have hA3 : 1 - ρ * ‖w‖ ≤ ‖1 - (ρ : ℂ) * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((ρ : ℂ) * w)
    rwa [norm_one, hρw] at this
  nlinarith [norm_nonneg w, norm_nonneg ((1 : ℂ) - (ρ : ℂ) * w), mul_nonneg h0 (sub_nonneg.2 hw)]

lemma bnd (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {s : ℝ} (hs : 0 ≤ s)
    {lam : ℝ} (hlam : 0 < lam) (v : Fin (2 * 0 + k + 1) → ℂ) (b : ℂ) (hb : b ≠ 0)
    (hvb : tW (iK k) v ^ 2 ≤ Complex.normSq b) :
    ∫⁻ x, ENNReal.ofReal (lam * ‖((Matrix.of x)ᴴ *ᵥ v) (iW k) + b‖) ^ (-s) ∂ν ≤
      ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * (C0 k s ν + ν Set.univ) := by
  have hWK := iW_ne_iK' hk
  have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hA : 0 ≤ lam * ‖b‖ / 2 := div_nonneg (mul_nonneg hlam.le hb0.le) (by norm_num)
  obtain ⟨t, ht⟩ : ∃ t, t = tW (iK k) v := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
  have htb : t ≤ ‖b‖ := by
    have h2 : t ^ 2 ≤ ‖b‖ ^ 2 := by rw [ht, ← Complex.normSq_eq_norm_sq]; exact hvb
    nlinarith
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (2 * 0 + k + 1))),
        0 ≤ (if i = iK k then (0:ℝ) else Complex.normSq (v i)) := fun i _ => by
      split_ifs <;> simp [Complex.normSq_nonneg]
    have hS : (∑ i, if i = iK k then (0:ℝ) else Complex.normSq (v i)) = 0 := by
      have h1 : tW (iK k) v = 0 := ht.symm.trans h0.symm
      unfold tW at h1
      have h2 := Real.sqrt_eq_zero'.mp h1
      linarith [Finset.sum_nonneg hnn]
    have hv0 : ∀ i, i ≠ iK k → v i = 0 := by
      intro i hi
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS i (Finset.mem_univ i)
      rw [if_neg hi] at h3
      exact Complex.normSq_eq_zero.mp h3
    calc ∫⁻ x, ENNReal.ofReal (lam * ‖((Matrix.of x)ᴴ *ᵥ v) (iW k) + b‖) ^ (-s) ∂ν
        = ∫⁻ _x, ENNReal.ofReal (lam * ‖b‖) ^ (-s) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [ae_mem_fixedUnitary hν] with x hx
          have hx0 : x (iK k) (iW k) = 0 := by
            have h := fixedUnitary_apply_fixedIndex_left hx (iW k)
            rw [if_neg hWK] at h
            exact h
          have hz : ((Matrix.of x)ᴴ *ᵥ v) (iW k) = 0 := by
            first
            | simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
            | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
            refine Finset.sum_eq_zero fun i _ => ?_
            by_cases hi : i = iK k
            · rw [hi, hx0, star_zero, zero_mul]
            · rw [hv0 i hi, mul_zero]
          rw [hz, zero_add]
      _ = ENNReal.ofReal (lam * ‖b‖) ^ (-s) * ν Set.univ := lintegral_const _
      _ ≤ ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * ν Set.univ :=
          mul_le_mul_of_nonneg_right (ofReal_rpow_neg_anti hs (by linarith)) (zero_le ..)
      _ ≤ _ := mul_le_mul_of_nonneg_left le_add_self (zero_le ..)
  · have hρ0' : 0 < t / ‖b‖ := div_pos hpos hb0
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = t / ‖b‖ := ⟨_, rfl⟩
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact hρ0'.le
    have hρne : ρ ≠ 0 := by rw [hρ]; exact hρ0'.ne'
    have hρ1 : ρ ≤ 1 := by rw [hρ]; exact (div_le_one hb0).mpr htb
    obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = star (-(b * (ρ : ℂ))) := ⟨_, rfl⟩
    have hsc : star c = -(b * (ρ : ℂ)) := by rw [hcdef, star_star]
    have hc : c ≠ 0 := by
      intro h
      have h' : star c = 0 := by rw [h, star_zero]
      rw [hsc, neg_eq_zero] at h'
      exact mul_ne_zero hb (Complex.ofReal_ne_zero.mpr hρne) h'
    have hvc : tW (iK k) v ^ 2 = Complex.normSq c := by
      have e : Complex.normSq c = Complex.normSq (star c) := (Complex.normSq_conj c).symm
      have hbne : ‖b‖ ≠ 0 := hb0.ne'
      rw [e, hsc, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_eq_norm_sq, ← ht, hρ]
      field_simp
      try ring
    have hφ : Measurable (fun z : ℂ => ENNReal.ofReal (lam * ‖z + b‖) ^ (-s)) := by
      first
      | exact (ENNReal.continuous_ofReal.comp
          (continuous_const.mul (continuous_id.add continuous_const).norm)).measurable.pow_const _
      | fun_prop
    have hrot := rot hk hν hφ v c hc hvc
    refine hrot.trans_le ?_
    have hmeasC : Measurable (fun x : Mt k 0 => (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s)) := by
      first
      | exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp (measurable_const.sub
          ((measurable_pi_apply (iW k)).comp (measurable_pi_apply (iW k)))))).pow_const _
      | fun_prop
    have key : ∀ x : Mt k 0, (Matrix.of x : Mat k 0) ∈ U0 k →
        ENNReal.ofReal (lam * ‖star c * star (x (iW k) (iW k)) + b‖) ^ (-s) ≤
          ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s) := by
      intro x hx
      have hz : ‖x (iW k) (iW k)‖ ≤ 1 := norm_fixedUnitary_entry_le_one hx (iW k) (iW k)
      have hw : ‖star (x (iW k) (iW k))‖ ≤ 1 := by rw [norm_star]; exact hz
      have h4 := norm_one_sub_le_two_mul_norm_one_sub_real_mul hw hρ0 hρ1
      have h5 := mul_le_mul_of_nonneg_left h4 hA
      have e2 : star c * star (x (iW k) (iW k)) + b =
          b * (1 - (ρ : ℂ) * star (x (iW k) (iW k))) := by
        rw [hsc]; ring
      have e3 : ‖(1 : ℂ) - x (iW k) (iW k)‖ = ‖(1 : ℂ) - star (x (iW k) (iW k))‖ := by
        rw [← norm_star, star_sub, star_one]
      rw [enn_nnnorm, ← ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ← ENNReal.ofReal_mul hA]
      apply ofReal_rpow_neg_anti hs
      rw [e2, norm_mul, e3]
      nlinarith [norm_nonneg ((1 : ℂ) - (ρ : ℂ) * star (x (iW k) (iW k))), norm_nonneg b]
    calc ∫⁻ x, ENNReal.ofReal (lam * ‖star c * star (x (iW k) (iW k)) + b‖) ^ (-s) ∂ν
        ≤ ∫⁻ x, ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) *
            (‖1 - x (iW k) (iW k)‖₊ : ℝ≥0∞) ^ (-s) ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [ae_mem_fixedUnitary hν] with x hx
          exact key x hx
      _ = ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * C0 k s ν := lintegral_const_mul _ hmeasC
      _ ≤ _ := mul_le_mul_of_nonneg_left le_self_add (zero_le ..)

private lemma nnnorm_one_sub_star_div_real_eq (z : ℂ) (t : ℝ) :
    ‖1 - star z / (t : ℂ)‖₊ = ‖1 - z / (t : ℂ)‖₊ := by
  have e : (1 : ℂ) - star z / (t : ℂ) = star (1 - z / (t : ℂ)) := by
    simp [star_div₀, Complex.conj_ofReal]
  rw [e, nnnorm_star]

lemma haarIntegralConstant_lt_top (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) (hνf : ν Set.univ < ∞)
    {s : ℝ} (hs : 0 ≤ s) (hsk : s < k) : C0 k s ν < ∞ := by
  classical
  have : IsFiniteMeasure ν := ⟨hνf⟩
  have hpq : iW k ≠ iK k := iW_ne_iK' hk
  have hcard : Fintype.card (Fin (2 * 0 + k + 1)) = k + 1 := by simp
  have hL := lint_Bset_lt_top hpq hcard hk hs hsk
  have hB0 := volume_Bset_ne_zero hpq hcard
  have hBm : MeasurableSet (Bset (iK k) : Set (Fin (2 * 0 + k + 1) → ℂ)) := measurableSet_Bset _

  let G : (Fin (2 * 0 + k + 1) → ℂ) → Mt k 0 → ℝ≥0∞ := fun x h =>
    (‖1 - ((Matrix.of h)ᴴ *ᵥ x) (iW k) / (tW (iK k) x : ℂ)‖₊ : ℝ≥0∞) ^ (-s)

  have hrot : ∀ x ∈ Bset (iK k), ∫⁻ h, G x h ∂ν = C0 k s ν := by
    intro x hx
    have ht : (1 : ℝ) / 2 ≤ tW (iK k) x := hx.1
    set c : ℂ := (tW (iK k) x : ℂ) with hcdef
    have hc : c ≠ 0 := by
      rw [hcdef]
      exact_mod_cast (ne_of_gt (by linarith : (0 : ℝ) < tW (iK k) x))
    have hvc : tW (iK k) x ^ 2 = Complex.normSq c := by
      rw [hcdef, Complex.normSq_ofReal]
      ring
    have hφ : Measurable fun z : ℂ => (‖1 - z / c‖₊ : ℝ≥0∞) ^ (-s) :=
      ((measurable_const.sub (measurable_id.div_const c)).nnnorm.coe_nnreal_ennreal).pow_const (-s)
    have hr := rot hk hν hφ x c hc hvc
    show ∫⁻ h, (fun z : ℂ => (‖1 - z / c‖₊ : ℝ≥0∞) ^ (-s)) (((Matrix.of h)ᴴ *ᵥ x) (iW k)) ∂ν = C0 k s ν
    rw [hr, C0]
    refine lintegral_congr fun h => ?_
    have hsc : star c = c := by rw [hcdef]; exact Complex.conj_ofReal _
    rw [hsc, mul_div_cancel_left₀ _ hc]
    have e : (1 : ℂ) - star (h (iW k) (iW k)) = star (1 - h (iW k) (iW k)) := by simp
    rw [e, nnnorm_star]

  have hinner : ∀ᵐ h ∂ν, ∫⁻ x in Bset (iK k), G x h = ∫⁻ x in Bset (iK k), PsiF (iW k) (iK k) s x := by
    filter_upwards [ae_mem_fixedUnitary hν] with h hh
    have hA : (Matrix.of h)ᴴ ∈ U0 k := fixedUnitary_conjTranspose_mem hh
    have hu := (fixedUnitary_projection_identities hA).1
    have htw := tW_mulVec hu (fixedUnitary_apply_fixedIndex_left hA)
    have hmp := mp_unitary _ hu
    have hpre : (fun x => (Matrix.of h)ᴴ *ᵥ x) ⁻¹' Bset (iK k) = Bset (iK k) := by
      ext x
      simp only [Set.mem_preimage, Bset, Set.mem_ofPred_eq, (htw x).1, (htw x).2]
    have hpt : ∀ x, G x h = PsiF (iW k) (iK k) s ((Matrix.of h)ᴴ *ᵥ x) := by
      intro x
      simp only [G, PsiF, (htw x).1]
      rw [nnnorm_one_sub_star_div_real_eq]
    simp only [hpt]
    rw [← hmp.setLIntegral_comp_preimage hBm (measurable_PsiF _ _ _), hpre]
  have hcont : Continuous fun p : (Fin (2 * 0 + k + 1) → ℂ) × Mt k 0 =>
      ((Matrix.of p.2)ᴴ *ᵥ p.1) (iW k) := by
    have h2 : Continuous fun p : (Fin (2 * 0 + k + 1) → ℂ) × Mt k 0 => (Matrix.of p.2 : Mat k 0) :=
      continuous_snd
    exact (continuous_apply _).comp (h2.matrix_conjTranspose.matrix_mulVec continuous_fst)
  have hden : Measurable fun p : (Fin (2 * 0 + k + 1) → ℂ) × Mt k 0 => (tW (iK k) p.1 : ℂ) :=
    (Complex.continuous_ofReal.comp ((continuous_tW (iK k)).comp continuous_fst)).measurable
  have hmeas : Measurable (Function.uncurry G) :=
    ((measurable_const.sub (hcont.measurable.div hden)).nnnorm.coe_nnreal_ennreal).pow_const (-s)
  have hswap := lintegral_lintegral_swap
    (hmeas.aemeasurable : AEMeasurable (Function.uncurry G) ((volume.restrict (Bset (iK k))).prod ν))
  have h1 : ∫⁻ x in Bset (iK k), ∫⁻ h, G x h ∂ν = C0 k s ν * volume (Bset (iK k)) := by
    rw [setLIntegral_congr_fun hBm hrot, lintegral_const, Measure.restrict_apply_univ]
  have h2 : ∫⁻ h, (∫⁻ x in Bset (iK k), G x h) ∂ν = (∫⁻ x in Bset (iK k), PsiF (iW k) (iK k) s x) * ν Set.univ := by
    rw [lintegral_congr_ae hinner, lintegral_const]
  have hfin : C0 k s ν * volume (Bset (iK k)) < ∞ := by
    rw [← h1, hswap, h2]
    exact ENNReal.mul_lt_top hL hνf
  rcases ENNReal.mul_lt_top_iff.1 hfin with h | h | h
  · exact h.1
  · rw [h]
    exact ENNReal.zero_lt_top
  · exact absurd h hB0

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

def sg (k : ℕ) (i : Fin (2 * 0 + k + 1)) : ℂ := if i = iK k then -1 else 1

lemma hpk_diag (k : ℕ) : Hpk k 0 = Matrix.diagonal (sg k) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Matrix.diagonal_apply, sg, iK, wI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | simp_all

lemma hpk_mulVec (v : Fin (2 * 0 + k + 1) → ℂ) (i : Fin (2 * 0 + k + 1)) :
    (Hpk k 0 *ᵥ v) i = sg k i * v i := by
  rw [hpk_diag, Matrix.mulVec_diagonal]

lemma hpk_sq (k : ℕ) : Hpk k 0 * Hpk k 0 = 1 := by
  rw [hpk_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [sg]
  split_ifs <;> norm_num

lemma herm0 (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) v w = ∑ i, star (w i) * (sg k i * v i) := by
  simp only [herm, dotProduct, Pi.star_apply, hpk_mulVec]

lemma herm_re (y : Fin (2 * 0 + k + 1) → ℂ) :
    (herm (Hpk k 0) y y).re = tW (iK k) y ^ 2 - Complex.normSq (y (iK k)) := by
  have hterm : ∀ i, (star (y i) * (sg k i * y i)).re =
      Complex.normSq (y i) - (if i = iK k then 2 * Complex.normSq (y i) else 0) := by
    intro i
    by_cases h : i = iK k
    · simp [sg, h, Complex.normSq_apply, Complex.mul_re]
      ring
    · simp [sg, h, Complex.normSq_apply, Complex.mul_re]
  rw [herm0, tW_sq, Complex.re_sum, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma phi'_eq (hk : 1 ≤ k) :
    phiV' k 0 0 = ((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) - bvec (iK k)) := by
  have hWK := iW_ne_iK hk
  funext i
  rw [phiV', hpk_mulVec]
  show sg k i * (((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) + bvec (iK k))) i = (((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) - bvec (iK k))) i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, bvec]
  rcases eq_or_ne i (iW k) with rfl | h1
  · simp [sg, hWK]
  · rcases eq_or_ne i (iK k) with rfl | h2
    · simp [sg, hWK.symm]
    · simp [h1, h2]

lemma phi'_iW (hk : 1 ≤ k) : phiV' k 0 0 (iW k) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [phi'_eq hk]
  simp [bvec, iW_ne_iK hk]

lemma phi'_iK (hk : 1 ≤ k) : phiV' k 0 0 (iK k) = -((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [phi'_eq hk]
  simp [bvec, (iW_ne_iK hk).symm]

lemma phi'_zero (hk : 1 ≤ k) (i : Fin (2 * 0 + k + 1)) (h1 : i ≠ iW k) (h2 : i ≠ iK k) :
    phiV' k 0 0 i = 0 := by
  rw [phi'_eq hk]
  simp [bvec, h1, h2]

lemma normSq_c : Complex.normSq ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma star_c : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

lemma norm_c : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
  rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]

lemma phi'_dot (hk : 1 ≤ k) : star (phiV' k 0 0) ⬝ᵥ phiV' k 0 0 = 1 := by
  have hWK := iW_ne_iK hk
  have hφ : ∀ i, Complex.normSq (phiV' k 0 0 i) =
      (if i = iW k then 1 / 2 else 0) + (if i = iK k then 1 / 2 else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, normSq_c, if_pos rfl, if_neg hWK, add_zero]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, Complex.normSq_neg, normSq_c, if_neg h1, if_pos rfl, zero_add]
      · rw [phi'_zero hk i h1 h2, map_zero, if_neg h1, if_neg h2, add_zero]
  rw [dot_star_self, Finset.sum_congr rfl fun i _ => hφ i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

private lemma sum_phi_lemma (hk : 1 ≤ k) (X : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i, star (phiV' k 0 0 i) * (sg k i * X i) = ((Real.sqrt 2)⁻¹ : ℂ) * (X (iW k) + X (iK k)) := by
  have hWK := iW_ne_iK hk
  have h : ∀ i, star (phiV' k 0 0 i) * (sg k i * X i) =
      (if i = iW k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iW k) else 0) + (if i = iK k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iK k) else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, star_c, if_pos rfl, if_neg hWK, add_zero]
      simp [sg, hWK]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, star_neg, star_c, if_neg h1, if_pos rfl, zero_add]
        simp [sg]
      · rw [phi'_zero hk i h1 h2, star_zero, zero_mul, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma phi'_iso (hk : 1 ≤ k) : herm (Hpk k 0) (phiV' k 0 0) (phiV' k 0 0) = 0 := by
  rw [herm0, sum_phi_lemma hk, phi'_iW hk, phi'_iK hk]
  ring

private lemma dl0_lemma_2 (M : Mat k 0) :
    Dl k 0 0 M = herm (Hpk k 0) (M *ᵥ phiV' k 0 0) (phiV' k 0 0) := by
  unfold Dl
  exact Matrix.det_fin_one _

lemma dl_eq (hk : 1 ≤ k) (M : Mat k 0) :
    Dl k 0 0 M = ((Real.sqrt 2)⁻¹ : ℂ) * ((M *ᵥ phiV' k 0 0) (iW k) + (M *ᵥ phiV' k 0 0) (iK k)) := by
  rw [dl0_lemma_2, herm0, sum_phi_lemma hk]

lemma G_left {g : Mat k 0} (hg : g ∈ GV k 0) : (Hpk k 0 * gᴴ * Hpk k 0) * g = 1 := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  calc Hpk k 0 * gᴴ * Hpk k 0 * g = Hpk k 0 * (gᴴ * Hpk k 0 * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

lemma G_star {g : Mat k 0} (hg : g ∈ GV k 0) : g * Hpk k 0 * gᴴ = Hpk k 0 := by
  have h1 : g * (Hpk k 0 * gᴴ * Hpk k 0) = 1 := mul_eq_one_comm.mp (G_left hg)
  calc g * Hpk k 0 * gᴴ = g * (Hpk k 0 * gᴴ * Hpk k 0) * Hpk k 0 := by
        simp only [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
    _ = Hpk k 0 := by rw [h1, Matrix.one_mul]

lemma G_det {g : Mat k 0} (hg : g ∈ GV k 0) : g.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (G_left hg)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

lemma herm_G {g : Mat k 0} (hg : g ∈ GV k 0) (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k 0) v w := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg']

private lemma ga0_lemma_3 (Y : Fin (0 + 1) → Fin (2 * 0 + k + 1) → ℂ) :
    Ga k 0 0 Y = (star (Y 0) ⬝ᵥ Y 0).re := by
  unfold Ga
  exact congrArg Complex.re (Matrix.det_fin_one _)

lemma sphericalFunction_fixedUnitary_eq_one (hk : 1 ≤ k) {h : Mat k 0} (hh : h ∈ U0 k) (s : Fin (0 + 1) → ℝ) : fsR k 0 s h = 1 := by
  rw [fsR, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ga0_lemma_3]
  rw [fixedUnitary_preserves_normSq hh, phi'_dot hk, Complex.one_re, Real.one_rpow]

lemma fsE_avg (hk : 1 ≤ k) {h : Mat k 0} (hh : h ∈ U0 k) (g h' : Mat k 0) (s : Fin (0 + 1) → ℝ) :
    FsE k 0 s (h⁻¹ * g * h') = ENNReal.ofReal ((Real.sqrt 2)⁻¹ *
      ‖(hᴴ *ᵥ ((g * h') *ᵥ phiV' k 0 0)) (iW k) + ((g * h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-s 0) := by
  have hinv : h⁻¹ = hᴴ := Matrix.inv_eq_left_inv (fixedUnitary_projection_identities hh).1
  rw [FsE, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, enn_nnnorm, dl_eq hk, norm_mul, norm_c,
    hinv, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, fixedUnitary_mulVec_fixedIndex (fixedUnitary_conjTranspose_mem hh)]

lemma outer_eq (hk : 1 ≤ k) {h' : Mat k 0} (hh : h' ∈ U0 k) (g : Mat k 0) :
    ‖((g * h') *ᵥ phiV' k 0 0) (iK k)‖ = (Real.sqrt 2)⁻¹ *
      ‖(h'ᴴ *ᵥ (fun j => star (g (iK k) j))) (iW k) + -star (g (iK k) (iK k))‖ := by
  have hM : ∀ M : Mat k 0, (M *ᵥ phiV' k 0 0) (iK k) =
      ((Real.sqrt 2)⁻¹ : ℂ) * (M (iK k) (iW k) - M (iK k) (iK k)) := by
    intro M
    rw [phi'_eq hk, Matrix.mulVec_smul, Matrix.mulVec_sub]
    simp [bvec, Matrix.mulVec_single]
  rw [hM, norm_mul, norm_c]
  congr 1
  have h1 : (g * h') (iK k) (iK k) = g (iK k) (iK k) := by
    rw [Matrix.mul_apply]
    simp [fixedUnitary_apply_fixedIndex_right hh]
  have h2 : (h'ᴴ *ᵥ fun j => star (g (iK k) j)) (iW k) = star ((g * h') (iK k) (iW k)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum,
      star_mul]
  rw [h1, h2, ← star_neg, ← star_add, norm_star, sub_eq_add_neg]

lemma outer_ws {g : Mat k 0} (hg : g ∈ GV k 0) :
    tW (iK k) (fun j => star (g (iK k) j)) ^ 2 + 1 = Complex.normSq (g (iK k) (iK k)) := by
  have e : (g * Hpk k 0 * gᴴ) (iK k) (iK k) = Hpk k 0 (iK k) (iK k) := by rw [G_star hg]
  rw [hpk_diag, Matrix.diagonal_apply_eq, Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] at e
  have hsK : sg k (iK k) = -1 := by simp [sg]
  have e2 : herm (Hpk k 0) (fun j => star (g (iK k) j)) (fun j => star (g (iK k) j)) = -1 := by
    rw [herm0, ← hsK, ← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [star_star]
    ring
  have hre := herm_re (k := k) (fun j => star (g (iK k) j))
  rw [e2] at hre
  have hn : Complex.normSq (star (g (iK k) (iK k))) = Complex.normSq (g (iK k) (iK k)) :=
    Complex.normSq_conj _
  simp only [Complex.neg_re, Complex.one_re] at hre
  rw [hn] at hre
  linarith

lemma iso_y (hk : 1 ≤ k) {g h' : Mat k 0} (hg : g ∈ GV k 0) (hh : h' ∈ GV k 0) :
    tW (iK k) ((g * h') *ᵥ phiV' k 0 0) ^ 2 = Complex.normSq (((g * h') *ᵥ phiV' k 0 0) (iK k)) ∧
    ((g * h') *ᵥ phiV' k 0 0) (iK k) ≠ 0 := by
  have hgh : g * h' ∈ GV k 0 := by
    show (g * h')ᴴ * Hpk k 0 * (g * h') = Hpk k 0
    have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
    have hh' : h'ᴴ * Hpk k 0 * h' = Hpk k 0 := hh
    rw [Matrix.conjTranspose_mul]
    calc h'ᴴ * gᴴ * Hpk k 0 * (g * h') = h'ᴴ * (gᴴ * Hpk k 0 * g) * h' := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k 0 := by rw [hg', hh']
  have hiso : herm (Hpk k 0) ((g * h') *ᵥ phiV' k 0 0) ((g * h') *ᵥ phiV' k 0 0) = 0 := by
    rw [herm_G hgh, phi'_iso hk]
  have hre := herm_re ((g * h') *ᵥ phiV' k 0 0)
  rw [hiso, Complex.zero_re] at hre
  refine ⟨by linarith, fun h0 => ?_⟩
  have hsum := tW_sq (iK k) ((g * h') *ᵥ phiV' k 0 0)
  rw [h0, map_zero, sub_zero] at hsum
  rw [h0, map_zero] at hre
  have hz : ∑ i, Complex.normSq (((g * h') *ᵥ phiV' k 0 0) i) = 0 := by
    rw [← hsum]
    linarith
  have hall : ∀ i, ((g * h') *ᵥ phiV' k 0 0) i = 0 := fun i =>
    Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp hz i
        (Finset.mem_univ i))
  have hdet : (g * h').det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (G_det hg) (G_det hh)
  have hphi := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext hall)
  have hW := congrFun hphi (iW k)
  rw [phi'_iW hk, Pi.zero_apply] at hW
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))) hW

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end
