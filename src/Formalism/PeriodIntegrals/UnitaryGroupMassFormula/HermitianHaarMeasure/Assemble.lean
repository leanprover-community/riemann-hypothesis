import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepresentsTransferOneOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem rel_posL_val (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    (posL k r i l).val = l.val + i.val := rfl

theorem rel_posL_injective (k r : ℕ) (i : Fin (r + 1)) : Function.Injective (posL k r i) := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [rel_posL_val, rel_posL_val] at h'
  omega

theorem rel_posL_bound (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    i.val ≤ (posL k r i l).val ∧ (posL k r i l).val + i.val ≤ 2 * r + k := by
  rw [rel_posL_val]
  have hl : l.val < 2 * (r - i.val) + k + 1 := l.isLt
  have hi := i.isLt
  omega

theorem rel_hpk_off_left (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r q p = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rel_hpk_off_right (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rel_sum_posL (k r : ℕ) (i : Fin (r + 1)) (F : Fin (2 * r + k + 1) → ℂ)
    (hF : ∀ a : Fin (2 * r + k + 1), (a.val < i.val ∨ 2 * r + k < a.val + i.val) → F a = 0) :
    ∑ a, F a = ∑ l : Fin (mdim k r i), F (posL k r i l) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := posL k r i)
    (fun x _ y _ h => rel_posL_injective k r i h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hF
  by_contra hc
  push_neg at hc
  apply ha
  have hi := i.isLt
  refine Finset.mem_image.2 ⟨⟨a.val - i.val, ?_⟩, Finset.mem_univ _, ?_⟩
  · show a.val - i.val < 2 * (r - i.val) + k + 1
    omega
  · apply Fin.ext
    show a.val - i.val + i.val = a.val
    omega

theorem rel_herm_unitary {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hU : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hU]

theorem rel_herm_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p : Fin n) (y : Fin n → ℂ) :
    herm H (bvec p) y = ∑ a, star (y a) * H a p := by
  unfold herm bvec
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

theorem conjugate_y_relation : YbRel := by
  intro k r z i _ g hg c
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  obtain ⟨_, hI, -⟩ := hpkFacts k r
  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hleft
  have hf : fvec k r z i = g *ᵥ (g⁻¹ *ᵥ fvec k r z i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have key : herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
      herm (Hpk k r) (bvec (posL k r i c)) (g⁻¹ *ᵥ fvec k r z i) := by
    conv_lhs => rw [hf]
    exact rel_herm_unitary _ _ hU _ _
  have hsum := rel_sum_posL k r i
    (fun a => star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
    ∑ l, Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [key, rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [mul_comm]
  rfl

theorem conjugate_x_relation : XbRel := by
  intro k r z' i _ c
  have hsum := rel_sum_posL k r i
    (fun a => star (fvec k r z' i a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star (fvec k r z' i a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (bvec (posL k r i c)) (fvec k r z' i) =
    ∑ l, Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star (fvec k r z' i (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [mul_comm]
  rfl

theorem restricted_gram_hermitian_involution : HmFacts := by
  intro k r i
  obtain ⟨hH, hI, -⟩ := hpkFacts k r
  constructor
  · ext a b
    show star (Hpk k r (posL k r i b) (posL k r i a)) = Hpk k r (posL k r i a) (posL k r i b)
    rw [← Matrix.conjTranspose_apply (Hpk k r), hH]
  · ext a b
    have h1 : (Hm k r i * Hm k r i) a b = (Hpk k r * Hpk k r) (posL k r i a) (posL k r i b) := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      symm
      refine rel_sum_posL k r i
        (fun q => Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b)) ?_
      intro q hq
      show Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b) = 0
      rw [rel_hpk_off_right k r (posL k r i a) q i.val (rel_posL_bound k r i a) hq, zero_mul]
    rw [h1, hI, Matrix.one_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg h, if_neg (fun e => h (rel_posL_injective k r i e))]

end PI.QnHermHaar
end
end

section
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma tst_exp_hasSum_linfty {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • X ^ j) (NormedSpace.exp X) :=
  NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X

end Linfty

lemma tst_exp_hasSum {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • X ^ j) (NormedSpace.exp X) := by
  exact tst_exp_hasSum_linfty X

private theorem exp_entry_lemma_2 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (j l : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) j l) (X j l) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) l).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) j)
  have h2 := (L.hasFDerivAt.comp_hasDerivAt _ hE).comp_ofReal
  simp only [L, Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

private theorem smul_mulVec_lemma {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext x
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma tst_exp_mulVec {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have h1 := (tst_exp_hasSum X).map (AddMonoidHom.mk' (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v)
    (fun A B => Matrix.add_mulVec A B v)) hc
  have h2 : HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) v := by
    have h := hasSum_single (f := fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) 0 (by
      intro j hj
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      show ((((m + 1).factorial : ℕ) : ℂ)⁻¹ • X ^ (m + 1)) *ᵥ v = 0
      rw [smul_mulVec_lemma, pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero])
    simpa using h
  exact h1.unique h2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma tst_mul_mem {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · have h1 : gᴴ * Hpk k r * g = Hpk k r := hg.1
    have h2 : hᴴ * Hpk k r * h = Hpk k r := hh.1
    show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    rw [Matrix.conjTranspose_mul,
      show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by simp only [Matrix.mul_assoc],
      h1, h2]
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).1, (hg.2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).2, (hg.2 a ha).2]

lemma tst_exp_mem {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hLie, hfix⟩ := hX
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hunitH : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hI)
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hI
  have hst : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · have hXc : Xᴴ = Hpk k r * (-X) * Hpk k r := by
      have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hLie
      calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hI, Matrix.mul_one]
        _ = Hpk k r * (-X) * Hpk k r := by rw [h1, Matrix.mul_neg]
    have hYc : ((t : ℂ) • X)ᴴ = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
      rw [hinv, Matrix.conjTranspose_smul, hst, hXc, ← smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    have hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ =
        Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
      rw [← Matrix.exp_conjTranspose, hYc, Matrix.exp_conj _ _ hunitH]
    have hEE : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
      rw [Matrix.exp_neg]
      exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
    rw [hE, hinv, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-((t : ℂ) • X))) (Hpk k r) (Hpk k r), hI,
      Matrix.mul_one, Matrix.mul_assoc, hEE, Matrix.mul_one]
  · exact tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).1, smul_zero])
  · exact tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).2, smul_zero])

lemma tst_H_zero {k r : ℕ} (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i q) (eI k r a) = 0 ∧ Hpk k r (posL k r i q) (esI k r a) = 0 := by
  have hq : q.val < 2 * (r - i.val) + k + 1 := q.isLt
  have hi := i.isLt
  have hp : (posL k r i q).val = q.val + i.val := rfl
  have he : (eI k r a).val = a.val := rfl
  have hs : (esI k r a).val = 2 * r + k - a.val := rfl
  constructor
  · simp only [Hpk, Fin.ext_iff, hp, he]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [Hpk, Fin.ext_iff, hp, hs]
    split_ifs <;> first | rfl | (exfalso; omega)

lemma tst_Z_fix {n : ℕ} (a' b' p : Fin n) (h : b' ≠ p) : Matrix.single a' b' (1 : ℂ) *ᵥ bvec p = 0 := by
  ext x
  simp [bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h]

lemma tst_ZH_fix {n : ℕ} (W H : Matrix (Fin n) (Fin n) ℂ) (a' b' p : Fin n) (h : H a' p = 0) :
    (W * (Matrix.single a' b' (1 : ℂ))ᴴ * H) *ᵥ bvec p = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h0 : (Matrix.single a' b' (1 : ℂ))ᴴ *ᵥ (H *ᵥ bvec p) = 0 := by
    ext x
    simp [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.single_apply, Pi.single_apply, h]
    by_cases hb : b' = x <;> simp [hb, h]
  rw [h0, Matrix.mulVec_zero]

lemma tst_core1 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) :
    (Z - H * Zᴴ * H)ᴴ * H + H * (Z - H * Zᴴ * H) = 0 := by
  have hHH : ∀ Y : Matrix (Fin n) (Fin n) ℂ, H * (H * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hH2, Matrix.one_mul]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hH2, hHH, Matrix.mul_one]
  abel

lemma tst_core2 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) :
    (Z + H * Zᴴ * H)ᴴ * H = H * (Z + H * Zᴴ * H) := by
  have hHH : ∀ Y : Matrix (Fin n) (Fin n) ℂ, H * (H * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hH2, Matrix.one_mul]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hH2, hHH, Matrix.mul_one]
  abel

lemma tst_lie {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hH := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hI
  have hfx : ∀ a' : Fin r, a'.val < i.val → ∀ p : Fin (2 * r + k + 1), (p = eI k r a' ∨ p = esI k r a') →
      Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) *ᵥ bvec p = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec p = 0 := by
    intro a' ha' p hp
    have hb : b.val < 2 * (r - i.val) + k + 1 := b.isLt
    have hi := i.isLt
    have hpb : (posL k r i b).val = b.val + i.val := rfl
    have hne : posL k r i b ≠ p := by
      intro e
      rcases hp with rfl | rfl
      · have := congrArg Fin.val e
        rw [hpb] at this
        have h2 : (eI k r a').val = a'.val := rfl
        omega
      · have := congrArg Fin.val e
        rw [hpb] at this
        have h2 : (esI k r a').val = 2 * r + k - a'.val := rfl
        omega
    have hz : Hpk k r (posL k r i a) p = 0 := by
      rcases hp with rfl | rfl
      · exact (tst_H_zero i a a' ha').1
      · exact (tst_H_zero i a a' ha').2
    exact ⟨tst_Z_fix _ _ _ hne, tst_ZH_fix _ _ _ _ _ hz⟩
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.conj_ofReal _
  have hs2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I, map_ofNat]
    ring
  constructor
  · refine ⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩
    · simp only [hpart1, hinv]
      rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, tst_core1 _ _ hH hI,
        smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inl rfl)
      simp only [hpart1, hinv]
      rw [smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inr rfl)
      simp only [hpart1, hinv]
      rw [smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
  · refine ⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩
    · simp only [hpart2, hinv]
      rw [Matrix.conjTranspose_smul, hs2, Matrix.smul_mul, Matrix.mul_smul, tst_core2 _ _ hH hI, neg_smul,
        neg_add_cancel]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inl rfl)
      simp only [hpart2, hinv]
      rw [smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inr rfl)
      simp only [hpart2, hinv]
      rw [smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]

private theorem gamma_lemma_3 {k r : ℕ} (g X : Mx k r) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  refine hasDerivAt_pi.2 fun m => hasDerivAt_pi.2 fun l => ?_
  simp only [Matrix.mul_apply]
  have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => (exp_entry_lemma_2 X j l).const_mul (g m j)
  convert hs using 1
  ext y
  simp [Finset.sum_apply]

lemma tst_rdV_eq {k r : ℕ} {i : Fin (r + 1)} (f F : Mx k r → ℂ) (U : Set (Mx k r)) (g X : Mx k r)
    (hU : IsOpen U) (hg : g ∈ U) (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, h ∈ Glev k r i → f h = F h) (hX : inLieLev k r i X) :
    RdV X f g = fderiv ℝ F g (g * X) := by
  have hγ := gamma_lemma_3 g X
  have hFd : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF.differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hg)).hasFDerivAt
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' U ∈ nhds (0 : ℝ) := by
      apply hγ.continuousAt.preimage_mem_nhds
      show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
      rw [h0]
      exact hU.mem_nhds hg
    filter_upwards [hmem] with t ht
    exact hfF _ ht (tst_mul_mem hgG (tst_exp_mem hX t))
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq 0 hFd hγ h0.symm
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = fderiv ℝ F g (g * X)
  exact (hcomp.congr_of_eventuallyEq hev).deriv

lemma tst_rdV_zero {k r : ℕ} {i : Fin (r + 1)} (f : Mx k r → ℂ) (K : Set (Mx k r)) (hK : IsClosed K)
    (hKf : ∀ g ∈ Glev k r i, g ∉ K → f g = 0) (X : Mx k r) (hX : inLieLev k r i X) (g : Mx k r)
    (hg : g ∈ Glev k r i) (hgK : g ∉ K) : RdV X f g = 0 := by
  have hγ := gamma_lemma_3 g X
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0] fun _ => (0 : ℂ) := by
    have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
    have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' Kᶜ ∈ nhds (0 : ℝ) := by
      apply hγ.continuousAt.preimage_mem_nhds
      show Kᶜ ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
      rw [h0]
      exact hK.isOpen_compl.mem_nhds hgK
    filter_upwards [hmem] with t ht
    exact hKf _ (tst_mul_mem hg (tst_exp_mem hX t)) ht
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = 0
  rw [hev.deriv_eq, deriv_const]

theorem elementary_generator_preserves_test : EabTest := by
  intro k r i a b f hf
  unfold TestF CptOn at hf ⊢
  obtain ⟨hs, K, hK, hKf⟩ := hf
  obtain ⟨h1, h2⟩ := tst_lie (k := k) i a b
  refine ⟨?_, K, hK, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hs g₀ hg₀
    have hd := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    refine ⟨U, fun g => fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) +
      Complex.I • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)),
      hU, hg₀U, ?_, ?_⟩
    · exact (hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).add
        ((hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).const_smul Complex.I)
    · intro g hg hgG
      show RdV _ f g + Complex.I • RdV _ f g = _
      rw [tst_rdV_eq f F U g _ hU hg hgG hF hfF h1, tst_rdV_eq f F U g _ hU hg hgG hF hfF h2]
  · intro g hg hgK
    show RdV _ f g + Complex.I • RdV _ f g = 0
    rw [tst_rdV_zero f K hK.isClosed hKf _ h1 g hg hgK, tst_rdV_zero f K hK.isClosed hKf _ h2 g hg hgK,
      smul_zero, add_zero]

lemma tst_cd_star {k r : ℕ} {φ : Mx k r → ℂ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (fun g => star (φ g)) := by
  have h2 := (Complex.conjCLE.contDiff (n := ∞)).comp h
  simpa [Function.comp_def] using h2

lemma tst_mul_test {k r : ℕ} {i : Fin (r + 1)} (φ ψ : Mx k r → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ∀ g ∈ Glev k r i, ψ g = φ g) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => ψ g * f g) := by
  unfold TestF SmoothLev CptOn at *
  obtain ⟨hs, K, hK, hKf⟩ := hf
  refine ⟨fun g₀ hg₀ => ?_, K, hK, fun g hg hgK => by
    show ψ g * f g = 0
    rw [hKf g hg hgK, mul_zero]⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hs g₀ hg₀
  refine ⟨U, fun g => φ g * F g, hU, hgU, hφ.contDiffOn.mul hF, fun g hgU' hgG => ?_⟩
  show ψ g * f g = φ g * F g
  rw [hψ g hgG, hfF g hgU' hgG]

def yExt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) : ℂ :=
  ∑ l, Hpk k r (posL k r i c) l * star (∑ m, star ((Hpk k r *ᵥ fvec k r z i) m) * g m l)

def bExt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) : ℂ :=
  ∑ j, star (fvec k r z i j) * ∑ l, Hpk k r j l * g l (posL k r i c)

lemma tst_yExt_cd (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) :
    ContDiff ℝ ∞ (yExt k r z i c) := by
  unfold yExt
  exact ContDiff.sum fun l _ => contDiff_const.mul
    (tst_cd_star (ContDiff.sum fun m _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id m) l)))

lemma tst_bExt_cd (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) :
    ContDiff ℝ ∞ (bExt k r z i c) := by
  unfold bExt
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (ContDiff.sum fun l _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id l) (posL k r i c)))

lemma tst_inv_eq {k r : ℕ} {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]

lemma tst_yv_eq {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) {g : Mx k r}
    (hg : g ∈ Glev k r i) : yv k r z i g c = yExt k r z i c g := by
  show (g⁻¹ *ᵥ fvec k r z i) (posL k r i c) = yExt k r z i c g
  rw [tst_inv_eq hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [yExt, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul, star_star]

lemma tst_ybv_eq {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) :
    ybv k r z i g c = bExt k r z i c g := by
  have hcol : g *ᵥ bvec (posL k r i c) = fun l => g l (posL k r i c) := by
    ext l
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) = bExt k r z i c g
  rw [hcol]
  simp only [herm, bExt, dotProduct, Matrix.mulVec, Pi.star_apply]

theorem multiplication_preserves_test : MulTest := by
  intro k r z i c f hf
  exact ⟨tst_mul_test (yExt k r z i c) (fun g => yv k r z i g c) (tst_yExt_cd k r z i c)
      (fun g hg => tst_yv_eq z i c hg) f hf,
    tst_mul_test (fun g => star (yExt k r z i c g)) (fun g => star (yv k r z i g c))
      (tst_cd_star (tst_yExt_cd k r z i c)) (fun g hg => congrArg star (tst_yv_eq z i c hg)) f hf,
    tst_mul_test (bExt k r z i c) (fun g => ybv k r z i g c) (tst_bExt_cd k r z i c)
      (fun g _ => tst_ybv_eq z i c g) f hf,
    tst_mul_test (fun g => star (bExt k r z i c g)) (fun g => star (ybv k r z i g c))
      (tst_cd_star (tst_bExt_cd k r z i c)) (fun g _ => congrArg star (tst_ybv_eq z i c g)) f hf⟩

lemma tst_glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have h1 : IsClosed {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h2 : ∀ a : Fin r, IsClosed {g : Mx k r | a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    intro a
    by_cases ha : a.val < i.val
    · simp only [ha, true_implies, Set.setOf_and]
      exact (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
    · simp only [ha, false_implies, Set.setOf_true]
      exact isClosed_univ
  have e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩ ⋂ a : Fin r, {g : Mx k r | a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    ext g
    simp [Glev, UH]
  rw [e]
  exact h1.inter (isClosed_iInter h2)

lemma tst_contOn {k r : ℕ} {i : Fin (r + 1)} (f : Mx k r → ℂ) (hf : SmoothLev k r i Set.univ f) :
    ContinuousOn f (Glev k r i) := by
  unfold SmoothLev at hf
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ ⟨hg₀, Set.mem_univ _⟩
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (Glev k r i) (hU.mem_nhds hg₀U)] with g hg
  exact hfF g hg.2 hg.1

theorem test_function_pairing_integral : TestInt := by
  intro k r i μ hμ f h hf hh
  unfold TestF CptOn at hf hh
  obtain ⟨hfs, Kf, hKf, hKf0⟩ := hf
  obtain ⟨hhs, -, -, -⟩ := hh
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ.finite_compact K hK⟩
  let S : Set (Mt k r) := Glev k r i
  let K : Set (Mt k r) := Kf
  have hSc : IsClosed S := tst_glev_closed k r i
  have hKc : IsCompact K := hKf
  have hfo : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) S := tst_contOn f hfs
  have hho : ContinuousOn (fun x : Mt k r => h (Matrix.of x)) S := tst_contOn h hhs
  have hφc : ContinuousOn (fun x : Mt k r => f (Matrix.of x) * star (h (Matrix.of x))) S :=
    hfo.mul (Complex.continuous_conj.comp_continuousOn hho)
  have hint : IntegrableOn (fun x : Mt k r => f (Matrix.of x) * star (h (Matrix.of x))) (S ∩ K) μ :=
    (hφc.mono Set.inter_subset_left).integrableOn_compact (hKc.inter_left hSc)
  have hind := hint.integrable_indicator (hSc.inter hKc.isClosed).measurableSet
  refine hind.congr ?_
  have hae : ∀ᵐ x ∂μ, x ∈ S := by
    rw [ae_iff]
    exact hμ.conc
  filter_upwards [hae] with x hx
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem (show x ∈ S ∩ K from ⟨hx, hxK⟩)]
  · have e : f (Matrix.of x) * star (h (Matrix.of x)) = 0 := by
      rw [hKf0 (Matrix.of x) hx hxK, zero_mul]
    rw [e]
    exact Set.indicator_apply_eq_zero.mpr (fun _ => e)

end PI.QnHermHaar
end
end

section
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

namespace HermitianAdjointLemmas

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have hexp : NormedSpace.exp X = ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • X ^ m := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  let φ : Matrix (Fin n) (Fin n) ℂ →+ (Fin n → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun A B => Matrix.add_mulVec A B v }
  have hφ : Continuous φ := continuous_id.matrix_mulVec continuous_const
  have h1 := hs.hasSum.map φ hφ
  have h2 : HasSum (fun m : ℕ => φ (((m.factorial : ℂ)⁻¹) • X ^ m)) v := by
    have e : (fun m : ℕ => φ (((m.factorial : ℂ)⁻¹) • X ^ m)) = fun m => if m = 0 then v else 0 := by
      funext m
      rcases m with _ | m
      · simp [φ]
      · simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (Nat.succ_ne_zero m)]
        rw [Matrix.smul_mulVec, pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
          smul_zero]
    rw [e]
    exact hasSum_ite_eq 0 v
  rw [hexp]
  exact h1.unique h2

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv WeylGroupFacts.hpk_sq

lemma hpk_ct : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1

lemma hpk_isUnit : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, WeylGroupFacts.hpk_sq, WeylGroupFacts.hpk_sq⟩, rfl⟩

lemma hpk_hpk (X : Mx k r) : Hpk k r * (Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.one_mul]

lemma inU_rsmul {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) (c : ℝ) :
    ((c : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((c : ℂ) • X) = 0 := by
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma exp_mem_uh {Y : Mx k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  have h0 : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hpk_inv, Matrix.mul_neg, ← h0, Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.mul_one]
  have hexp : (NormedSpace.exp Y)ᴴ = Hpk k r * NormedSpace.exp (-Y) * Hpk k r := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hpk_isUnit, hpk_inv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  rw [hexp, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-Y)) (Hpk k r) (Hpk k r), WeylGroupFacts.hpk_sq,
    Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]

lemma glev_mul_exp {i : Fin (r + 1)} {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X)
    (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  have e : ∀ v, X *ᵥ v = 0 → (g * NormedSpace.exp ((t : ℂ) • X)) *ᵥ v = g *ᵥ v := by
    intro v hv
    rw [← Matrix.mulVec_mulVec, exp_mulVec_fix _ v (by rw [Matrix.smul_mulVec, hv, smul_zero])]
  show _ ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val → _
  refine ⟨WeylGroupFacts.uh_mul hg'.1 (exp_mem_uh (inU_rsmul hX.1 t)), fun a ha => ?_⟩
  obtain ⟨h1, h2⟩ := hX.2 a ha
  obtain ⟨g1, g2⟩ := hg'.2 a ha
  exact ⟨by rw [e _ h1, g1], by rw [e _ h2, g2]⟩

lemma rd_ext {i : Fin (r + 1)} {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) {g : Mx k r}
    (hg : g ∈ Glev k r i) : ∃ L : Mx k r →L[ℝ] ℂ, ∀ X, inLieLev k r i X → RdV X f g = L (g * X) := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g ⟨hg, Set.mem_univ _⟩
  refine ⟨fderiv ℝ F g, fun X hX => ?_⟩
  unfold RdV
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (glev_mul_exp hg hX t)
  rw [hev.deriv_eq]
  exact hcomp.deriv

lemma rdV_neg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : RdV (-X) f g = -RdV X f g := by
  unfold RdV
  have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • -X))) =
      fun t : ℝ => (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (-t) := by
    funext t
    simp only [Complex.ofReal_neg, smul_neg, neg_smul]
  rw [e]
  exact (deriv_comp_neg (f := fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (x := 0)).trans
    (by rw [neg_zero])

def Out (i : Fin (r + 1)) (p : Fin (2 * r + k + 1)) : Prop := p.val < i.val ∨ 2 * r + k < p.val + i.val

def SuppV (i : Fin (r + 1)) (W : Mx k r) : Prop := ∀ p q, (Out i p ∨ Out i q) → W p q = 0

lemma out_tau {i : Fin (r + 1)} {p : Fin (2 * r + k + 1)} (h : Out i p) : Out i (WeylGroupFacts.tau k r p) := by
  have := i.isLt
  have := p.isLt
  unfold Out WeylGroupFacts.tau at *
  split_ifs <;> simp only <;> omega

lemma not_out_posL (i : Fin (r + 1)) (c : Fin (mdim k r i)) : ¬ Out i (posL k r i c) := by
  have := i.isLt
  have := c.isLt
  unfold Out posL mdim at *
  simp only
  omega

lemma supp_sub {i : Fin (r + 1)} {A B : Mx k r} (hA : SuppV i A) (hB : SuppV i B) : SuppV i (A - B) := by
  intro p q h; rw [Matrix.sub_apply, hA p q h, hB p q h, sub_zero]

lemma supp_add {i : Fin (r + 1)} {A B : Mx k r} (hA : SuppV i A) (hB : SuppV i B) : SuppV i (A + B) := by
  intro p q h; rw [Matrix.add_apply, hA p q h, hB p q h, add_zero]

lemma supp_smul {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) (c : ℂ) : SuppV i (c • A) := by
  intro p q h; rw [Matrix.smul_apply, hA p q h, smul_zero]

lemma supp_ct {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i Aᴴ := by
  intro p q h; rw [Matrix.conjTranspose_apply, hA q p h.symm, star_zero]

lemma supp_hmul {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (Hpk k r * A) := by
  intro p q h
  rw [WeylGroupFacts.hpk_mul_apply]
  rcases h with hp | hq
  · rw [hA _ _ (Or.inl (out_tau hp)), mul_zero]
  · rw [hA _ _ (Or.inr hq), mul_zero]

lemma supp_mulh {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (A * Hpk k r) := by
  have e : A * Hpk k r = (Hpk k r * Aᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct]
  rw [e]
  exact supp_ct (supp_hmul (supp_ct hA))

lemma supp_conj {i : Fin (r + 1)} {A : Mx k r} (hA : SuppV i A) : SuppV i (Hpk k r * Aᴴ * Hpk k r) :=
  supp_mulh (supp_hmul (supp_ct hA))

lemma supp_single (i : Fin (r + 1)) (c d : Fin (mdim k r i)) :
    SuppV i (Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) := by
  intro p q h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  rcases h with h | h <;> exact not_out_posL i _ h

lemma supp_hpart1 {i : Fin (r + 1)} {W : Mx k r} (hW : SuppV i W) : SuppV i (hpart1 (Hpk k r) W) := by
  unfold hpart1
  rw [hpk_inv]
  exact supp_smul (supp_sub hW (supp_conj hW)) _

lemma supp_hpart2 {i : Fin (r + 1)} {W : Mx k r} (hW : SuppV i W) : SuppV i (hpart2 (Hpk k r) W) := by
  unfold hpart2
  rw [hpk_inv]
  exact supp_smul (supp_add hW (supp_conj hW)) _

lemma inU_hpart1 (W : Mx k r) :
    (hpart1 (Hpk k r) W)ᴴ * Hpk k r + Hpk k r * hpart1 (Hpk k r) W = 0 := by
  unfold hpart1
  rw [hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, ← smul_add]
  convert smul_zero (1 / 2 : ℂ) using 2
  abel

lemma inU_hpart2 (W : Mx k r) :
    (hpart2 (Hpk k r) W)ᴴ * Hpk k r + Hpk k r * hpart2 (Hpk k r) W = 0 := by
  unfold hpart2
  rw [hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_ct, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    simp [mul_neg, div_neg, map_ofNat]
  rw [hs, neg_smul, neg_add_eq_zero]
  congr 1
  abel

lemma lie_of {i : Fin (r + 1)} {X : Mx k r} (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hS : SuppV i X) :
    inLieLev k r i X := by
  refine ⟨hU, fun a ha => ⟨?_, ?_⟩⟩
  · funext p
    simp only [bvec, Matrix.mulVec_single_one, Pi.zero_apply]
    refine hS _ _ (Or.inr ?_)
    have := a.isLt
    unfold Out eI
    simp only
    omega
  · funext p
    simp only [bvec, Matrix.mulVec_single_one, Pi.zero_apply]
    refine hS _ _ (Or.inr ?_)
    have := a.isLt
    unfold Out esI
    simp only
    omega

lemma hpart1_add (A B : Mx k r) :
    hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
  unfold hpart1
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

lemma hpart2_add (A B : Mx k r) :
    hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
  unfold hpart2
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

lemma two_I_inv : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero) two_ne_zero]
  linear_combination (2 : ℂ) * Complex.I_sq

lemma star_re_im (c : ℂ) : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

lemma hpart1_smul (c : ℂ) (W : Mx k r) :
    hpart1 (Hpk k r) (c • W) = c.re • hpart1 (Hpk k r) W - c.im • hpart2 (Hpk k r) W := by
  unfold hpart1 hpart2
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
    ← Complex.coe_smul, two_I_inv, star_re_im]
  set M := (Hpk k r)⁻¹ * Wᴴ * Hpk k r
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  match_scalars <;> ring_nf

lemma hpart2_smul (c : ℂ) (W : Mx k r) :
    hpart2 (Hpk k r) (c • W) = c.re • hpart2 (Hpk k r) W + c.im • hpart1 (Hpk k r) W := by
  unfold hpart1 hpart2
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
    ← Complex.coe_smul, two_I_inv, star_re_im]
  set M := (Hpk k r)⁻¹ * Wᴴ * Hpk k r
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  match_scalars <;> (ring_nf; (try simp only [Complex.I_sq]); (try ring))

def phiL (L : Mx k r →L[ℝ] ℂ) (g : Mx k r) : Mx k r →ₗ[ℂ] ℂ where
  toFun W := L (g * hpart1 (Hpk k r) W) + Complex.I * L (g * hpart2 (Hpk k r) W)
  map_add' A B := by
    simp only [hpart1_add, hpart2_add, Matrix.mul_add, map_add]
    ring
  map_smul' c W := by
    simp only [RingHom.id_apply, smul_eq_mul, hpart1_smul, hpart2_smul, Matrix.mul_sub,
      Matrix.mul_add, Matrix.mul_smul, map_sub, map_add, map_smul, Complex.real_smul]
    set L1 := L (g * hpart1 (Hpk k r) W)
    set L2 := L (g * hpart2 (Hpk k r) W)
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_rhs => rw [hc]
    linear_combination (-((c.im : ℂ) * L2)) * Complex.I_sq

lemma hpart1_conj (Z : Mx k r) :
    hpart1 (Hpk k r) (Hpk k r * Zᴴ * Hpk k r) = -hpart1 (Hpk k r) Z := by
  unfold hpart1
  rw [hpk_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hpk_ct]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  rw [← smul_neg, neg_sub]

lemma hpart2_conj (Z : Mx k r) :
    hpart2 (Hpk k r) (Hpk k r * Zᴴ * Hpk k r) = hpart2 (Hpk k r) Z := by
  unfold hpart2
  rw [hpk_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hpk_ct]
  simp only [Matrix.mul_assoc, WeylGroupFacts.hpk_sq, hpk_hpk, Matrix.mul_one]
  congr 1
  abel

lemma hpk_conj_single_apply (a' b' p q : Fin (2 * r + k + 1)) :
    (Hpk k r * (Matrix.single a' b' (1 : ℂ))ᴴ * Hpk k r) p q = Hpk k r p b' * Hpk k r a' q := by
  rw [Matrix.conjTranspose_single, star_one]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

lemma hpk_out_left {i : Fin (r + 1)} {p m : Fin (2 * r + k + 1)} (hp : Out i p) (hm : ¬ Out i m) :
    Hpk k r p m = 0 := by
  rw [WeylGroupFacts.hpk_row, if_neg]
  intro h
  exact hm (h ▸ out_tau hp)

lemma hpk_out_right {i : Fin (r + 1)} {q m : Fin (2 * r + k + 1)} (hq : Out i q) (hm : ¬ Out i m) :
    Hpk k r m q = 0 := by
  rw [WeylGroupFacts.hpk_row, if_neg]
  intro h
  apply hm
  have := out_tau (k := k) hq
  rw [h, WeylGroupFacts.tau_tau] at this
  exact this

lemma posL_inj {i : Fin (r + 1)} {c c' : Fin (mdim k r i)} (h : posL k r i c = posL k r i c') : c = c' := by
  have := congrArg Fin.val h
  simp only [posL] at this
  exact Fin.ext (by omega)

lemma posL_surj {i : Fin (r + 1)} {p : Fin (2 * r + k + 1)} (hp : ¬ Out i p) :
    ∃ c : Fin (mdim k r i), posL k r i c = p := by
  have := i.isLt
  unfold Out at hp
  refine ⟨⟨p.val - i.val, by unfold mdim; omega⟩, Fin.ext ?_⟩
  simp only [posL]
  omega

lemma conj_single_expand (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r =
      ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ) := by
  ext p q
  rw [hpk_conj_single_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hp : Out i p
  · rw [hpk_out_left hp (not_out_posL i b), zero_mul]
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨rfl, -⟩
    exact not_out_posL i c hp
  by_cases hq : Out i q
  · rw [hpk_out_right hq (not_out_posL i a), mul_zero]
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨-, rfl⟩
    exact not_out_posL i d hq
  obtain ⟨c₀, rfl⟩ := posL_surj hp
  obtain ⟨d₀, rfl⟩ := posL_surj hq
  rw [Finset.sum_eq_single c₀, Finset.sum_eq_single d₀, if_pos ⟨rfl, rfl⟩]
  · rfl
  · intro d _ hd
    rw [if_neg]
    rintro ⟨-, h⟩
    exact hd (posL_inj h)
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => if_neg ?_
    rintro ⟨h, -⟩
    exact hc (posL_inj h)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma ec_phi {i : Fin (r + 1)} {L : Mx k r →L[ℝ] ℂ} {f : Mx k r → ℂ} {g : Mx k r}
    (hL : ∀ X, inLieLev k r i X → RdV X f g = L (g * X)) {W : Mx k r} (hW : SuppV i W) :
    RdV (hpart1 (Hpk k r) W) f g + Complex.I • RdV (hpart2 (Hpk k r) W) f g = phiL L g W := by
  rw [hL _ (lie_of (inU_hpart1 W) (supp_hpart1 hW)), hL _ (lie_of (inU_hpart2 W) (supp_hpart2 hW)),
    smul_eq_mul]
  rfl

lemma ec_expand {i : Fin (r + 1)} {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) {g : Mx k r}
    (hg : g ∈ Glev k r i) (a b : Fin (mdim k r i)) :
    RdV (hpart1 (Hpk k r) (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) f g +
      Complex.I • RdV (hpart2 (Hpk k r)
        (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) f g =
    ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g := by
  obtain ⟨L, hL⟩ := rd_ext hf hg
  rw [ec_phi hL (supp_conj (supp_single i a b)), conj_single_expand, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, ← ec_phi hL (supp_single i c d)]
  rfl

end HermitianAdjointLemmas

open HermitianAdjointLemmas in
theorem elementary_generator_adjoint : EabAdjFrom := by
  intro hRd _hP hT hI k r i μ hμ a b f₁ f₂ h₁ h₂
  set Z : Mx k r := Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) with hZ
  have hX1 : inLieLev k r i (hpart1 (Hpk k r) Z) :=
    lie_of (inU_hpart1 Z) (supp_hpart1 (supp_single i a b))
  have hX2 : inLieLev k r i (hpart2 (Hpk k r) Z) :=
    lie_of (inU_hpart2 Z) (supp_hpart2 (supp_single i a b))
  set Ψ : (Mx k r → ℂ) → Mx k r → ℂ := fun f g =>
    ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g with hΨ
  have hE : ∀ f g, EH k r (posL k r i a) (posL k r i b) f g =
      RdV (hpart1 (Hpk k r) Z) f g + Complex.I * RdV (hpart2 (Hpk k r) Z) f g := fun f g => rfl
  have hPsi : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      Ψ f g = -RdV (hpart1 (Hpk k r) Z) f g + Complex.I * RdV (hpart2 (Hpk k r) Z) f g := by
    intro f hf g hg
    rw [hΨ]
    dsimp only
    rw [← ec_expand hf hg a b, hpart1_conj, hpart2_conj, rdV_neg, smul_eq_mul]
  have hR1 : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      RdV (hpart1 (Hpk k r) Z) f g = (EH k r (posL k r i a) (posL k r i b) f g - Ψ f g) / 2 := by
    intro f hf g hg
    rw [hE, hPsi f hf g hg]
    ring
  have hR2 : ∀ f, SmoothLev k r i Set.univ f → ∀ g ∈ Glev k r i,
      RdV (hpart2 (Hpk k r) Z) f g =
        (EH k r (posL k r i a) (posL k r i b) f g + Ψ f g) / (2 * Complex.I) := by
    intro f hf g hg
    rw [hE, hPsi f hf g hg]
    field_simp
    ring
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ Glev k r i := by
    rw [ae_iff]
    exact hμ.conc

  have iA : Integrable (fun x : Mt k r =>
      EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ :=
    hI k r i μ hμ _ _ (hT k r i a b f₁ h₁) h₂
  have iB : Integrable (fun x : Mt k r => Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ := by
    have e : (fun x : Mt k r => Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) = fun x =>
        ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) *
          (EH k r (posL k r i c) (posL k r i d) f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) := by
      funext x
      simp only [hΨ, Finset.sum_mul, smul_eq_mul, mul_assoc]
    rw [e]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ =>
      (hI k r i μ hμ _ _ (hT k r i c d f₁ h₁) h₂).const_mul _
  have iC : Integrable (fun x : Mt k r =>
      f₁ (Matrix.of x) * star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x))) μ :=
    hI k r i μ hμ _ _ h₁ (hT k r i a b f₂ h₂)
  have iD : Integrable (fun x : Mt k r => f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x))) μ := by
    have e : (fun x : Mt k r => f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x))) = fun x =>
        ∑ c, ∑ d, star (Hm k r i c b * Hm k r i a d) *
          (f₁ (Matrix.of x) * star (EH k r (posL k r i c) (posL k r i d) f₂ (Matrix.of x))) := by
      funext x
      simp only [hΨ, star_sum, Finset.mul_sum, smul_eq_mul, star_mul']
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [e]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ =>
      (hI k r i μ hμ _ _ h₁ (hT k r i c d f₂ h₂)).const_mul _

  have s1 := hRd k r i μ hμ _ f₁ f₂ hX1 h₁.1 h₂.1 h₁.2 h₂.2
  have s2 := hRd k r i μ hμ _ f₁ f₂ hX2 h₁.1 h₂.1 h₁.2 h₂.2
  have l1 : (∫ x : Mt k r, RdV (hpart1 (Hpk k r) Z) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      (1 / 2 : ℂ) * ((∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) *
        star (f₂ (Matrix.of x)) ∂μ) - ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_sub iA iB, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR1 f₁ h₁.1 _ hx]
    ring
  have r1 : (∫ x : Mt k r, f₁ (Matrix.of x) * star (RdV (hpart1 (Hpk k r) Z) f₂ (Matrix.of x)) ∂μ) =
      (1 / 2 : ℂ) * ((∫ x : Mt k r, f₁ (Matrix.of x) *
        star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ) -
          ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_sub iC iD, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR1 f₂ h₂.1 _ hx, star_div₀, star_sub, star_ofNat]
    ring
  have l2 : (∫ x : Mt k r, RdV (hpart2 (Hpk k r) Z) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      (1 / (2 * Complex.I)) * ((∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) *
        star (f₂ (Matrix.of x)) ∂μ) + ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_add iA iB, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR2 f₁ h₁.1 _ hx]
    ring
  have r2 : (∫ x : Mt k r, f₁ (Matrix.of x) * star (RdV (hpart2 (Hpk k r) Z) f₂ (Matrix.of x)) ∂μ) =
      -(1 / (2 * Complex.I)) * ((∫ x : Mt k r, f₁ (Matrix.of x) *
        star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ) +
          ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ) := by
    rw [← integral_add iC iD, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hR2 f₂ h₂.1 _ hx, star_div₀, star_add, star_mul', star_ofNat, Complex.star_def, Complex.conj_I]
    field_simp
  rw [l1, r1] at s1
  rw [l2, r2] at s2
  show (∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
    ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ
  set A := ∫ x : Mt k r, EH k r (posL k r i a) (posL k r i b) f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ
  set B := ∫ x : Mt k r, Ψ f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ
  set C := ∫ x : Mt k r, f₁ (Matrix.of x) * star (EH k r (posL k r i a) (posL k r i b) f₂ (Matrix.of x)) ∂μ
  set D := ∫ x : Mt k r, f₁ (Matrix.of x) * star (Ψ f₂ (Matrix.of x)) ∂μ
  have hk : (1 / (2 * Complex.I) : ℂ) ≠ 0 := by simp
  have e2 : A + B = C + D := mul_left_cancel₀ hk (by rw [s2]; ring)
  linear_combination s1 + (1 / 2 : ℂ) * e2

end PI.QnHermHaar
end
end

section
namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem qnHermHaar_of_alg (hA : HermAlgFrom) :
    RdSkew → StarMinor → ContractionsCovariant → MoveVec → MoveCov → YLeibniz → EabGlLev → EabPres → HermHaar :=
  qnHermHaar_of hA elementary_generator_adjoint elementary_generator_preserves_test multiplication_preserves_test test_function_pairing_integral conjugate_y_relation conjugate_x_relation restricted_gram_hermitian_involution glue_holds_var


end PI.QnHermHaar
end
