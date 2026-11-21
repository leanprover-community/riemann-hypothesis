import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SumFlatMapMap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.JKFinA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA

section
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_smooth (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : H}
    (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (dS σ X v) :=
  IsSmoothVecU.dS hσ hX hv

theorem dSW_cons (X : Matrix (Fin n) (Fin n) ℂ) (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) :
    dSW σ (X :: w) v = dS σ X (dSW σ w v) := rfl

theorem dSW_append (a b : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) :
    dSW σ (a ++ b) v = dSW σ a (dSW σ b v) := by
  induction a with
  | nil => rfl
  | cons X a ih => rw [List.cons_append, dSW_cons, dSW_cons, ih]

theorem dSW_smooth (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {v : H} (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (dSW σ w v) := by
  induction w with
  | nil => exact hv
  | cons X w ih =>
    rw [dSW_cons]
    exact IsSmoothVecU.dS hσ (hw X (by simp)) (ih (fun Y hY => hw Y (by simp [hY])))

theorem dSW_add (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {v v' : H} (hv : IsSmoothVecU ε σ v) (hv' : IsSmoothVecU ε σ v') :
    dSW σ w (v + v') = dSW σ w v + dSW σ w v' := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    have hw' : ∀ Y ∈ w, inG ε Y := fun Y hY => hw Y (by simp [hY])
    rw [dSW_cons, dSW_cons, dSW_cons, ih hw',
      dS_add_vec hσ (hw X (by simp)) (dSW_smooth hσ hw' hv) (dSW_smooth hσ hw' hv')]

theorem dSW_smul (c : ℂ) (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) :
    dSW σ w (c • v) = c • dSW σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih => rw [dSW_cons, dSW_cons, ih, dS_smul_vec]

theorem dSW_sub (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {v v' : H} (hv : IsSmoothVecU ε σ v) (hv' : IsSmoothVecU ε σ v') :
    dSW σ w (v - v') = dSW σ w v - dSW σ w v' := by
  have e : v - v' = v + (-1 : ℂ) • v' := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, dSW_add hσ hw hv (IsSmoothVecU.smul (-1) hv'), dSW_smul, neg_one_smul, sub_eq_add_neg]

private lemma exp_real_smul_mem_UJset_of_inG {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  have h : inG ε ((t : ℂ) • X) := by
    unfold inG at hX ⊢
    have e : ((t : ℂ) • X)ᴴ = (t : ℂ) • Xᴴ := by
      rw [Matrix.conjTranspose_smul]
      congr 1
      exact Complex.conj_ofReal t
    rw [e, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
  exact Formalism.REAL.f1alg_exp_inUJ ε _ h

private lemma inner_map_map_of_isURepOn (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (y v : H) : inner ℂ (σ g y) (σ g v) = inner ℂ y v := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.2.1 g hg }
  exact L.inner_map_map y v

theorem inner_dS_add (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {y v : H}
    (hy : IsSmoothVecU ε σ y) (hv : IsSmoothVecU ε σ v) :
    inner ℂ (dS σ X y) v + inner ℂ y (dS σ X v) = 0 := by
  have hf : HasDerivAt
      (fun t : ℝ => inner ℂ (σ (NormedSpace.exp ((t : ℂ) • X)) y) (σ (NormedSpace.exp ((t : ℂ) • X)) v))
      (inner ℂ (σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) y) (dS σ X v) +
        inner ℂ (dS σ X y) (σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) v)) 0 :=
    (hasDerivAt_dS hσ hX hy).inner ℂ (hasDerivAt_dS hσ hX hv)
  have hc : (fun t : ℝ => inner ℂ (σ (NormedSpace.exp ((t : ℂ) • X)) y)
      (σ (NormedSpace.exp ((t : ℂ) • X)) v)) = fun _ => inner ℂ y v := by
    funext t
    exact inner_map_map_of_isURepOn hσ (exp_real_smul_mem_UJset_of_inG hX t) y v
  rw [hc] at hf
  have h0 : σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    exact hσ.1.1
  rw [h0] at hf
  have h2 := hf.unique (hasDerivAt_const (0 : ℝ) (inner ℂ y v))
  simpa [add_comm] using h2

theorem inner_dSW (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {y v : H} (hy : IsSmoothVecU ε σ y) (hv : IsSmoothVecU ε σ v) :
    inner ℂ y (dSW σ w v) = (-1 : ℂ) ^ w.length * inner ℂ (dSW σ w.reverse y) v := by
  induction w generalizing y with
  | nil =>
    simp only [List.reverse_nil, List.length_nil, pow_zero, one_mul]
    rfl
  | cons X w ih =>
    have hX : inG ε X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inG ε Y := fun Y hY => hw Y (by simp [hY])
    have hXy : IsSmoothVecU ε σ (dS σ X y) := IsSmoothVecU.dS hσ hX hy
    have h1 := inner_dS_add hσ hX hy (dSW_smooth hσ hw' hv)
    have h2 : inner ℂ (dS σ X y) (dSW σ w v) =
        (-1 : ℂ) ^ w.length * inner ℂ (dSW σ w.reverse (dS σ X y)) v := ih (y := dS σ X y) hw' hXy
    have e : dSW σ [X] y = dS σ X y := rfl
    rw [dSW_cons, eq_neg_of_add_eq_zero_right h1, h2, List.reverse_cons, dSW_append, e,
      List.length_cons, pow_succ]
    ring

theorem inG_conj_K {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X) : inG ε (kᴴ * X * k) := by
  have hu : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  have hu' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
  have hc : k * Jm ε = Jm ε * k := hk.2
  have hc' : kᴴ * Jm ε = Jm ε * kᴴ := by
    calc kᴴ * Jm ε = kᴴ * (Jm ε * k) * kᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hu, Matrix.mul_one]
      _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hc]
      _ = Jm ε * kᴴ := by rw [← Matrix.mul_assoc, hu', Matrix.one_mul]
  unfold inG at hX ⊢
  have e : (kᴴ * X * k)ᴴ * Jm ε + Jm ε * (kᴴ * X * k) = kᴴ * (Xᴴ * Jm ε + Jm ε * X) * k := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_add, Matrix.add_mul]
    congr 1
    · simp only [Matrix.mul_assoc, hc]
    · simp only [← Matrix.mul_assoc, hc']
  rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem Kset_mul_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k * kᴴ = 1 ∧ kᴴ * k = 1 := by
  exact ⟨Matrix.mem_unitaryGroup_iff.mp hk.1, Matrix.mem_unitaryGroup_iff'.mp hk.1⟩

theorem dS_conj (hσ : IsURepOn (UJset ε) σ) {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X)
    {v : H} (hv : IsSmoothVecU ε σ v) : dS σ X (σ k v) = σ k (dS σ (kᴴ * X * k) v) := by
  obtain ⟨hu, hu'⟩ := Kset_mul_conj hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hu'
  have hunit : IsUnit k := (Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse hu')
  have hkU : k ∈ UJset ε := by
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu', Matrix.one_mul]
  have hY : inG ε (kᴴ * X * k) := inG_conj_K hk hX
  have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (σ k v)) =
      fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • (kᴴ * X * k))) v) := by
    funext t
    have he : NormedSpace.exp ((t : ℂ) • X) * k = k * NormedSpace.exp ((t : ℂ) • (kᴴ * X * k)) := by
      have h1 : (t : ℂ) • (kᴴ * X * k) = k⁻¹ * ((t : ℂ) • X) * k := by
        rw [hinv, Matrix.mul_smul, Matrix.smul_mul]
      rw [h1, Matrix.exp_conj' k _ hunit, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu,
        Matrix.one_mul]
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (exp_real_smul_mem_UJset_of_inG hX t) _ hkU, he,
      hσ.1.2 _ hkU _ (exp_real_smul_mem_UJset_of_inG hY t), ContinuousLinearMap.comp_apply]
  have hd := hasDerivAt_dS hσ hY hv
  have hd2 : HasDerivAt (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • (kᴴ * X * k))) v))
      (σ k (dS σ (kᴴ * X * k) v)) 0 :=
    ((σ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  rw [show dS σ X (σ k v) = deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (σ k v)) 0 from rfl,
    hfun]
  exact hd2.deriv

theorem dSW_conj (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X) {v : H} (hv : IsSmoothVecU ε σ v) :
    dSW σ w (σ k v) = σ k (dSW σ (w.map fun X => kᴴ * X * k) v) := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    have hX : inG ε X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inG ε Y := fun Y hY => hw Y (by simp [hY])
    have hm : ∀ Y ∈ w.map (fun X => kᴴ * X * k), inG ε Y := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inG_conj_K hk (hw' Z hZ)
    rw [List.map_cons, dSW_cons, dSW_cons, ih hw', dS_conj hσ hk hX (dSW_smooth hσ hm hv)]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem inG_rsum {ι : Type*} (s : Finset ι) (r : ι → ℝ) (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i ∈ s, inG ε (X i)) : inG ε (∑ i ∈ s, (r i : ℂ) • X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.inG_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact smc_inG_add (smc_inG_rsmul (hX a (Finset.mem_insert_self a s)) (r a))
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

theorem dS_rsum (hσ : IsURepOn (UJset ε) σ) {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (X : ι → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ i ∈ s, inG ε (X i)) {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ (∑ i ∈ s, (r i : ℂ) • X i) v = ∑ i ∈ s, (r i : ℂ) • dS σ (X i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.dS_zero_mat (σ := σ) v
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, inG ε (X i) := fun i hi => hX i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, dS_add_smul hσ (inG_rsum s r X hs)
      (hX a (Finset.mem_insert_self a s)) (r a) hv, ih hs, add_comm]

theorem dS_vsum (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → H) (hv : ∀ i ∈ s, IsSmoothVecU ε σ (v i)) :
    dS σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dS σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dS_smul_vec (σ := σ) 0 X 0
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsSmoothVecU ε σ (v i) := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hsum : IsSmoothVecU ε σ (∑ i ∈ s, c i • v i) := by
      clear ih
      induction s using Finset.induction_on with
      | empty => simpa using (isSmoothVecU_zero : IsSmoothVecU ε σ (0 : H))
      | insert b t hb ih2 =>
        rw [Finset.sum_insert hb]
        exact ((hs b (Finset.mem_insert_self b t)).smul (c b)).add
          (ih2 (fun h => ha (Finset.mem_insert_of_mem h)) (fun i hi => hv i (by
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)))
            (fun i hi => hs i (Finset.mem_insert_of_mem hi)))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dS_add_vec hσ hX ((hv a (Finset.mem_insert_self a s)).smul _)
      hsum, dS_smul_vec, ih hs]

theorem inG_expand {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    Y = ∑ p : (Fin n × Fin n) × Bool, ((cond p.2 (Y p.1.1 p.1.2).re (-(Y p.1.1 p.1.2).im) : ℝ) : ℂ) •
      cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1)) := by
  classical
  have hY1 : S7.cpart1 ε Y = Y := ((smc_cpart Y).2.2.2 hY).1
  set L : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ :=
    { toFun := S7.cpart1 ε, map_zero' := by simpa using smc_cpart1_real (ε := ε) 0 0,
      map_add' := smc_cpart1_add }
  have hdec : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • Matrix.single p.1 p.2 1 +
      ((Y p.1 p.2).im : ℂ) • (Complex.I • Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    rw [smul_smul, ← add_smul, Complex.re_add_im, Matrix.smul_single, smul_eq_mul, mul_one]
  have h2 : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • S7.cpart1 ε (Matrix.single p.1 p.2 1) +
      ((-(Y p.1 p.2).im : ℝ) : ℂ) • S7.cpart2 ε (Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [← hY1, hdec]
    change L (∑ p : Fin n × Fin n, _) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    change S7.cpart1 ε _ = _
    rw [smc_cpart1_add, smc_cpart1_real, smc_cpart1_real, smc_cpart1_I, Complex.ofReal_neg, smul_neg, neg_smul]
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_bool]
  simp only [cond_true, cond_false]

def FinCont (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (z : S7.KG ε → H) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → S7.KG ε → ℂ) (v : ι → H),
    (∀ i, Continuous (d i)) ∧ (∀ i, IsSmoothVecU ε σ (v i)) ∧ ∀ k, z k = ∑ i, d i k • v i

theorem finCont_step (hσ : IsURepOn (UJset ε) σ) {z : S7.KG ε → H} (hz : FinCont ε σ z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    FinCont ε σ (fun k => dS σ ((S7.toMK k)ᴴ * X * S7.toMK k) (z k)) := by
  classical
  obtain ⟨ι, _, d, v, hd, hv, hz⟩ := hz
  set Y : S7.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => (S7.toMK k)ᴴ * X * S7.toMK k
  have hYc : Continuous Y := by
    have hc := S7.IdA.continuous_toMK (ε := ε)
    exact (hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc
  have hYg : ∀ k, inG ε (Y k) := fun k => inG_conj_K k.2 hX
  set B : (Fin n × Fin n) × Bool → Matrix (Fin n) (Fin n) ℂ := fun p =>
    cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1))
  have hB : ∀ p, inG ε (B p) := by
    rintro ⟨q, _ | _⟩
    · exact (smc_cpart _).2.1
    · exact (smc_cpart _).1
  set r : S7.KG ε → (Fin n × Fin n) × Bool → ℝ := fun k p =>
    cond p.2 (Y k p.1.1 p.1.2).re (-(Y k p.1.1 p.1.2).im)
  refine ⟨ι × ((Fin n × Fin n) × Bool), inferInstance, fun q k => d q.1 k * (r k q.2 : ℂ),
    fun q => dS σ (B q.2) (v q.1), fun q => ?_, fun q => dS_smooth hσ (hB q.2) (hv q.1), fun k => ?_⟩
  · refine (hd q.1).mul (Complex.continuous_ofReal.comp ?_)
    have hent : Continuous fun k => Y k q.2.1.1 q.2.1.2 :=
      (continuous_apply q.2.1.2).comp ((continuous_apply q.2.1.1).comp hYc)
    rcases q with ⟨i, q, _ | _⟩
    · exact (Complex.continuous_im.comp hent).neg
    · exact Complex.continuous_re.comp hent
  · show dS σ (Y k) (z k) = _
    rw [hz k, dS_vsum hσ (hYg k) _ _ _ fun i _ => hv i, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [inG_expand (hYg k)]
    rw [dS_rsum hσ _ _ _ (fun p _ => hB p) (hv i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only [r]
    rw [smul_smul, mul_comm]

theorem finCont_dSW (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {u : H} (hu : IsSmoothVecU ε σ u) :
    FinCont ε σ (fun k => dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u) := by
  induction w with
  | nil => exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => u, fun _ => continuous_const, fun _ => hu,
      fun k => by simp [dSW]⟩
  | cons X w ih =>
    exact finCont_step hσ (ih fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (hw X List.mem_cons_self)

theorem continuous_dSW_orbit (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)}
    (hw : ∀ X ∈ w, inG ε X) {u : H} (hu : IsSmoothVecU ε σ u) :
    Continuous fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u) := by
  obtain ⟨ι, _, d, v, hd, -, hz⟩ := finCont_dSW hσ hw hu
  have e : (fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u)) =
      fun k => ∑ i, d i k • σ (S7.toMK k) (v i) := by
    funext k
    rw [dSW_conj hσ (k := S7.toMK k) k.2 hw hu, show dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u = _ from hz k, map_sum]
    simp only [map_smul]
  rw [e]
  refine continuous_finsetSum _ fun i _ => (hd i).smul ?_
  exact (hσ.2.2 (v i)).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2
end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

theorem approx_id {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hsep : (Mult1.Down.KF.finAlg K).SeparatesPoints) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (F : ι → K → E) (hF : ∀ i, Continuous (F i)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ α : C(K, ℂ), Mult1.Down.KF.Fin2 α ∧ ∀ i, ‖∫ k, α k • F i k ∂μ - F i 1‖ < δ := by
  classical
  have hint : ∀ (a : C(K, ℂ)) i, Integrable (fun k => a k • F i k) μ := fun a i =>
    integrableOn_univ.mp ((a.continuous.smul (hF i)).continuousOn.integrableOn_compact isCompact_univ)

  set U : Set K := ⋂ i, {k | ‖F i k - F i 1‖ < δ / 3}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt ((hF i).sub continuous_const).norm continuous_const
  have h1U : (1 : K) ∈ U := mem_iInter.2 fun i => by simp [hδ]

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := (1 : K)))
    hU.isClosed_compl (disjoint_singleton_left.2 fun h => h h1U)
  set b : K → ℝ := fun k => 1 - f k
  have hbc : Continuous b := continuous_const.sub f.continuous
  have hb0 : ∀ k, 0 ≤ b k := fun k => by simp only [b]; linarith [(hf01 k).2]
  have hb1 : b 1 = 1 := by simp only [b]; rw [hf0 (mem_singleton 1)]; simp
  have hbU : ∀ k, k ∉ U → b k = 0 := fun k hk => by simp only [b]; rw [hf1 hk]; simp
  have hbcs : HasCompactSupport b := isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  have hcpos : 0 < ∫ k, b k ∂μ :=
    hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbcs hb0 (by rw [hb1]; exact one_ne_zero)
  set c := ∫ k, b k ∂μ
  have hbint : Integrable b μ := integrableOn_univ.mp (hbc.continuousOn.integrableOn_compact isCompact_univ)
  set β : C(K, ℂ) := ⟨fun k => ((b k / c : ℝ) : ℂ), Complex.continuous_ofReal.comp (hbc.div_const c)⟩
  have hβ : ∀ i, ‖∫ k, β k • F i k ∂μ - F i 1‖ ≤ δ / 3 := by
    intro i
    have hβ1 : ∫ k, β k • F i 1 ∂μ = F i 1 := by
      rw [integral_smul_const]
      have : ∫ k, β k ∂μ = 1 := by
        show ∫ k, ((b k / c : ℝ) : ℂ) ∂μ = 1
        rw [integral_complex_ofReal, integral_div]
        rw [show ∫ k, b k ∂μ = c from rfl, div_self hcpos.ne', Complex.ofReal_one]
      rw [this, one_smul]
    have hc : Integrable (fun k => β k • F i 1) μ :=
      integrableOn_univ.mp ((β.continuous.smul continuous_const).continuousOn.integrableOn_compact isCompact_univ)
    rw [← hβ1, ← integral_sub (hint β i) hc]
    calc ‖∫ k, (β k • F i k - β k • F i 1) ∂μ‖ ≤ ∫ k, b k / c * (δ / 3) ∂μ := by
          refine norm_integral_le_of_norm_le ((hbint.div_const c).mul_const _) (Filter.Eventually.of_forall fun k => ?_)
          rw [← smul_sub, norm_smul]
          by_cases hk : k ∈ U
          · have := (mem_iInter.1 hk) i
            simp only [mem_ofPred_eq] at this
            have hn : ‖β k‖ = b k / c := by
              show ‖((b k / c : ℝ) : ℂ)‖ = _
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb0 k) hcpos.le)]
            rw [hn]
            exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hb0 k) hcpos.le)
          · have hn : β k = 0 := by show ((b k / c : ℝ) : ℂ) = 0; rw [hbU k hk]; simp
            rw [hn, norm_zero, zero_mul, hbU k hk, zero_div, zero_mul]
      _ = δ / 3 := by
          rw [integral_mul_const, integral_div]
          rw [show (∫ k, b k ∂μ) = c from rfl, div_self hcpos.ne', one_mul]

  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_finsetSum Finset.univ fun i _ => (hF i).norm).continuousOn
  have hMi : ∀ i k, ‖F i k‖ ≤ M := fun i k => by
    have := hM k (mem_univ k)
    rw [Real.norm_eq_abs] at this
    refine le_trans ?_ ((le_abs_self _).trans this)
    exact Finset.single_le_sum (f := fun i => ‖F i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  set R := |M| * μ.real univ + 1
  have hR : 0 < R := by positivity
  have hη : 0 < δ / 3 / R := by positivity
  have hmem : β ∈ closure ((Mult1.Down.KF.finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
    have : β ∈ (Mult1.Down.KF.finAlg K).topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨α, hα, hαβ⟩ := Metric.mem_closure_iff.1 hmem _ hη
  refine ⟨α, hα, fun i => ?_⟩
  have hdiff : ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ ≤ δ / 3 / R * |M| * μ.real univ := by
    rw [← integral_sub (hint α i) (hint β i)]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [← sub_smul, norm_smul]
    have h1 : ‖α k - β k‖ ≤ δ / 3 / R := by
      have := (β - α).norm_coe_le_norm k
      rw [dist_eq_norm] at hαβ
      rw [norm_sub_rev]
      exact this.trans hαβ.le
    exact mul_le_mul h1 ((hMi i k).trans (le_abs_self M)) (norm_nonneg _) hη.le
  have hsmall : δ / 3 / R * |M| * μ.real univ < δ / 3 := by
    rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ hR]
    have : |M| * μ.real univ < R := by simp [R]
    nlinarith [measureReal_nonneg (μ := μ) (s := univ), abs_nonneg M]
  calc ‖∫ k, α k • F i k ∂μ - F i 1‖
      ≤ ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ + ‖∫ k, β k • F i k ∂μ - F i 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ / 3 + δ / 3 := add_lt_add_of_lt_of_le (hdiff.trans_lt hsmall) (hβ i)
    _ < δ := by linarith

theorem finAlg_sep_KG {n : ℕ} (ε : Fin n → Bool) : (Mult1.Down.KF.finAlg (S7.KG ε)).SeparatesPoints := by
  intro k k' hne
  have hne' : S7.toMK k ≠ S7.toMK k' := fun h => hne (Subtype.ext (Subtype.ext (Units.ext h)))
  obtain ⟨i, j, hij⟩ : ∃ i j, S7.toMK k i j ≠ S7.toMK k' i j := by
    by_contra hc
    push Not at hc
    exact hne' (Matrix.ext hc)
  have hcont : ∀ a b : Fin n, Continuous fun κ : S7.KG ε => S7.toMK κ a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp S7.IdA.continuous_toMK)
  refine ⟨_, ⟨⟨fun κ => S7.toMK κ i j, hcont i j⟩, ?_, rfl⟩, hij⟩
  refine ⟨Fin n, inferInstance, fun l k₀ => S7.toMK k₀ i l, fun l => ⟨fun κ => S7.toMK κ l j, hcont l j⟩,
    fun k₀ κ => ?_⟩
  show (S7.toMK k₀ * S7.toMK κ) i j = _
  rw [Matrix.mul_apply]
  rfl

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem intK {E : Type*} [NormedAddCommGroup E] {f : S7.KG ε → E} (hf : Continuous f) :
    Integrable f (S7.muK ε) := by
  have := S7.compactSpace_KG ε
  have : IsFiniteMeasureOnCompacts (S7.muK ε) := by unfold S7.muK; infer_instance
  exact integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem orbitK_continuous (hσ : IsURepOn (UJset ε) σ) (u : H) :
    Continuous fun k : S7.KG ε => σ (S7.toMK k) u :=
  (hσ.2.2 u).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2

theorem toMK_mul_apply (hσ : IsURepOn (UJset ε) σ) (k₀ k : S7.KG ε) (u : H) :
    σ (S7.toMK (k₀ * k)) u = σ (S7.toMK k₀) (σ (S7.toMK k) u) := by
  rw [show S7.toMK (k₀ * k) = S7.toMK k₀ * S7.toMK k from rfl,
    hσ.1.2 _ (smd_inUJ_of_Kset k₀.2) _ (smd_inUJ_of_Kset k.2)]
  rfl

theorem kfin_integral (hσ : IsURepOn (UJset ε) σ) (u : H) {α : C(S7.KG ε, ℂ)} (hα : Mult1.Down.KF.Fin2 α) :
    Formalism.MainNotions.S.IsKFin ε σ (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)) := by
  classical
  have := S7.compactSpace_KG ε
  set x := ∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)
  obtain ⟨ι, _, a, β, hab⟩ := hα
  have hint : ∀ γ : C(S7.KG ε, ℂ), Integrable (fun k => γ k • σ (S7.toMK k) u) (S7.muK ε) := fun γ =>
    intK (γ.continuous.smul (orbitK_continuous hσ u))
  set T : Submodule ℂ H := Submodule.span ℂ (Set.range fun i => ∫ κ, β i κ • σ (S7.toMK κ) u ∂(S7.muK ε))
  have hT : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have key : ∀ k₀ : S7.KG ε, σ (S7.toMK k₀) x ∈ T := by
    intro k₀
    have e1 : σ (S7.toMK k₀) x = ∫ k, α k • σ (S7.toMK (k₀ * k)) u ∂(S7.muK ε) := by
      rw [← (σ (S7.toMK k₀)).integral_comp_comm (hint α)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_smul, toMK_mul_apply hσ]
    set f : S7.KG ε → H := fun κ => α (k₀⁻¹ * κ) • σ (S7.toMK κ) u
    have e2 : ∫ k, α k • σ (S7.toMK (k₀ * k)) u ∂(S7.muK ε) = ∫ κ, f κ ∂(S7.muK ε) := by
      rw [← integral_mul_left_eq_self f k₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [f, inv_mul_cancel_left]
    have e3 : ∫ κ, f κ ∂(S7.muK ε) =
        ∑ i, a i k₀⁻¹ • ∫ κ, β i κ • σ (S7.toMK κ) u ∂(S7.muK ε) := by
      have : f = fun κ => ∑ i, a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u) := by
        funext κ
        simp only [f, hab, Finset.sum_smul, smul_smul]
      rw [this]
      show ∫ κ, ∑ i, a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u) ∂(S7.muK ε) = _
      rw [integral_finsetSum Finset.univ (f := fun i κ => a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u))
        (fun i _ => (hint (β i)).smul (a i k₀⁻¹))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_smul]
    rw [e1, e2, e3]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set S : Submodule ℂ H := Submodule.span ℂ (Set.range fun k : S7.KG ε => σ (S7.toMK k) x)
  have hST : S ≤ T := Submodule.span_le.2 fun v ⟨k, hk⟩ => hk ▸ key k
  refine ⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩
  · have : σ (S7.toMK (1 : S7.KG ε)) x = x := by
      rw [show S7.toMK (1 : S7.KG ε) = 1 from rfl, hσ.1.1]
      rfl
    exact this ▸ Submodule.subset_span ⟨1, rfl⟩
  · intro g hg v hv
    obtain ⟨k', rfl⟩ := ffa_Kset (ε := ε) hg
    have hle : S ≤ S.comap (σ (S7.toMK k')) := Submodule.span_le.2 fun w ⟨k, hk⟩ => by
      rw [← hk]
      show σ (S7.toMK k') (σ (S7.toMK k) x) ∈ S
      rw [← toMK_mul_apply hσ]
      exact Submodule.subset_span ⟨k' * k, rfl⟩
    exact hle hv

theorem dSW_integral (hσ : IsURepOn (UJset ε) σ)
    (hsep : ∀ z : H, (∀ y, IsSmoothVecU ε σ y → inner ℂ y z = 0) → z = 0)
    {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X) {u : H} (hu : IsSmoothVecU ε σ u)
    (α : C(S7.KG ε, ℂ)) (hx : IsSmoothVecU ε σ (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε))) :
    dSW σ w (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)) =
      ∫ k, α k • dSW σ w (σ (S7.toMK k) u) ∂(S7.muK ε) := by
  have := S7.compactSpace_KG ε
  have hint1 : Integrable (fun k => α k • σ (S7.toMK k) u) (S7.muK ε) :=
    intK (α.continuous.smul (orbitK_continuous hσ u))
  have hint2 : Integrable (fun k => α k • dSW σ w (σ (S7.toMK k) u)) (S7.muK ε) :=
    intK (α.continuous.smul (continuous_dSW_orbit hσ hw hu))
  refine sub_eq_zero.1 (hsep _ fun y hy => ?_)
  have hwr : ∀ X ∈ w.reverse, inG ε X := fun X hX => hw X (List.mem_reverse.1 hX)
  rw [inner_sub_right, sub_eq_zero, inner_dSW hσ hw hy hx, ← integral_inner hint1, ← integral_inner hint2,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_dSW hσ hw hy (IsSmoothVecU.kStable hσ k.2 hu)]
  ring

section abelian₂

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem sigLam_smooth_of_genSub {y : smD ε (rreg ε)}
    (hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀) :
    IsSmoothVecU ε (sigLam ε Ψ v₀) (⟨(y : L2 ε), hyH⟩ : Hlam ε Ψ v₀) := by
  have h := (mem_smD_iff ε (rreg ε) (y : L2 ε)).1 y.2
  exact smoothOnGV_clm (Hlam ε Ψ v₀).orthogonalProjectionOnto h

theorem sigLam_sep (z : Hlam ε Ψ v₀)
    (hz : ∀ y, IsSmoothVecU ε (sigLam ε Ψ v₀) y → inner ℂ y z = 0) : z = 0 := by
  have hcl : IsClosed {v : L2 ε | inner ℂ v (z : L2 ε) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : (((genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)).map (smD ε (rreg ε)).subtype : Submodule ℂ (L2 ε)) :
      Set (L2 ε)) ⊆ {v : L2 ε | inner ℂ v (z : L2 ε) = 0} := by
    rintro v ⟨y, hy, rfl⟩
    have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ :=
      Submodule.le_topologicalClosure _ ⟨y, hy, rfl⟩
    have := hz _ (sigLam_smooth_of_genSub hyH)
    rwa [Submodule.coe_inner] at this
  have hzc : (z : L2 ε) ∈ closure (((genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)).map (smD ε (rreg ε)).subtype :
      Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    have := z.2
    unfold Hlam closGen at this
    rwa [← Submodule.topologicalClosure_coe]
  have h0 : inner ℂ (z : L2 ε) (z : L2 ε) = (0 : ℂ) := hcl.closure_subset_iff.2 hsub hzc
  exact Subtype.ext (inner_self_eq_zero.1 h0)

end abelian₂

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem kfin_mem_genSub {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (x : Hlam ε Ψ v₀) (hx : Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x) :
    ∃ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ((y : smD ε (rreg ε)) : L2 ε) = (x : L2 ε) := by
  obtain ⟨S, hSf, hxS, hSK⟩ := hx
  have h := sigLam_kfin hgap hP hv₀ S hSf hSK hxS
  simp only [kfinLam, Submodule.mem_comap, Submodule.mem_map] at h
  obtain ⟨y, hy, hyx⟩ := h
  exact ⟨y, hy, hyx⟩

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem exists_kfin_near {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X)
    (u : Hlam ε Ψ v₀) (hu : IsSmoothVecU ε (sigLam ε Ψ v₀) u) {e : ℝ} (he : 0 < e) :
    ∃ x : Hlam ε Ψ v₀, Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x ∧ nuJ (sigLam ε Ψ v₀) Ws (u - x) < e := by
  have := S7.compactSpace_KG ε
  have : MeasureTheory.IsFiniteMeasure (S7.muK ε) := by unfold S7.muK; infer_instance
  have : (S7.muK ε).IsOpenPosMeasure := by unfold S7.muK; infer_instance
  have hσ : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := sigLam_isURepOn hgap hP hv₀
  have hWg : ∀ i : Fin Ws.length, ∀ X ∈ Ws.get i, inG ε X := fun i => hWs _ (List.get_mem Ws i)
  obtain ⟨α, hα, hαF⟩ := approx_id (S7.muK ε) (finAlg_sep_KG ε)
    (fun (i : Fin Ws.length) (k : S7.KG ε) => dSW (sigLam ε Ψ v₀) (Ws.get i) (sigLam ε Ψ v₀ (S7.toMK k) u))
    (fun i => continuous_dSW_orbit hσ (hWg i) hu) (δ := e / (Ws.length + 1)) (by positivity)
  obtain ⟨x, hxdef⟩ : ∃ x : Hlam ε Ψ v₀, x = ∫ k, α k • sigLam ε Ψ v₀ (S7.toMK k) u ∂(S7.muK ε) := ⟨_, rfl⟩
  have hK : Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x := by rw [hxdef]; exact kfin_integral hσ u hα
  obtain ⟨y, -, hyx⟩ := kfin_mem_genSub hlam hgap hP hv₀ x hK
  have hxs : IsSmoothVecU ε (sigLam ε Ψ v₀) x := by
    have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ := by rw [hyx]; exact x.2
    have h := sigLam_smooth_of_genSub (Ψ := Ψ) (v₀ := v₀) hyH
    rwa [show (⟨(y : L2 ε), hyH⟩ : Hlam ε Ψ v₀) = x from Subtype.ext hyx] at h
  refine ⟨x, hK, ?_⟩
  have hterm : ∀ w ∈ Ws, ‖dSW (sigLam ε Ψ v₀) w (u - x)‖ ≤ e / (Ws.length + 1) := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.get_of_mem hw
    have hxs' : IsSmoothVecU ε (sigLam ε Ψ v₀) (∫ k, α k • sigLam ε Ψ v₀ (S7.toMK k) u ∂(S7.muK ε)) := by
      rw [← hxdef]; exact hxs
    rw [dSW_sub hσ (hWg i) hu hxs, hxdef]
    erw [dSW_integral hσ (fun z hz => sigLam_sep z hz) (hWg i) hu α hxs']
    rw [norm_sub_rev]
    have h1 : sigLam ε Ψ v₀ (S7.toMK (1 : S7.KG ε)) u = u := by
      rw [show S7.toMK (1 : S7.KG ε) = 1 from rfl, hσ.1.1]
      rfl
    have h2 := hαF i
    beta_reduce at h2
    rw [h1] at h2
    exact h2.le
  unfold nuJ
  calc (Ws.map fun w => ‖dSW (sigLam ε Ψ v₀) w (u - x)‖).sum
      ≤ (Ws.map fun w => ‖dSW (sigLam ε Ψ v₀) w (u - x)‖).length • (e / (Ws.length + 1)) :=
        List.sum_le_card_nsmul _ _ fun r hr => by
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
          exact hterm w hw
    _ = (Ws.length : ℝ) * (e / (Ws.length + 1)) := by rw [List.length_map, nsmul_eq_mul]
    _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem exists_near_smooth {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X)
    (u : Hlam ε Ψ v₀) (hu : IsSmoothVecU ε (sigLam ε Ψ v₀) u) {e : ℝ} (he : 0 < e) :
    ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∃ hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀,
        nuJ (sigLam ε Ψ v₀) Ws (u - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) < e := by
  obtain ⟨x, hxK, hxe⟩ := exists_kfin_near hlam hgap hP hv₀ Ws hWs u hu he
  obtain ⟨y, hy, hyx⟩ := kfin_mem_genSub hlam hgap hP hv₀ x hxK
  have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ := by rw [hyx]; exact x.2
  refine ⟨y, hy, hyH, ?_⟩
  have hxy : (⟨((y : smD ε (rreg ε)) : L2 ε), hyH⟩ : Hlam ε Ψ v₀) = x := Subtype.ext hyx
  rw [hxy]
  exact hxe

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem nuJ_nonneg (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : 0 ≤ nuJ σ Ws v := by
  unfold nuJ
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 ha
  exact norm_nonneg _

theorem nuJ_cons_nil (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : nuJ σ ([] :: Ws) v = ‖v‖ + nuJ σ Ws v := by
  simp [nuJ, dSW]

theorem nuJ_le_add_of (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a b c : H) :
    ∀ Ws : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ w ∈ Ws, ‖dSW σ w a‖ ≤ ‖dSW σ w b‖ + ‖dSW σ w c‖) → nuJ σ Ws a ≤ nuJ σ Ws b + nuJ σ Ws c
  | [], _ => by simp [nuJ]
  | w :: Ws, h => by
    have h1 := h w List.mem_cons_self
    have h2 := nuJ_le_add_of σ a b c Ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    simp only [nuJ, List.map_cons, List.sum_cons] at h2 ⊢
    linarith

theorem NE_nonneg' {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : 0 ≤ NE E j x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

end Gen

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem dS_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (y : Hlam ε Ψ v₀) :
    ((dS (sigLam ε Ψ v₀) X y : Hlam ε Ψ v₀) : L2 ε) = dS (rreg ε) X (y : L2 ε) := by
  unfold dS
  set f : ℝ → Hlam ε Ψ v₀ := fun t => sigLam ε Ψ v₀ (NormedSpace.exp ((t : ℂ) • X)) y with hfdef
  have hf : (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (y : L2 ε)) = fun t => ((f t : Hlam ε Ψ v₀) : L2 ε) := by
    funext t
    rw [hfdef, sigLam_coe hgap hP hv₀ (exp_smul_mem_UJset hX t)]
  rw [hf]
  let Ir : Hlam ε Ψ v₀ →L[ℝ] L2 ε := ((Hlam ε Ψ v₀).subtypeL).restrictScalars ℝ
  let Pr : L2 ε →L[ℝ] Hlam ε Ψ v₀ := ((Hlam ε Ψ v₀).orthogonalProjectionOnto).restrictScalars ℝ
  by_cases hd : DifferentiableAt ℝ f 0
  · exact ((Ir.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hd.hasDerivAt).deriv).symm
  · have hd' : ¬ DifferentiableAt ℝ (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 := by
      intro h
      apply hd
      have h2 := Pr.differentiableAt.comp (0 : ℝ) h
      have e : (Pr ∘ fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) = f := by
        funext t
        exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (f t)
      rw [e] at h2
      exact h2
    have h0 : deriv f 0 = 0 := deriv_zero_of_not_differentiableAt hd
    have h1 : deriv (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 = 0 := deriv_zero_of_not_differentiableAt hd'
    exact (congrArg Subtype.val h0).trans h1.symm

theorem dSW_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ y : Hlam ε Ψ v₀,
      ((dSW (sigLam ε Ψ v₀) w y : Hlam ε Ψ v₀) : L2 ε) = dSW (rreg ε) w (y : L2 ε)
  | [], _, _ => rfl
  | X :: w, hw, y => by
    simp only [dSW]
    rw [dS_sigLam_coe hgap hP hv₀ (hw X List.mem_cons_self),
      dSW_sigLam_coe hgap hP hv₀ w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) y]

theorem nuJ_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (y : Hlam ε Ψ v₀) :
    nuJ (rreg ε) Ws (y : L2 ε) = nuJ (sigLam ε Ψ v₀) Ws y := by
  unfold nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [← dSW_sigLam_coe hgap hP hv₀ w (hWs w hw) y, Submodule.coe_norm]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem decBoundJ_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (m N : ℕ)
    (hM : ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m * ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ ≤
          C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y) :
    DecBoundJ ε (sigLam ε Ψ v₀) m N := by
  obtain ⟨C, hC⟩ := hM
  obtain ⟨Ws, C', hWs, hNE⟩ := NE_le_nuJ (rreg_isURepOn ε) N
  have hU : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := sigLam_isURepOn hgap hP hv₀
  have hWsG : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  have hVs : ∀ w ∈ ([] :: Ws), w.length ≤ N ∧ ∀ X ∈ w, inG ε X := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · simp
    · exact hWs w hw
  have hVsG : ∀ w ∈ ([] :: Ws), ∀ X ∈ w, inG ε X := fun w hw => (hVs w hw).2
  have hnn : ∀ z : Hlam ε Ψ v₀, 0 ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := fun z =>
    nuJ_nonneg _ _ _
  have hnorm : ∀ z : Hlam ε Ψ v₀, ‖z‖ ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := by
    intro z
    rw [nuJ_cons_nil]
    linarith [nuJ_nonneg (sigLam ε Ψ v₀) Ws z]
  have hC₁ : 0 ≤ max C' 0 := le_max_right _ _
  have hK : 0 ≤ max C 0 * max C' 0 * max C' 0 :=
    mul_nonneg (mul_nonneg (le_max_right _ _) hC₁) hC₁
  have hNE' : ∀ (x : smD ε (rreg ε)) (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      NE (smE ε (rreg ε)) N x ≤
        max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) := by
    intro x hx
    have h1 := hNE x
    have h2 : nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) =
        nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_sigLam_coe hgap hP hv₀ hWsG (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)
    have h3 := nuJ_nonneg (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)
    have h4 : nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) =
        ‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
          nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_cons_nil _ _ _
    rw [h4, ← h2]
    calc NE (smE ε (rreg ε)) N x ≤ C' * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) := h1
      _ ≤ max C' 0 * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max C' 0 * (‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
            nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hC₁
  have hfin : ∀ (x : smD ε (rreg ε)), x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      ∀ (y : smD ε (rreg ε)), y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hy : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀), ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m *
            ‖inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
              (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩)‖ ≤
          max C 0 * max C' 0 * max C' 0 *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ := by
    intro x hxg hx y hyg hy g hg
    have he : inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
        (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) =
        inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε)) := by
      rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ hg]
    rw [he]
    have hb := hC x hxg y hyg g hg
    have hx0 := NE_nonneg' (smE ε (rreg ε)) N x
    have hy0 := NE_nonneg' (smE ε (rreg ε)) N y
    have hxb := hNE' x hx
    have hyb := hNE' y hy
    calc _ ≤ C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y := hb
      _ ≤ max C 0 * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0) hy0
      _ ≤ max C 0 * (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) *
            (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩) := by
          have hm := le_max_right C 0
          exact mul_le_mul (mul_le_mul_of_nonneg_left hxb hm) hyb hy0
            (mul_nonneg hm (mul_nonneg hC₁ (hnn _)))
      _ = _ := by ring
  refine ⟨max C 0 * max C' 0 * max C' 0, [] :: Ws, hVs, ?_⟩
  intro u v hu hv g hg
  have hA : 0 ≤ Real.sqrt (S7.hs g) ^ m := pow_nonneg (Real.sqrt_nonneg _) _
  have hiso : ∀ z : Hlam ε Ψ v₀, ‖sigLam ε Ψ v₀ g z‖ = ‖z‖ := fun z => hU.2.1 g hg z
  have hnear : ∀ (w : Hlam ε Ψ v₀), IsSmoothVecU ε (sigLam ε Ψ v₀) w → ∀ (e : ℝ), 0 < e →
      ∃ (x : smD ε (rreg ε)) (_ : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
        (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
        ‖w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩‖ ≤ e ∧
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ ≤
          nuJ (sigLam ε Ψ v₀) ([] :: Ws) w + e := by
    intro w hw e he
    obtain ⟨x, hxg, hx, hlt⟩ := exists_near_smooth hlam hgap hP hv₀ ([] :: Ws) hVsG w hw he
    refine ⟨x, hxg, hx, (hnorm _).trans hlt.le, ?_⟩
    have hxs := sigLam_smooth_of_genSub (ε := ε) (Ψ := Ψ) (v₀ := v₀) hx
    have htri := nuJ_le_add_of (sigLam ε Ψ v₀) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ w
      (w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) ([] :: Ws) (by
        intro W hW
        rw [dSW_sub hU (hVsG W hW) hw hxs]
        set a := dSW (sigLam ε Ψ v₀) W w
        set b := dSW (sigLam ε Ψ v₀) W ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩
        calc ‖b‖ = ‖a - (a - b)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _)
    linarith
  have hbound : ∀ e : ℝ, 0 < e →
      Real.sqrt (S7.hs g) ^ m * ‖inner ℂ v (sigLam ε Ψ v₀ g u)‖ ≤
        Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
          max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
            (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
    intro e he
    obtain ⟨x, hxg, hx, hux, hnx⟩ := hnear u hu e he
    obtain ⟨y, hyg, hy, hvy, hny⟩ := hnear v hv e he
    set x' : Hlam ε Ψ v₀ := ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ with hx'
    set y' : Hlam ε Ψ v₀ := ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ with hy'
    have hsplit : inner ℂ v (sigLam ε Ψ v₀ g u) =
        inner ℂ (v - y') (sigLam ε Ψ v₀ g u) +
          (inner ℂ y' (sigLam ε Ψ v₀ g (u - x')) + inner ℂ y' (sigLam ε Ψ v₀ g x')) := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : ‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ ≤ e * ‖u‖ := by
      calc _ ≤ ‖v - y'‖ * ‖sigLam ε Ψ v₀ g u‖ := norm_inner_le_norm _ _
        _ = ‖v - y'‖ * ‖u‖ := by rw [hiso]
        _ ≤ e * ‖u‖ := mul_le_mul_of_nonneg_right hvy (norm_nonneg _)
    have hy'n : ‖y'‖ ≤ ‖v‖ + e := by
      calc ‖y'‖ = ‖v - (v - y')‖ := by rw [sub_sub_cancel]
        _ ≤ ‖v‖ + ‖v - y'‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + e := by linarith
    have h2 : ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ ≤ (‖v‖ + e) * e := by
      calc _ ≤ ‖y'‖ * ‖sigLam ε Ψ v₀ g (u - x')‖ := norm_inner_le_norm _ _
        _ = ‖y'‖ * ‖u - x'‖ := by rw [hiso]
        _ ≤ (‖v‖ + e) * e := mul_le_mul hy'n hux (norm_nonneg _) (by linarith [norm_nonneg v])
    have h3 := hfin x hxg hx y hyg hy g hg
    have h3' : Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ ≤
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
      refine h3.trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left hnx hK) hny (hnn _)
        (mul_nonneg hK (by linarith [hnn u]))
    rw [hsplit]
    calc _ ≤ Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            (‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ + ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖)) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) hA
      _ = Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖) +
            Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA) h3'
  have hlim : Filter.Tendsto (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (max C 0 * max C' 0 * max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) u *
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) v)) := by
    have hc : Continuous (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e)) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun e he => hbound e he)

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
