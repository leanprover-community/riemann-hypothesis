import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant

section
noncomputable section

open scoped Matrix

namespace GlobalTheory.HaarLin

def TD (R : Type) [CommRing R] (κ : Type) [Fintype κ] [DecidableEq κ] : Submonoid (Matrix κ κ R) :=
  Submonoid.closure ({M | ∃ i j : κ, ∃ c : R, i ≠ j ∧ M = Matrix.transvection i j c} ∪
    {M | ∃ d : κ → Rˣ, M = Matrix.diagonal fun i => (d i : R)})

def HasStableRangeOne (R : Type) [CommRing R] : Prop := ∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)

end GlobalTheory.HaarLin

open NumberField MeasureTheory Matrix
open scoped NNReal ENNReal
namespace GlobalTheory.HaarLin

private lemma nnreal_eq_of_smul_addHaar_eq {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : X)
  have h1 : μ K ≠ 0 := (μ.measure_pos_of_mem_nhds hK0).ne'
  have h2 : μ K ≠ ∞ := hK.measure_lt_top.ne
  have h3 : (a • μ) K = (b • μ) K := by rw [h]
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h3
  exact_mod_cast (ENNReal.mul_left_inj h1 h2).1 h3

private lemma map_mul_lemma_2 {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)]
    (A B : Matrix κ κ R) (μ : Measure (κ → R)) :
    μ.map (fun x => (A * B) *ᵥ x) = (μ.map (fun x => B *ᵥ x)).map (fun x => A *ᵥ x) := by
  have hA : Measurable (fun x : κ → R => A *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hB : Measurable (fun x : κ → R => B *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  rw [Measure.map_map hA hB]
  congr 1
  funext x
  simp [Function.comp, Matrix.mulVec_mulVec]

private lemma exists_map_mulVec_eq_smul_of_invertible {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (P Q : Matrix κ κ R) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∃ c : ℝ≥0, ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → μ.map (fun x => P *ᵥ x) = c • μ := by
  let e : (κ → R) ≃+ (κ → R) :=
    { toFun := fun x => P *ᵥ x
      invFun := fun x => Q *ᵥ x
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, hQP]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, hPQ]
      map_add' := fun x y => Matrix.mulVec_add P x y }
  have he : Continuous (fun x : κ → R => P *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have he' : Continuous (fun x : κ → R => Q *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have key : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → (μ.map (fun x => P *ᵥ x)).IsAddHaarMeasure :=
    fun μ _ => e.isAddHaarMeasure_map μ he he'
  let μ₀ : Measure (κ → R) := Measure.addHaar
  haveI := key μ₀ inferInstance
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ₀.map (fun x => P *ᵥ x) = c • μ₀ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun μ hμ => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hc, smul_comm]

private lemma map_transvection_mulVec_addHaar_eq_self {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (i j : κ) (hij : i ≠ j) (c : R)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => transvection i j c *ᵥ x) = μ := by
  set D : Matrix κ κ R := diagonal (Function.update (1 : κ → R) i (-1)) with hD0
  have hD : D * D = 1 := by
    rw [hD0, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [Function.update_apply, hk]
  have hT : transvection i j c * transvection i j (-c) = 1 := by
    rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero]
  have hT' : transvection i j (-c) * transvection i j c = 1 := by
    rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]
  have hconj : D * transvection i j c * D = transvection i j (-c) := by
    have hji : j ≠ i := Ne.symm hij
    clear hD hT hT'
    ext a b
    simp only [hD0, Matrix.mul_diagonal, Matrix.diagonal_mul, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply]
    clear hD0
    split_ifs <;> grind
  have hone : μ.map (fun x => (1 : Matrix κ κ R) *ᵥ x) = μ := by
    simp only [Matrix.one_mulVec, Measure.map_id']
  obtain ⟨a, ha⟩ := exists_map_mulVec_eq_smul_of_invertible D D hD hD
  obtain ⟨t, ht⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT hT'
  obtain ⟨t', ht'⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT' hT
  have haa : a * a = 1 := by
    have h := map_mul_lemma_2 D D μ
    rw [hD, hone, ha μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have htt : t' * t = 1 := by
    have h := map_mul_lemma_2 (transvection i j c) (transvection i j (-c)) μ
    rw [hT, hone, ht' μ inferInstance, Measure.map_smul, ht μ inferInstance, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have hcj : t' = a * t * a := by
    have h := map_mul_lemma_2 (D * transvection i j c) D μ
    rw [hconj, ht' μ inferInstance, ha μ inferInstance, Measure.map_smul, map_mul_lemma_2,
      ht μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ h
  have h2 : t * t = 1 := by
    rw [hcj] at htt
    calc t * t = t * t * (a * a) := by rw [haa, mul_one]
      _ = a * t * a * t := by ring
      _ = 1 := htt
  have h3 : t = 1 := by
    have h4 : (t : ℝ) * t = 1 := by exact_mod_cast h2
    apply NNReal.eq
    have h5 := t.coe_nonneg
    push_cast
    nlinarith
  rw [ht μ inferInstance, h3, one_smul]

private lemma map_diagonal_mulVec_eq_inv_prod_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [inst : MeasurableSpace (κ → R)] [hb : BorelSpace (κ → R)] (d : κ → Rˣ)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • μ := by
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩
  have e : inst = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq (κ → R) _ inst hb).trans
      (@BorelSpace.measurable_eq (κ → R) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have h1 : ∀ u : Rˣ, (Measure.addHaar : Measure R).map (fun y => (u : R) * y) =
      (distribHaarChar R u)⁻¹ • Measure.addHaar := by
    intro u
    have hu : (fun y : R => (u : R) * y) = fun y => (DomMulAct.mk.symm (DomMulAct.mk u⁻¹)⁻¹ : Rˣ) • y := by
      funext y
      simp [Units.smul_def]
    rw [hu]
    change DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R) = _
    rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R)) Measure.addHaar,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  set ν : Measure (κ → R) := Measure.pi (fun _ => (Measure.addHaar : Measure R)) with hν0
  have hν : ν.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • ν := by
    have hf : (fun x : κ → R => diagonal (fun i => (d i : R)) *ᵥ x) = fun x i => (d i : R) * x i := by
      funext x i
      exact mulVec_diagonal _ _ _
    haveI : ∀ i, SigmaFinite ((Measure.addHaar : Measure R).map (fun y => (d i : R) * y)) := fun i => by
      rw [h1]; infer_instance
    rw [hf, hν0, Measure.pi_map_pi (f := fun i y => (d i : R) * y)
      (fun i => (continuous_mul_left (d i : R)).measurable.aemeasurable)]
    simp_rw [h1]
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← Finset.prod_inv_distrib,
      Finset.prod_mul_distrib, ENNReal.coe_finset_prod]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hν, smul_comm]

private lemma exists_unit_det_map_mulVec_haar_eq_inv_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (M : Matrix κ κ R) (hM : M ∈ TD R κ) :
    ∃ v : Rˣ, (v : R) = M.det ∧ ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure →
      μ.map (fun x => M *ᵥ x) = (distribHaarChar R v)⁻¹ • μ := by
  induction hM using Submonoid.closure_induction with
  | mem M hM =>
    simp only [Set.mem_union, Set.mem_setOf_eq] at hM
    rcases hM with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨1, by rw [det_transvection_of_ne (h := hij), Units.val_one], fun μ hμ => ?_⟩
      rw [map_one, inv_one, one_smul]
      exact map_transvection_mulVec_addHaar_eq_self i j hij c μ
    · refine ⟨∏ i, d i, by simp [det_diagonal], fun μ hμ => ?_⟩
      rw [map_prod]
      exact map_diagonal_mulVec_eq_inv_prod_smul d μ
  | one => exact ⟨1, by simp, fun μ hμ => by simp [Measure.map_id']⟩
  | mul M N _ _ hM hN =>
    obtain ⟨v, hv, hvμ⟩ := hM
    obtain ⟨w, hw, hwμ⟩ := hN
    refine ⟨v * w, by simp [hv, hw, det_mul], fun μ hμ => ?_⟩
    rw [map_mul_lemma_2, hwμ μ hμ, Measure.map_smul, hvμ μ hμ, smul_smul, map_mul, mul_inv, mul_comm]

theorem map_mulVec_of_mem_TD : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), M ∈ TD R κ → ∀ u : Rˣ, u.1 = M.det → ∀ μ : @Measure (κ → R) (borel _),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    @Measure.map _ _ (borel _) (borel _) (fun x : κ → R => M *ᵥ x) μ = ((distribHaarChar R u)⁻¹ : ℝ≥0) • μ := by
  intro R _ _ _ _ _ _ κ _ _ M hM u hu μ hμ
  letI : MeasurableSpace (κ → R) := borel (κ → R)
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  obtain ⟨v, hv, hvμ⟩ := exists_unit_det_map_mulVec_haar_eq_inv_smul M hM
  have huv : u = v := Units.ext (hu.trans hv.symm)
  subst huv
  exact hvμ μ hμ

end GlobalTheory.HaarLin
end
end

section
open NumberField IsDedekindDomain GlobalTheory.HaarLin

namespace GlobalTheory.HaarLin.Gauss

open Matrix

variable {R : Type} [CommRing R]

theorem transvection_mem {κ : Type} [Fintype κ] [DecidableEq κ] {i j : κ} (h : i ≠ j) (c : R) :
    transvection i j c ∈ TD R κ :=
  Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)

theorem diagonal_mem {κ : Type} [Fintype κ] [DecidableEq κ] (d : κ → Rˣ) :
    (diagonal fun i => (d i : R)) ∈ TD R κ :=
  Submonoid.subset_closure (Or.inr ⟨d, rfl⟩)

theorem exists_inv {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ R} (hA : A ∈ TD R κ) :
    ∃ B ∈ TD R κ, B * A = 1 ∧ A * B = 1 := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨transvection i j (-c), transvection_mem hij _, ?_, ?_⟩ <;>
        simp [transvection_mul_transvection_same _ _ hij]
    · refine ⟨_, diagonal_mem (fun i => (d i)⁻¹), ?_, ?_⟩ <;>
        simp [diagonal_mul_diagonal]
  | one => exact ⟨1, one_mem _, by simp, by simp⟩
  | mul A B _ _ IA IB =>
    obtain ⟨A', hA', h1, h2⟩ := IA
    obtain ⟨B', hB', h3, h4⟩ := IB
    refine ⟨B' * A', mul_mem hB' hA', ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc A', h1, one_mul, h3]
    · rw [mul_assoc, ← mul_assoc B, h4, one_mul, h2]

theorem of_left {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (E * M).det → E * M ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem hB (h (by rw [det_mul]; exact hd.mul hM))
  rwa [← mul_assoc, h1, one_mul] at this

theorem of_right {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (M * E).det → M * E ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem (h (by rw [det_mul]; exact hM.mul hd)) hB
  rwa [mul_assoc, h2, mul_one] at this

theorem rowOp {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ M : Matrix κ κ R, (∀ b, (E * M) p b = M p b + ∑ k ∈ s, w k * M k b) ∧
      ∀ a b, a ≠ p → (E * M) a b = M a b := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH (fun h => hs (by simp [h]))
    refine ⟨transvection p k (w k) * E, mul_mem (transvection_mem hkp _) hE, fun M => ⟨fun b => ?_, fun a b ha => ?_⟩⟩
    · rw [mul_assoc, transvection_mul_apply_same, (H M).1, (H M).2 _ _ hkp.symm, Finset.sum_insert hk]
      ring
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, (H M).2 _ _ ha]

theorem colOpLeft {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (E * M) a b = M a b + if a ∈ s then w a * M p b else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨transvection k p (w k) * E, mul_mem (transvection_mem hkp.symm _) hE, fun M a b => ?_⟩
    by_cases ha : a = k
    · subst ha
      rw [mul_assoc, transvection_mul_apply_same, H, H]
      simp [hk, hps]
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, H]
      simp [ha]

theorem colOpRight {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (M * E) a b = M a b + if b ∈ s then w b * M a p else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨E * transvection p k (w k), mul_mem hE (transvection_mem hkp _), fun M a b => ?_⟩
    by_cases hb : b = k
    · subst hb
      rw [← mul_assoc, mul_transvection_apply_same, H, H]
      simp [hk, hps]
    · rw [← mul_assoc, mul_transvection_apply_of_ne _ _ _ _ hb, H]
      simp [hb]

theorem reindex_mem {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : A.submatrix e.symm e.symm ∈ TD R κ' := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : (transvection i j c).submatrix e.symm e.symm = transvection (e i) (e j) c := by
        ext a b
        simp [transvection, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]
      rw [this]
      exact transvection_mem (e.injective.ne hij) c
    · rw [submatrix_diagonal_equiv]
      exact diagonal_mem (fun i => d (e.symm i))
  | one => rw [submatrix_one_equiv]; exact one_mem _
  | mul A B _ _ IA IB =>
    rw [← submatrix_mul_equiv A B e.symm e.symm e.symm]
    exact mul_mem IA IB

theorem fromBlocks_mem {κ : Type} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : fromBlocks A 0 0 (1 : Matrix Unit Unit R) ∈ TD R (κ ⊕ Unit) := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : transvection (Sum.inl i) (Sum.inl j) c = fromBlocks (transvection i j c) 0 0 (1 : Matrix Unit Unit R) :=
        TransvectionStruct.toMatrix_sumInl Unit (⟨i, j, hij, c⟩ : TransvectionStruct κ R)
      rw [← this]
      exact transvection_mem (Sum.inl_injective.ne hij) c
    · rw [← diagonal_one, fromBlocks_diagonal]
      convert diagonal_mem (R := R) (Sum.elim d (fun _ : Unit => 1)) using 2
      ext x
      cases x <;> rfl
  | one => rw [fromBlocks_one]; exact one_mem _
  | mul A B _ _ IA IB =>
    have := mul_mem IA IB
    rw [fromBlocks_multiply] at this
    simpa using this

theorem step {κ : Type} [Fintype κ] [DecidableEq κ] (hR : HasStableRangeOne R)
    (IH : ∀ N : Matrix κ κ R, IsUnit N.det → N ∈ TD R κ)
    (M : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R) (hM : IsUnit M.det) : M ∈ TD R (κ ⊕ Unit) := by
  set l : κ ⊕ Unit := Sum.inr () with hl
  set s : Finset (κ ⊕ Unit) := Finset.univ.erase l with hs
  have hls : l ∉ s := Finset.notMem_erase _ _
  have hin : ∀ i : κ, Sum.inl i ∈ s := fun i => by simp [hs, hl]
  have h1 : (M⁻¹ * M) l l = 1 := by rw [nonsing_inv_mul M hM, one_apply_eq]
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at h1
  obtain ⟨t, ht⟩ := hR (M l l) (∑ k ∈ s, M⁻¹ l k * M k l) ⟨M⁻¹ l l, 1, by rw [one_mul]; exact h1⟩
  obtain ⟨E₁, hE₁, H₁⟩ := rowOp l (fun k => t * M⁻¹ l k) s hls
  refine of_left hE₁ hM fun hM₁ => ?_
  have hu : IsUnit ((E₁ * M) l l) := by
    rw [(H₁ M).1]
    simpa [Finset.mul_sum, mul_assoc] using ht
  generalize E₁ * M = M₁ at hM₁ hu
  obtain ⟨u, hu⟩ := hu
  obtain ⟨E₂, hE₂, H₂⟩ := colOpLeft l (fun a => - M₁ a l * ↑u⁻¹) s hls
  refine of_left hE₂ hM₁ fun hM₂ => ?_
  have hu₂ : (E₂ * M₁) l l = u := by rw [H₂, if_neg hls, add_zero, hu]
  have hc₂ : ∀ i : κ, (E₂ * M₁) (Sum.inl i) l = 0 := fun i => by
    rw [H₂, if_pos (hin i), ← hu, mul_assoc, Units.inv_mul]; ring
  generalize E₂ * M₁ = M₂ at hM₂ hu₂ hc₂
  obtain ⟨E₃, hE₃, H₃⟩ := colOpRight l (fun b => - M₂ l b * ↑u⁻¹) s hls
  refine of_right hE₃ hM₂ fun hM₃ => ?_
  have hu₃ : (M₂ * E₃) l l = u := by rw [H₃, if_neg hls, add_zero, hu₂]
  have hc₃ : ∀ i : κ, (M₂ * E₃) (Sum.inl i) l = 0 := fun i => by
    rw [H₃, if_neg hls, add_zero, hc₂]
  have hr₃ : ∀ i : κ, (M₂ * E₃) l (Sum.inl i) = 0 := fun i => by
    rw [H₃, if_pos (hin i), hu₂, mul_assoc, Units.inv_mul]; ring
  generalize M₂ * E₃ = M₃ at hM₃ hu₃ hc₃ hr₃
  have hform : M₃ = (diagonal fun i => ((Sum.elim (fun _ => 1) (fun _ => u) : κ ⊕ Unit → Rˣ) i : R)) *
      fromBlocks M₃.toBlocks₁₁ 0 0 (1 : Matrix Unit Unit R) := by
    ext a b
    rw [diagonal_mul]
    rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
    · simp [toBlocks₁₁]
    · simpa using hc₃ a
    · simpa using hr₃ b
    · simpa using hu₃
  have hN : IsUnit M₃.toBlocks₁₁.det := by
    rw [hform, det_mul, det_fromBlocks_zero₂₁, det_one, mul_one] at hM₃
    exact isUnit_of_mul_isUnit_right hM₃
  rw [hform]
  exact mul_mem (diagonal_mem _) (fromBlocks_mem (IH _ hN))

theorem mem_TD_of_isUnit_det : ∀ (R : Type) [CommRing R], HasStableRangeOne R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), IsUnit M.det → M ∈ TD R κ := by
  intro R _ hR κ _ _
  have key : ∀ n : ℕ, ∀ N : Matrix (Fin n) (Fin n) R, IsUnit N.det → N ∈ TD R (Fin n) := by
    intro n
    induction n with
    | zero => intro N _; rw [Subsingleton.elim N 1]; exact one_mem _
    | succ n IH =>
      intro N hN
      let e : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
      have := reindex_mem e (step hR IH (N.submatrix e e) (by rwa [det_submatrix_equiv_self]))
      simpa using this
  intro M hM
  let e := (Fintype.equivFin κ).symm
  have := reindex_mem e (key _ (M.submatrix e e) (by rwa [det_submatrix_equiv_self]))
  simpa using this

end GlobalTheory.HaarLin.Gauss
end
