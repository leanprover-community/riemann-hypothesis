import Formalism.ThetaLogCoordinates.DualWeylCoordinates.FiltrationTheoremOfClauses
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLDetUZpow
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

variable {n : ℕ}

lemma qd_evGLR_mapCoord {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (z : GLCoord ℤ n) :
    evGLR (R := ℚ) x (mapCoord ℚ z) = evGL x z := by
  have h : (evGLR (R := ℚ) x).comp (mapCoord ℚ) = evGL x := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGLR, mapCoord, evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h

def qd_sig (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ →ₐ[ℚ] GLCoord ℚ n :=
  (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)).comp (rename Prod.swap)

lemma qd_sig_X (v : Fin n × Fin n) :
    qd_sig n (X v) = algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (v.2, v.1)) := by
  simp [qd_sig, Prod.swap]

lemma qd_genDet_ne (n : ℕ) : (genMat ℚ n).det ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)) h
  rw [RingHom.map_det] at this
  have h1 : (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)).mapMatrix (genMat ℚ n)
      = 1 := by
    ext a b; simp [genMat, Matrix.one_apply]
  rw [h1] at this
  simp at this

lemma qd_sig_inj (n : ℕ) : Function.Injective (qd_sig n) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)) :=
    IsLocalization.injective (GLCoord ℚ n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (qd_genDet_ne n))
  have h2 : Function.Injective (rename (R := ℚ) (Prod.swap : Fin n × Fin n → Fin n × Fin n)) :=
    rename_injective _ Prod.swap_injective
  intro p q hpq
  exact h2 (h1 hpq)

lemma qd_ev_sig {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) x (qd_sig n P) = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) P := by
  have h : (evGLR (R := ℚ) x).comp (qd_sig n).toRingHom
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [qd_sig, evGLR, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ P) h

lemma qd_evGL_detU {R : Type} [CommRing R] (x : GL (Fin n) R) (m : ℤ) :
    evGL x ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((Matrix.GeneralLinearGroup.det x ^ m : Rˣ) : R) := by
  have h : Units.map (evGL x).toMonoidHom (detU n) = Matrix.GeneralLinearGroup.det x := by
    ext
    simp only [Units.coe_map, detU, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    rw [evGL, IsLocalization.Away.lift_eq, RingHom.map_det, genMat_map_eval]
  rw [← h, ← map_zpow]
  rfl

variable [NeZero n]

def qd_P (mu : Fin n → ℤ) (I : TIdx mu) : MvPolynomial (Fin n × Fin n) ℚ :=
  ∏ c : ↥(TCols mu), initMinor ℚ (fun p => (I c).1.orderEmbOfFin (I c).2 p) (colH_le mu c)

def qd_U (mu : Fin n → ℤ) : GLCoord ℚ n := mapCoord ℚ ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)

lemma qd_can_emb (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2 (f := Fin.castLE (colH_le mu c))
    (by intro x; simp [canT]) (Fin.strictMono_castLE _)
  rw [← this]

lemma qd_brk (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord ℚ (brk mu I) = qd_U mu * qd_sig n (qd_P mu I) := by
  unfold brk TMat qd_U qd_P
  rw [map_mul, map_prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold minorC initMinor
  rw [mapCoord, IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.map_det, AlgHom.map_det,
    RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [genMat, qd_can_emb, qd_sig_X]

def qd_nu (mu : Fin n → ℤ) : Fin n → ℕ := ∑ c : ↥(TCols mu), initW n (colH mu c)

lemma qd_nu_anti (mu : Fin n → ℤ) : Antitone (qd_nu mu) := by
  intro s t hst
  unfold qd_nu
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_le_sum fun c _ => ?_
  have : s.val ≤ t.val := hst
  unfold initW
  split_ifs <;> omega

lemma tableauBideterminant_mem_dualWeyl' (mu : Fin n → ℤ) (I : TIdx mu) : qd_P mu I ∈ dualWeyl ℚ n n (qd_nu mu) :=
  dualWeyl_prod univ _ _ (fun _ _ => initMinor_mem _ _)

def qd_L (mu : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] GLCoord ℚ n :=
  (LinearMap.mulLeft ℚ (qd_U mu)) ∘ₗ (qd_sig n).toLinearMap

lemma qd_L_apply (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    qd_L mu P = qd_U mu * qd_sig n P := rfl

lemma qd_L_P (mu : Fin n → ℤ) (I : TIdx mu) : qd_L mu (qd_P mu I) = mapCoord ℚ (brk mu I) :=
  (qd_brk mu I).symm

lemma qd_span_le (mu : Fin n → ℤ) :
    Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)) ≤
      (dualWeyl ℚ n n (qd_nu mu)).map (qd_L mu) := by
  rw [Submodule.span_le]
  rintro _ ⟨I, rfl⟩
  exact ⟨qd_P mu I, tableauBideterminant_mem_dualWeyl' mu I, qd_L_P mu I⟩

omit [NeZero n] in
lemma generic_point_det_isUnit (n : ℕ) : IsUnit (Matrix.of fun a b : Fin n =>
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))).det := by
  have : (Matrix.of fun a b : Fin n =>
      Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))) =
      (Polynomial.C.comp (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n))).mapMatrix (genMat ℚ n) := by
    ext a b : 2; simp [genMat]
  rw [this, ← RingHom.map_det]
  exact (IsLocalization.Away.algebraMap_isUnit (S := GLCoord ℚ n) (genMat ℚ n).det).map Polynomial.C

def qd_genPt (n : ℕ) : GL (Fin n) (Polynomial (GLCoord ℚ n)) :=
  Matrix.GeneralLinearGroup.mk'' _ (generic_point_det_isUnit n)

omit [NeZero n] in
lemma qd_genPt_val (i j : Fin n) : (qd_genPt n).val i j =
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (i, j))) := rfl

def qd_trans {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) : GL (Fin n) R :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection a b t)
    (by rw [Matrix.det_transvection_of_ne _ _ hab]; exact isUnit_one)

omit [NeZero n] in
lemma qd_trans_det {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) :
    Matrix.GeneralLinearGroup.det (qd_trans a b hab t) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transvection_of_ne _ _ hab t

omit [NeZero n] in
lemma qd_mul_trans {R : Type} [CommRing R] (x : GL (Fin n) R) (a b : Fin n) (hab : a ≠ b) (t : R) (i j : Fin n) :
    (x * qd_trans a b hab t).val i j = x.val i j + if j = b then t * x.val i a else 0 := by
  have : (x * qd_trans a b hab t).val = x.val * Matrix.transvection a b t := rfl
  rw [this]
  split_ifs with h
  · subst h; rw [Matrix.mul_transvection_apply_same]
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ h, add_zero]

omit [NeZero n] in
lemma qd_trans_diag {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) (i : Fin n) :
    (qd_trans a b hab t).val i i = 1 := by
  have : (qd_trans a b hab t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, h⟩; exact hab h.symm), add_zero]

omit [NeZero n] in
lemma qd_trans_low {R : Type} [CommRing R] (a b : Fin n) (hab : a < b) (t : R) (i j : Fin n) (hji : j < i) :
    (qd_trans a b hab.ne t).val i j = 0 := by
  have : (qd_trans a b hab.ne t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.mpr hji.le)), add_zero]

omit [NeZero n] in
lemma aeval_generic_point (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1) P = Polynomial.C (qd_sig n P) := by
  have h : (aeval (R := ℚ) (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1))
      = (Polynomial.CAlgHom (R := ℚ) (A := GLCoord ℚ n)).comp (qd_sig n) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h

omit [NeZero n] in
lemma qd_aeval_xu (a b : Fin n) (hab : a ≠ b) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1) P
      = Polynomial.map (qd_sig n).toRingHom (rowGen ℚ a b P) := by
  have h : (aeval (R := ℚ)
      (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1))
      = (Polynomial.mapAlgHom (qd_sig n)).comp (rowGen ℚ a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [aeval_X, AlgHom.comp_apply, rowGen_X, qd_mul_trans, Polynomial.coe_mapAlgHom]
    split_ifs <;> simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h

lemma qd_U_unit {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (mu : Fin n → ℤ) :
    IsUnit (evGLR (R := ℚ) x (qd_U mu)) := by
  unfold qd_U
  rw [qd_evGLR_mapCoord, qd_evGL_detU]
  exact Units.isUnit _

lemma qd_U_inv {R' : Type} [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R') (mu : Fin n → ℤ)
    (hu : Matrix.GeneralLinearGroup.det u = 1) :
    evGLR (R := ℚ) (x * u) (qd_U mu) = evGLR (R := ℚ) x (qd_U mu) := by
  unfold qd_U
  rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, map_mul, hu, mul_one]

lemma qd_raise (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) (a b : Fin n) (hab : a ≠ b)
    (h : evGLR (R := ℚ) (qd_genPt n * qd_trans a b hab Polynomial.X) (qd_L mu P)
      = evGLR (R := ℚ) (qd_genPt n) (qd_L mu P)) :
    rowGen ℚ a b P = Polynomial.C P := by
  rw [qd_L_apply, map_mul, map_mul, qd_U_inv _ _ _ (qd_trans_det a b hab _)] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, qd_aeval_xu] at h2
  apply Polynomial.map_injective (qd_sig n).toRingHom (qd_sig_inj n)
  rw [h2, Polynomial.map_C]
  rfl

lemma tableauBideterminant_canonical_eq_prod_leadingMinor (mu : Fin n → ℤ) :
    qd_P mu (canT mu) = ∏ c : ↥(TCols mu), lpMinor ℚ (colH mu c) (colH_le mu c) (colH_le mu c) := by
  unfold qd_P
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor lpMinor
  simp only [qd_can_emb]

lemma tableauBideterminant_canonical_eq_smul_highestWeight (mu : Fin n → ℤ) : ∃ c0 : ℚ, c0 ≠ 0 ∧ qd_P mu (canT mu) = c0 • hw ℚ le_rfl (qd_nu mu) := by
  obtain ⟨c0, h0⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ (tableauBideterminant_mem_dualWeyl' mu (canT mu)) (by
    intro a b hab k hk
    unfold rowDiv
    rw [tableauBideterminant_canonical_eq_prod_leadingMinor, map_prod]
    simp only [rowGen_lpMinor ℚ a b hab]
    rw [← map_prod, Polynomial.coeff_C, if_neg (by omega)])
  refine ⟨c0, ?_, h0⟩
  rintro rfl
  rw [zero_smul, tableauBideterminant_canonical_eq_prod_leadingMinor] at h0
  have := congrArg (eval (idPoint ℚ n n)) h0
  simp [eval_idPoint_lpMinor] at this

theorem eq_smul_canonical_of_unipotent_invariant (mu : Fin n → ℤ) (f : GLCoord ℚ n)
    (hf : f ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)))
    (hinv : ∀ (R' : Type) [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R'), (∀ a, u.val a a = 1) →
      (∀ a b, b < a → u.val a b = 0) → evGLR (R := ℚ) (x * u) f = evGLR (R := ℚ) x f) :
    ∃ c : ℚ, f = c • mapCoord ℚ (brk mu (canT mu)) := by
  obtain ⟨P, hP, rfl⟩ := qd_span_le mu hf
  obtain ⟨c, hc⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) P hP (by
    intro a b hab k hk
    unfold rowDiv
    rw [qd_raise mu P a b hab.ne (hinv _ _ _ (qd_trans_diag a b hab.ne _) (qd_trans_low a b hab _)),
      Polynomial.coeff_C, if_neg (by omega)])
  obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
  refine ⟨c / c0, ?_⟩
  rw [← qd_L_P, ← map_smul, h0, hc, smul_smul, div_mul_cancel₀ _ hc0]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qd_vander {σ : Type} (W : Submodule ℚ (MvPolynomial σ ℚ)) (p : Polynomial (MvPolynomial σ ℚ))
    (h : ∀ t : ℕ, p.eval (C (t : ℚ)) ∈ W) (k : ℕ) : p.coeff k ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  set ψ : MvPolynomial σ ℚ →ₗ[ℚ] ℚ := φ ∘ₗ W.mkQ with hψ
  have hW : ∀ x ∈ W, ψ x = 0 := by
    intro x hx
    rw [hψ, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hx, map_zero]
  set q : Polynomial ℚ := ∑ i ∈ range (p.natDegree + 1), Polynomial.monomial i (ψ (p.coeff i)) with hq
  have hev : ∀ t : ℕ, q.eval (t : ℚ) = 0 := by
    intro t
    rw [← hW _ (h t), Polynomial.eval_eq_sum_range (p := p), map_sum, hq, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, mul_comm (p.coeff i), ← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (fun t : ℕ => (t : ℚ)))
    · rintro _ ⟨t, rfl⟩
      exact hev t
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have hc : q.coeff k = ψ (p.coeff k) := by
    rw [hq, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' ]
    split_ifs with hk
    · rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk), map_zero]
  rw [hq0, Polynomial.coeff_zero] at hc
  exact hc.symm

variable {n : ℕ}

lemma qd_eval_rowGen (a b : Fin n) (t : ℚ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (rowGen ℚ a b f).eval (C t) = rowAct ℚ (1 + Matrix.single b a t) f := by
  have h : ((Polynomial.aeval (R := MvPolynomial (Fin n × Fin n) ℚ) (C t : MvPolynomial (Fin n × Fin n) ℚ)).restrictScalars
      ℚ).comp (rowGen ℚ a b) = rowAct ℚ (1 + Matrix.single b a t) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowGen_X, rowAct, aeval_X]
    simp only [AlgHom.restrictScalars_apply, map_add, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, Matrix.single_apply]
    congr 1
    · simp
    · split_ifs with hv
      · simp only [hv, true_and, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_self,
          RingHom.id_apply]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
        simp
      · simp [Ne.symm hv]
  have := congrArg (fun φ => φ f) h
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using this

lemma qd_det_E (a b : Fin n) (t : ℕ) : IsUnit (1 + Matrix.single b a (t : ℚ)).det := by
  by_cases hab : b = a
  · subst hab
    have : (1 + Matrix.single b b (t : ℚ)) = Matrix.diagonal (fun i => if i = b then (1 + t : ℚ) else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = b <;> simp [hi, Matrix.single_apply]
        intro h; exact absurd h.symm hi
      · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [this, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp only [mem_univ, if_true]
    exact isUnit_iff_ne_zero.2 (by positivity)
  · have : (1 + Matrix.single b a (t : ℚ)) = Matrix.transvection b a (t : ℚ) := rfl
    rw [this, Matrix.det_transvection_of_ne _ _ hab]
    exact isUnit_one

variable [NeZero n]

def translatesSpanCanonical (mu : Fin n → ℤ) : Submodule ℚ (MvPolynomial (Fin n × Fin n) ℚ) :=
  Submodule.span ℚ {f | ∃ g : Matrix (Fin n) (Fin n) ℚ, IsUnit g.det ∧ f = rowAct ℚ g (qd_P mu (canT mu))}

lemma qd_W_closed (mu : Fin n → ℤ) : RowDivClosed (translatesSpanCanonical mu) := by
  intro a b k f hf
  have : translatesSpanCanonical mu ≤ (translatesSpanCanonical mu).comap (rowDivL ℚ a b k) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, rowDivL_apply]
    apply qd_vander
    intro t
    rw [qd_eval_rowGen, ← AlgHom.comp_apply, rowActMul]
    apply Submodule.subset_span
    exact ⟨_, by rw [Matrix.det_mul]; exact hg.mul (qd_det_E a b t), rfl⟩
  exact this hf

lemma qd_W_eq (mu : Fin n → ℤ) : translatesSpanCanonical mu = dualWeyl ℚ n n (qd_nu mu) := by
  have hcan : qd_P mu (canT mu) ∈ translatesSpanCanonical mu := by
    apply Submodule.subset_span
    exact ⟨1, by simp, by rw [ldrow_rowAct_one]; rfl⟩
  apply closedEqNabla n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ _ (qd_W_closed mu)
  · obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
    have : hw ℚ le_rfl (qd_nu mu) = c0⁻¹ • qd_P mu (canT mu) := by
      rw [h0, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hcan
  · unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, _, rfl⟩
    exact dualWeylRowStable ℚ n n _ g _ (tableauBideterminant_mem_dualWeyl' mu _)

omit [NeZero n] in
lemma qd_evGL_map {R' : Type} [CommRing R'] [Algebra ℚ R'] (γ : GL (Fin n) ℚ) (z : GLCoord ℤ n) :
    evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) z = algebraMap ℚ R' (evGL γ z) := by
  have h : evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) = (algebraMap ℚ R').comp (evGL γ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h

omit [NeZero n] in
lemma qd_aeval_mul {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1) P
      = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) (rowAct ℚ γ.val.transpose P) := by
  have h : aeval (R := ℚ) (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1)
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).comp (rowAct ℚ γ.val.transpose) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowAct, aeval_X, aeval_X, map_sum, Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_X, aeval_C, Matrix.transpose_apply, mul_comm]
    rfl
  exact congrArg (fun φ => φ P) h

omit [NeZero n] in
lemma qd_ev_algebraMap {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (c : ℚ) :
    evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) c) = algebraMap ℚ R' c := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n), evGLR,
    IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]

lemma qd_ev_L_mul {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ) (mu : Fin n → ℤ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_L mu P)
      = evGLR (R := ℚ) x (qd_L mu
        (((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose P)) := by
  rw [map_smul, qd_L_apply, qd_L_apply, map_mul, qd_ev_sig, qd_aeval_mul, Algebra.smul_def, map_mul, map_mul,
    qd_ev_sig]
  have h1 : evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_U mu)
      = evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        * evGLR (R := ℚ) x (qd_U mu) := by
    have h2 : evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        = algebraMap ℚ R' ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) :=
      qd_ev_algebraMap x _
    rw [h2, ← qd_evGL_detU, ← qd_evGL_map]
    unfold qd_U
    rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, qd_evGL_detU, map_mul, mul_zpow,
      Units.val_mul, mul_comm]
  rw [h1]
  ring

lemma qd_L_inj (mu : Fin n → ℤ) (P Q : MvPolynomial (Fin n × Fin n) ℚ)
    (h : evGLR (R := ℚ) (qd_genPt n) (qd_L mu P) = evGLR (R := ℚ) (qd_genPt n) (qd_L mu Q)) : P = Q := by
  rw [qd_L_apply, qd_L_apply, map_mul, map_mul] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, aeval_generic_point] at h2
  exact qd_sig_inj n (Polynomial.C_injective h2)

def qd_Lam (mu : Fin n → ℤ) : (TIdx mu → ℚ) →ₗ[ℚ] GLCoord ℚ n :=
  Fintype.linearCombination ℚ (fun K : TIdx mu => mapCoord ℚ (brk mu K))

lemma qd_Lam_apply (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    qd_Lam mu w = ∑ K, w K • mapCoord ℚ (brk mu K) := by
  rw [qd_Lam, Fintype.linearCombination_apply]

lemma qd_Lam_L (mu : Fin n → ℤ) (w : TIdx mu → ℚ) : qd_Lam mu w = qd_L mu (∑ K, w K • qd_P mu K) := by
  rw [qd_Lam_apply, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P]

def qd_gcan (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) : TIdx mu → ℚ := fun K => evGL γ (TMat mu K (canT mu))

lemma qd_translate (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) :
    ∑ K, qd_gcan mu γ K • qd_P mu K =
      ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose (qd_P mu (canT mu)) := by
  apply qd_L_inj mu
  rw [← qd_ev_L_mul, qd_L_P, qd_evGLR_mapCoord, brk, qc_TMat_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P, Algebra.smul_def, map_mul, qd_evGLR_mapCoord, qd_evGL_map, mul_comm]
  rw [qd_ev_algebraMap]
  rfl

theorem qd_gen (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    ∃ w' ∈ Submodule.span ℚ (Set.range (qd_gcan mu)), qd_Lam mu w = qd_Lam mu w' := by
  have h1 : (∑ K, w K • qd_P mu K) ∈ translatesSpanCanonical mu := by
    rw [qd_W_eq]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl' mu K)
  have h2 : translatesSpanCanonical mu ≤ (Submodule.span ℚ (Set.range (qd_gcan mu))).map
      (Fintype.linearCombination ℚ (fun K : TIdx mu => qd_P mu K)) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    set γ : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.mk'' g.transpose (by rwa [Matrix.det_transpose]) with hγ
    have hv : γ.val.transpose = g := by
      rw [hγ]; exact Matrix.transpose_transpose g
    refine ⟨(((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))⁻¹ • qd_gcan mu γ,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, rfl⟩), ?_⟩
    rw [map_smul, Fintype.linearCombination_apply, qd_translate, hv, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  obtain ⟨w', hw', he⟩ := h2 h1
  refine ⟨w', hw', ?_⟩
  rw [qd_Lam_L, qd_Lam_L, ← he, Fintype.linearCombination_apply]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_ev_point (M : GLMod n) (nu : Fin n → ℤ) (x : M.ι → ℚ) {R' : Type} [CommRing R'] [Algebra ℚ R']
    (g : GL (Fin n) R') (i : M.ι) :
    evGLR (R := ℚ) g (qb_ev M ℚ nu x i) =
      Matrix.mulVec ((prMu M nu).map (Int.castRingHom R'))
        (Matrix.mulVec (M.A.map (evGL g)) (fun l => algebraMap ℚ R' (x l))) i := by
  rw [qb_ev_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast, qd_evGLR_mapCoord, qd_ev_algebraMap,
    Matrix.map_apply, Int.coe_castRingHom]

lemma qd_ev_inv (M : GLMod n) (la nu : Fin n → ℤ) (x : M.ι → ℚ) (hx : IsHighest M ℚ la x)
    {R' : Type} [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R') (hu1 : ∀ a, u.val a a = 1)
    (hu2 : ∀ a b, b < a → u.val a b = 0) (i : M.ι) :
    evGLR (R := ℚ) (g * u) (qb_ev M ℚ nu x i) = evGLR (R := ℚ) g (qb_ev M ℚ nu x i) := by
  rw [qd_ev_point, qd_ev_point, M.mul, ← Matrix.mulVec_mulVec, hx.2 R' u hu1 hu2]

variable [NeZero n]

lemma qd_canT_std (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [canT, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  have hle : colH mu ((c : ℤ) + 1) ≤ colH mu c := by
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 hle⟩, rfl⟩

def qd_f {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) : GLCoord ℚ n :=
  ∑ I : {I : TIdx (CF.mu j) // StdT I}, a ⟨j, I⟩ • mapCoord ℚ (brk (CF.mu j) I.1)

lemma qd_f_mem {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) :
    qd_f CF a j ∈ Submodule.span ℚ (Set.range fun I : TIdx (CF.mu j) => mapCoord ℚ (brk (CF.mu j) I)) :=
  Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨I.1, rfl⟩)

lemma qd_ev_expand {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (nu : Fin n → ℤ)
    (hmax : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) (i : M.ι) :
    qb_ev M ℚ nu (∑ y, a y • qb_vecF CF ℚ y) i =
      ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : ℚ) • qd_f CF a j.1 := by
  classical
  rw [← qb_evL_apply, map_sum, Finset.sum_apply, Fintype.sum_sigma,
    ← Finset.sum_subtype (univ.filter fun j => CF.mu j = nu) (by simp)
      (fun j => ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ) • qd_f CF a j), Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · subst hj
    rw [qd_f, Finset.smul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def, qb_key_eq, smul_comm, Algebra.smul_def (R := ℚ)
      ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ), map_intCast]
  · refine Finset.sum_eq_zero fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def]
    by_cases ha : a ⟨j, I⟩ = 0
    · rw [ha, zero_smul]
    · rw [qb_key_zero CF ℚ j I.1 nu (fun hd => hj (hmax ⟨j, I⟩ ha hd)), Pi.zero_apply, smul_zero]

theorem highest_vectors_rational_span_of : LemmaA → HighestVectorsRationalSpan := by
  intro hA n _ M CF la hla x hx
  classical
  have hsp := (qb_basisR hA CF ℚ).2
  have hli := (qb_basisR hA CF ℚ).1
  obtain ⟨a, ha⟩ : ∃ a : qb_Idx CF → ℚ, ∑ y, a y • qb_vecF CF ℚ y = x := by
    have : x ∈ Submodule.span ℚ (Set.range (qb_vecF CF ℚ)) := by rw [hsp]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 this
  subst ha

  have h1 : ∀ y, a y ≠ 0 → qb_wtT (CF.mu y.1) y.2.1 = la := by
    have hpr : ∀ y, Matrix.mulVec ((prMu M la).map (Int.castRingHom ℚ)) (qb_vecF CF ℚ y) =
        if qb_wtT (CF.mu y.1) y.2.1 = la then qb_vecF CF ℚ y else 0 := by
      intro y
      funext i
      have := congrArg (Int.cast : ℤ → ℚ) (qb_prMu_ph CF y.1 la i y.2.1)
      push_cast at this
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom, qb_vecF, ColFam.vec]
      rw [this]
      split_ifs <;> rfl
    have h : Matrix.mulVecLin ((prMu M la).map (Int.castRingHom ℚ)) (∑ y, a y • qb_vecF CF ℚ y) =
        ∑ y, a y • qb_vecF CF ℚ y := hx.1
    rw [map_sum] at h
    simp only [map_smul, Matrix.mulVecLin_apply, hpr, smul_ite, smul_zero] at h
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun y => (if qb_wtT (CF.mu y.1) y.2.1 = la then a y else 0) - a y) (by
        simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul]
        rw [sub_eq_zero]
        exact h)
    intro y hy
    by_contra hne
    have := h0 y
    simp only [if_neg hne, zero_sub, neg_eq_zero] at this
    exact hy this

  have h3 : ∀ nu, (∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) →
      ∀ y, CF.mu y.1 = nu → a y ≠ 0 → y.2.1 = canT (CF.mu y.1) := by
    intro nu hmax
    have hinv : ∀ (j : {j : CF.J // CF.mu j = nu}) (R' : Type) [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R'),
        (∀ a, u.val a a = 1) → (∀ a b, b < a → u.val a b = 0) →
        evGLR (R := ℚ) (g * u) (qd_f CF a j.1) = evGLR (R := ℚ) g (qd_f CF a j.1) := by
      intro j R' _ _ g u hu1 hu2
      have := qb_indep_ext (k := ℚ) (W := R') _ (CF.indepQ nu)
        (fun j => evGLR (R := ℚ) (g * u) (qd_f CF a j.1) - evGLR (R := ℚ) g (qd_f CF a j.1)) (fun i => ?_) j
      · exact sub_eq_zero.1 this
      · have e := qd_ev_inv M la nu _ hx g u hu1 hu2 i
        rw [qd_ev_expand CF a nu hmax i, map_sum, map_sum] at e
        simp only [smul_sub, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        convert e using 2 <;>
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, qd_ev_algebraMap]
    intro y hy hay
    obtain ⟨c, hc⟩ := eq_smul_canonical_of_unipotent_invariant (CF.mu y.1) (qd_f CF a y.1) (qd_f_mem CF a y.1) (hinv ⟨y.1, hy⟩)
    have hind := hA n (CF.mu y.1) (CF.dom y.1) ℚ
    by_contra hne
    have := Fintype.linearIndependent_iff.1 hind
      (fun I => a ⟨y.1, I⟩ - if I = ⟨canT (CF.mu y.1), qd_canT_std _⟩ then c else 0) (by
        simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
          if_true]
        rw [sub_eq_zero]
        exact hc) y.2
    rw [if_neg (fun h => hne (congrArg Subtype.val h)), sub_zero] at this
    exact hay this
  have h4 : ∀ y, a y ≠ 0 → CF.mu y.1 = la ∧ y.2.1 = canT (CF.mu y.1) := by
    intro y0 hy0
    let s : Finset (Fin n → ℤ) := (univ.filter fun y => a y ≠ 0).image fun y => CF.mu y.1
    have hs0 : CF.mu y0.1 ∈ s := mem_image.2 ⟨y0, by simp [hy0], rfl⟩
    obtain ⟨nu, hnu, hle, hmax⟩ := qb_exists_max_above s hs0
    obtain ⟨y1, hy1, hy1nu⟩ := mem_image.1 hnu
    have hay1 : a y1 ≠ 0 := by simpa using hy1
    have hmax' : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu :=
      fun y hy hd => hmax _ (mem_image.2 ⟨y, by simp [hy], rfl⟩) hd
    have hcan := h3 nu hmax' y1 hy1nu hay1
    have hw := h1 y1 hay1
    rw [hcan, qb_wtT_can (CF.dom y1.1)] at hw
    have hnula : nu = la := hy1nu.symm.trans hw
    have hle2 : DomLE la (CF.mu y0.1) := by
      rw [← h1 y0 hy0]; exact qb_wtT_le (CF.dom _) _
    have heq : CF.mu y0.1 = la := qb_domLE_antisymm (hnula ▸ hle) hle2
    exact ⟨heq, (qb_wtT_eq_iff (CF.dom _) _).1 ((h1 y0 hy0).trans heq.symm)⟩
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hy : a y = 0
  · rw [hy, zero_smul]; exact zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    obtain ⟨e1, e2⟩ := h4 y hy
    refine ⟨y.1, e1, ?_⟩
    funext i
    simp only [qb_vecF]
    rw [e2]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_high_zero (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) : IsHighest M R mu 0 :=
  ⟨Matrix.mulVec_zero _, fun R' _ _ u _ _ => by
    have e : (fun i => algebraMap R R' ((0 : M.ι → R) i)) = 0 := by funext i; simp
    rw [e, Matrix.mulVec_zero]⟩

lemma qd_high_add (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) {x y : M.ι → R}
    (hx : IsHighest M R mu x) (hy : IsHighest M R mu y) : IsHighest M R mu (x + y) :=
  ⟨by rw [Matrix.mulVec_add, hx.1, hy.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((x + y) i)) =
        (fun i => algebraMap R R' (x i)) + fun i => algebraMap R R' (y i) := by funext i; simp
    rw [e, Matrix.mulVec_add, hx.2 R' u h1 h2, hy.2 R' u h1 h2]⟩

lemma qd_high_smul (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) (c : R) {x : M.ι → R}
    (hx : IsHighest M R mu x) : IsHighest M R mu (c • x) :=
  ⟨by rw [Matrix.mulVec_smul, hx.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((c • x) i)) = algebraMap R R' c • fun i => algebraMap R R' (x i) := by
      funext i; simp
    rw [e, Matrix.mulVec_smul, hx.2 R' u h1 h2]⟩

lemma qd_det_unitri {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) : Matrix.GeneralLinearGroup.det u = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (fun a b hab => h2 a b hab)]
  simp [h1]

variable [NeZero n]

lemma qd_minor_unitri {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (c : ↥(TCols mu))
    (J : {J : Finset (Fin n) // J.card = colH mu c}) :
    evGL u (minorC J.1 (canT mu c).1 J.2 (canT mu c).2) = if J = canT mu c then 1 else 0 := by
  rw [qb_evGL_minorC]
  split_ifs with hJ
  · subst hJ
    rw [Matrix.det_of_isUpperTriangular]
    · simp [h1]
    · intro a b hab
      exact h2 _ _ ((OrderEmbedding.lt_iff_lt _).2 hab)
  · obtain ⟨j, hjJ, hj⟩ : ∃ j ∈ J.1, colH mu c ≤ j.val := by
      by_contra hcon
      push Not at hcon
      apply hJ
      apply Subtype.ext
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        exact (qb_mem_canT mu c j).2 (hcon j hj)
      · rw [J.2, (canT mu c).2]
    have hr : j ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hjJ
    obtain ⟨a, ha⟩ := hr
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, ha, qd_can_emb]
    apply h2
    exact Fin.lt_def.2 (lt_of_lt_of_le (show (Fin.castLE (colH_le mu c) b).val < colH mu c from b.2) hj)

lemma unipotent_eval_canonical {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (K : TIdx mu) :
    evGL u (TMat mu K (canT mu)) = if K = canT mu then 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod, qd_evGL_detU, qd_det_unitri u h1 h2, one_zpow, Units.val_one, one_mul]
  simp only [qd_minor_unitri u h1 h2]
  split_ifs with hK
  · subst hK
    simp
  · obtain ⟨c, hc⟩ : ∃ c, K c ≠ canT mu c := by
      by_contra hcon
      push Not at hcon
      exact hK (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg hc)

lemma qd_vec_can_high {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (j : CF.J) :
    IsHighest M R (CF.mu j) (fun i => (CF.vec j (canT (CF.mu j)) i : R)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → R) (qb_prMu_ph CF j (CF.mu j) i (canT (CF.mu j)))
    rw [if_pos (qb_wtT_can (CF.dom j))] at this
    push_cast at this
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using this
  · intro R' _ _ u h1 h2
    funext i
    have h := congrArg (evGL u) (qb_equiv_apply CF j i (canT (CF.mu j)))
    simp only [map_sum, map_mul, map_intCast, unipotent_eval_canonical u h1 h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using h

lemma qd_high_cast (M : GLMod n) (mu : Fin n → ℤ) (x : M.ι → ℤ) (hx : IsHighest M ℤ mu x) :
    IsHighest M ℚ mu (fun i => (x i : ℚ)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → ℚ) (congrFun hx.1 i)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro R' _ _ u h1 h2
    have := hx.2 R' u h1 h2
    simpa using this

theorem highest_vectors_eq_lattice_of : LemmaA → HighestVectorsEqLattice := by
  intro hA n _ M CF mu hmu
  classical
  ext x
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => IsHighest M ℤ mu x) ?_ (qd_high_zero M ℤ mu)
      (fun x y _ _ hx hy => qd_high_add M ℤ mu hx hy) (fun c x _ hx => qd_high_smul M ℤ mu c hx) hx
    rintro _ ⟨j, rfl, rfl⟩
    have := qd_vec_can_high CF ℤ j
    simpa using this
  · intro hx
    have hQ := highest_vectors_rational_span_of hA n M CF mu hmu _ (qd_high_cast M mu x hx)
    obtain ⟨b, hb⟩ : ∃ b : qb_Idx CF → ℤ, ∑ y, b y • qb_vecF CF ℤ y = x := by
      have : x ∈ Submodule.span ℤ (Set.range (qb_vecF CF ℤ)) := by rw [(qb_basisR hA CF ℤ).2]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    let S : Set (qb_Idx CF) := {y | CF.mu y.1 = mu ∧ y.2.1 = canT (CF.mu y.1)}
    have hcast : (fun i => (x i : ℚ)) = ∑ y, (b y : ℚ) • qb_basis hA CF ℚ y := by
      funext i
      rw [← hb]
      simp [qb_basis_apply, qb_vecF, Finset.sum_apply]
    have hS : (fun i => (x i : ℚ)) ∈ Submodule.span ℚ (qb_basis hA CF ℚ '' S) := by
      refine Submodule.span_mono ?_ hQ
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨⟨j, ⟨canT (CF.mu j), qd_canT_std _⟩⟩, ⟨hj, rfl⟩, by rw [qb_basis_apply]; rfl⟩
    rw [Module.Basis.mem_span_image, hcast] at hS
    have hsupp : ∀ y, b y ≠ 0 → y ∈ S := by
      intro y hy
      apply hS
      rw [Finset.mem_coe, Finsupp.mem_support_iff, Module.Basis.repr_sum_self]
      exact_mod_cast hy
    rw [← hb]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : b y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      obtain ⟨e1, e2⟩ := hsupp y hy
      refine ⟨y.1, e1, ?_⟩
      funext i
      simp only [qb_vecF, Int.cast_id]
      rw [e2]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_typeSum_mono (M : GLMod n) {pi pi' : Set (Fin n → ℤ)} (h : pi ⊆ pi') : typeSum M pi ≤ typeSum M pi' :=
  Submodule.span_mono (by
    rintro _ ⟨mu, hmu, v, hv, g, rfl⟩
    exact ⟨mu, h hmu, v, hv, g, rfl⟩)

def qd_low (mu : Fin n → ℤ) : Set (Fin n → ℤ) := {la | Dominant la ∧ DomLE la mu}

variable [NeZero n]

def qd_phQ {M : GLMod n} (CF : ColFam M) (j : CF.J) : (TIdx (CF.mu j) → ℚ) →ₗ[ℚ] (M.ι → ℚ) :=
  Matrix.mulVecLin ((CF.ph j).map (Int.castRingHom ℚ))

lemma qd_phQ_eq {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ) :
    qd_phQ CF j w = ∑ I, w I • (fun i => (CF.vec j I i : ℚ)) := by
  funext i
  simp [qd_phQ, Matrix.mulVec, dotProduct, ColFam.vec, Finset.sum_apply, mul_comm]

lemma qd_phQ_single {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) :
    qd_phQ CF j (Pi.single I 1) = fun i => (CF.vec j I i : ℚ) := by
  classical
  rw [qd_phQ_eq]
  simp [Pi.single_apply, ite_smul]

lemma qd_A_can {M : GLMod n} (CF : ColFam M) (j : CF.J) (g : GL (Fin n) ℚ) :
    Matrix.mulVec (M.A.map (evGL g)) (fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)) =
      qd_phQ CF j (qd_gcan (CF.mu j) g) := by
  funext i
  have h := congrArg (evGL g) (qb_equiv_apply CF j i (canT (CF.mu j)))
  simp only [map_sum, map_mul, map_intCast] at h
  simpa [Matrix.mulVec, dotProduct, ColFam.vec, qd_phQ, qd_gcan] using h

lemma qd_ev_phQ {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (w : TIdx (CF.mu j) → ℚ) (i : M.ι) :
    qb_ev M ℚ nu (qd_phQ CF j w) i = ∑ I, w I • qb_ev M ℚ nu (fun i => (CF.vec j I i : ℚ)) i := by
  rw [qd_phQ_eq, ← qb_evL_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, qb_evL_apply, Pi.smul_apply]

lemma qd_ev_phQ_zero {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (h : ¬ DomLE nu (CF.mu j))
    (w : TIdx (CF.mu j) → ℚ) : qb_ev M ℚ nu (qd_phQ CF j w) = 0 := by
  funext i
  rw [qd_ev_phQ]
  simp only [qb_key_zero CF ℚ j _ nu h, Pi.zero_apply, smul_zero, Finset.sum_const_zero]

lemma qd_ev_phQ_top {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ)
    (hw : qd_Lam (CF.mu j) w = 0) : qb_ev M ℚ (CF.mu j) (qd_phQ CF j w) = 0 := by
  funext i
  rw [qd_ev_phQ]
  simp only [qb_key_eq, ← mul_smul_comm]
  rw [← Finset.mul_sum, ← qd_Lam_apply, hw, mul_zero, Pi.zero_apply]

omit [NeZero n] in
lemma qd_low_minus (mu : Fin n → ℤ) : DomLowerSet (qd_low mu \ {mu}) := by
  refine ⟨fun la hla => hla.1.1, fun la hla nu hnu hle => ⟨⟨hnu, qb_domLE_trans hle hla.1.2⟩, ?_⟩⟩
  intro h
  rw [Set.mem_singleton_iff] at h
  subst h
  exact hla.2 (qb_domLE_antisymm hla.1.2 hle)

theorem qd_ph_type (hA : LemmaA) {M : GLMod n} (CF : ColFam M) : ∀ (N : ℕ) (j : CF.J),
    (by classical exact (univ.filter fun j' => DomLE (CF.mu j') (CF.mu j)).card) ≤ N →
    ∀ w, qd_phQ CF j w ∈ typeSum M (qd_low (CF.mu j)) := by
  classical
  intro N
  induction N with
  | zero =>
    intro j hj
    exfalso
    have : j ∈ univ.filter fun j' => DomLE (CF.mu j') (CF.mu j) := by simp [qb_domLE_refl]
    have := Finset.card_pos.2 ⟨j, this⟩
    omega
  | succ N ih =>
    intro j hj w
    obtain ⟨w', hw', he⟩ := qd_gen (CF.mu j) w
    have hsplit : qd_phQ CF j w = qd_phQ CF j w' + qd_phQ CF j (w - w') := by
      rw [← map_add, add_sub_cancel]
    rw [hsplit]
    apply Submodule.add_mem
    · have : Submodule.span ℚ (Set.range (qd_gcan (CF.mu j))) ≤
          (typeSum M (qd_low (CF.mu j))).comap (qd_phQ CF j) := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, ← qd_A_can]
        exact Submodule.subset_span ⟨CF.mu j, ⟨CF.dom j, qb_domLE_refl _⟩, _, qd_vec_can_high CF ℚ j, g, rfl⟩
      exact this hw'
    · have hv : qd_Lam (CF.mu j) (w - w') = 0 := by rw [map_sub, he, sub_self]
      obtain ⟨a, ha⟩ : ∃ a : qb_Idx CF → ℚ, ∑ y, a y • qb_vecF CF ℚ y = qd_phQ CF j (w - w') := by
        have : qd_phQ CF j (w - w') ∈ Submodule.span ℚ (Set.range (qb_vecF CF ℚ)) := by
          rw [(qb_basisR hA CF ℚ).2]; trivial
        exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 this
      have hs := qb_supp_in hA CF ℚ a _ (qd_low_minus (CF.mu j)) (by
        intro nu hnu hnot
        rw [ha]
        by_cases h : nu = CF.mu j
        · rw [h]; exact qd_ev_phQ_top CF j _ hv
        · exact qd_ev_phQ_zero CF j nu (fun hd => hnot ⟨⟨hnu, hd⟩, h⟩) _)
      rw [← ha]
      refine Submodule.sum_mem _ fun y _ => ?_
      by_cases hy : a y = 0
      · rw [hy, zero_smul]; exact zero_mem _
      · apply Submodule.smul_mem
        have hy' := hs y hy
        have hcard : (univ.filter fun j' => DomLE (CF.mu j') (CF.mu y.1)).card ≤ N := by
          have hlt : (univ.filter fun j' => DomLE (CF.mu j') (CF.mu y.1)) ⊂
              (univ.filter fun j' => DomLE (CF.mu j') (CF.mu j)) := by
            refine (Finset.ssubset_iff_of_subset ?_).2 ⟨j, by simp [qb_domLE_refl], ?_⟩
            · intro j' hj'
              simp only [mem_filter, mem_univ, true_and] at hj' ⊢
              exact qb_domLE_trans hj' hy'.1.2
            · simp only [mem_filter, mem_univ, true_and]
              intro hd
              exact hy'.2 (qb_domLE_antisymm hy'.1.2 hd)
          have := Finset.card_lt_card hlt
          omega
        have h1 := ih y.1 hcard (Pi.single y.2.1 1)
        rw [qd_phQ_single] at h1
        exact qd_typeSum_mono M (show qd_low (CF.mu y.1) ⊆ qd_low (CF.mu j) from
          fun la hla => ⟨hla.1, qb_domLE_trans hla.2 hy'.1.2⟩) h1

theorem filtration_type_intersection_ofA : LemmaA → FiltrationTypeIntersection := by
  intro hA n _ M CF pi hpi x
  classical
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => (fun i => (x i : ℚ)) ∈ typeSum M pi) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, I, rfl⟩
      have h1 := qd_ph_type hA CF _ j le_rfl (Pi.single I 1)
      rw [qd_phQ_single] at h1
      exact qd_typeSum_mono M (show qd_low (CF.mu j) ⊆ pi from fun la hla => hpi.2 _ hj la hla.1 hla.2) h1
    · have : (fun i => (((0 : M.ι → ℤ) i : ℤ) : ℚ)) = 0 := by funext i; simp
      rw [this]; exact zero_mem _
    · intro x y _ _ hx hy
      have : (fun i => (((x + y) i : ℤ) : ℚ)) = (fun i => (x i : ℚ)) + fun i => (y i : ℚ) := by funext i; simp
      rw [this]; exact add_mem hx hy
    · intro c x _ hx
      have : (fun i => (((c • x) i : ℤ) : ℚ)) = (c : ℚ) • fun i => (x i : ℚ) := by funext i; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro hx
    have hK : ∀ nu, Dominant nu → nu ∉ pi → typeSum M pi ≤ LinearMap.ker (qb_evL M ℚ nu) := by
      intro nu hnu hnot
      unfold typeSum
      rw [Submodule.span_le]
      rintro _ ⟨mu, hmu, v, hv, g, rfl⟩
      have hvs := highest_vectors_rational_span_of hA n M CF mu (hpi.1 mu hmu) v hv
      have : Submodule.span ℚ {y | ∃ j, CF.mu j = mu ∧ y = fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)} ≤
          (LinearMap.ker (qb_evL M ℚ nu)).comap (Matrix.mulVecLin (M.A.map (evGL g))) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply, qd_A_can, qb_evL_apply]
        exact qd_ev_phQ_zero CF j nu (fun hd => hnot (hpi.2 _ (by rw [hj]; exact hmu) nu hnu hd)) _
      exact this hvs
    obtain ⟨b, hb⟩ : ∃ b : qb_Idx CF → ℤ, ∑ y, b y • qb_vecF CF ℤ y = x := by
      have : x ∈ Submodule.span ℤ (Set.range (qb_vecF CF ℤ)) := by rw [(qb_basisR hA CF ℤ).2]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    have hcast : (fun i => (x i : ℚ)) = ∑ y, (b y : ℚ) • qb_vecF CF ℚ y := by
      funext i
      rw [← hb]
      simp [qb_vecF, Finset.sum_apply]
    have hs := qb_supp_in hA CF ℚ (fun y => (b y : ℚ)) pi hpi (fun nu hnu hnot => by
      rw [← hcast]; exact hK nu hnu hnot hx)
    rw [← hb]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : b y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨y.1, hs y (by exact_mod_cast hy), y.2.1, ?_⟩
      funext i
      simp only [qb_vecF, Int.cast_id]

theorem filtration_type_intersection_of : LemmaA → SBasis → FiltrationTypeIntersection := fun hA _ => filtration_type_intersection_ofA hA

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
