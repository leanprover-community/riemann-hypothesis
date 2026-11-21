import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ExtendedColumns
import Mathlib
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

lemma qk_antitone_of_step {n : ℕ} {f : Fin n → ℤ} (h : ∀ a : Fin n, ∀ h : a.1 + 1 < n, f ⟨a.1 + 1, h⟩ ≤ f a) :
    Antitone f := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m =>
    rw [Fin.antitone_iff_succ_le]
    intro i
    exact h i.castSucc (by simp)

lemma qk_hstrip_dom {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) : Dominant nu ∧ Dominant mu :=
  ⟨qk_antitone_of_step fun a ha => (h.1 _).trans (h.2.1 a ha),
   qk_antitone_of_step fun a ha => (h.2.1 a ha).trans (h.1 a)⟩

lemma qk_hstrip_iff {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) : HStrip nu mu b ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip mu nu b := by
  unfold HStrip Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h m m' hm
      have := h m (by have := m'.2; omega)
      have e : (⟨m.1 + 1, by have := m'.2; omega⟩ : Fin n) = m' := Fin.ext hm
      rwa [e] at this
    · intro h a ha
      exact h a ⟨a.1 + 1, ha⟩ rfl
  · rw [sum_sub_distrib]

lemma qk_strUp_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strUp mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp mu b := by
  unfold strUp Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp
  ext nu
  simp only [mem_filter, qk_hstrip_iff]

lemma qk_strDown_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strDown mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown mu b := by
  unfold strDown Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown
  ext nu
  simp only [mem_filter, qk_hstrip_iff]

lemma qk_mem_strUp {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := by
  unfold strUp at h
  simp only [mem_filter] at h
  exact h.2

lemma qk_mem_strDown {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b := by
  unfold strDown at h
  simp only [mem_filter] at h
  exact h.2

def qk_symEquiv (n b : ℕ) : SymIdx n b ≃ {P : Fin n → ℕ // ∑ i, P i = b} where
  toFun α := ⟨fun a => (α.1 a : ℕ), α.2⟩
  invFun P := ⟨fun a => ⟨P.1 a, by
    have := single_le_sum (f := P.1) (fun i _ => Nat.zero_le _) (mem_univ a)
    have h2 := P.2
    omega⟩, P.2⟩
  left_inv α := rfl
  right_inv P := rfl

lemma qk_card_symIdx (n b : ℕ) : Fintype.card (SymIdx n b) = (n + b - 1).choose b := by
  rw [Fintype.card_congr ((qk_symEquiv n b).trans (Sym.equivNatSumOfFintype (Fin n) b).symm),
    Sym.card_sym_eq_choose, Fintype.card_fin]

theorem symmetric_power_count_holds : CntSym := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).1, ← qk_strUp_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strUp hnu)).2]

theorem dual_symmetric_power_count_holds : CntSymD := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).2, ← qk_strDown_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strDown hnu)).1]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset Polynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qk_det_eval {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (hdeg : ∀ i, (p i).natDegree ≤ i) :
    (Matrix.of fun i j => (p j).eval (v i)).det = (Matrix.vandermonde v).det * ∏ i, (p i).coeff i := by
  have h : (Matrix.of fun i j => (p j).eval (v i)) =
      Matrix.vandermonde v * Matrix.of fun (i j : Fin n) => (p j).coeff i := by
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (hdeg j) j.2),
      ← Fin.sum_univ_eq_sum_range (fun k => (p j).coeff k * v i ^ k)]
    refine sum_congr rfl fun k _ => ?_
    simp [Matrix.vandermonde_apply, mul_comm]
  rw [h, Matrix.det_mul, Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p hdeg)]
  rfl

lemma qk_det_shift {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (x : R) :
    (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * (v i - 1) ^ (j : ℕ)).det =
      (Matrix.vandermonde v).det * (1 + x) ^ n := by
  have h := qk_det_eval v (fun j : Fin n => (X : R[X]) ^ (j : ℕ) + C x * (X - C 1) ^ (j : ℕ)) (by
    intro i
    refine (natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le _) ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_pow_le.trans ?_
    have := natDegree_X_sub_C_le (1 : R)
    calc (i : ℕ) * (X - C (1 : R)).natDegree ≤ (i : ℕ) * 1 := Nat.mul_le_mul_left _ this
      _ = i := mul_one _)
  have hc : ∀ i : Fin n, ((X : R[X]) ^ (i : ℕ) + C x * (X - C 1) ^ (i : ℕ)).coeff i = 1 + x := by
    intro i
    rw [coeff_add, coeff_X_pow_self, coeff_C_mul]
    have := (monic_X_sub_C (1 : R)).pow (i : ℕ)
    have h2 : ((X - C (1 : R)) ^ (i : ℕ)).coeff i = 1 := by
      nontriviality R
      have h3 : ((X - C (1 : R)) ^ (i : ℕ)).natDegree = (i : ℕ) := by
        rw [(monic_X_sub_C (1 : R)).natDegree_pow, natDegree_X_sub_C, mul_one]
      have h4 := this.coeff_natDegree
      rwa [h3] at h4
    rw [h2, mul_one]
  simp only [hc, prod_const, card_univ, Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext i j
  simp

lemma qk_det_expand {R : Type*} [CommRing R] {n : ℕ} (v w : Fin n → R) (x : R) :
    (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * w i ^ (j : ℕ)).det =
      ∑ s : Finset (Fin n), x ^ s.card * (Matrix.vandermonde (s.piecewise w v)).det := by
  have hV : ∀ u : Fin n → R, (Matrix.vandermonde u).det =
      Matrix.detRowAlternating (fun (i j : Fin n) => u i ^ (j : ℕ)) := fun u => rfl
  have h0 : (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * w i ^ (j : ℕ)).det =
      Matrix.detRowAlternating ((fun (i : Fin n) => x • fun (j : Fin n) => w i ^ (j : ℕ)) +
        fun (i j : Fin n) => v i ^ (j : ℕ)) := by
    show Matrix.detRowAlternating _ = _
    congr 1
    funext i j
    simp [add_comm]
  rw [h0, AlternatingMap.map_add_univ]
  refine sum_congr rfl fun s _ => ?_
  have h2 : s.piecewise (fun (i : Fin n) => x • fun (j : Fin n) => w i ^ (j : ℕ)) (fun (i j : Fin n) => v i ^ (j : ℕ)) =
      s.piecewise (fun i => (fun _ => x) i • (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) i)
        (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) := by
    funext i
    by_cases hi : i ∈ s
    · simp only [piecewise_eq_of_mem _ _ _ hi]
    · simp only [piecewise_eq_of_notMem _ _ _ hi]
  rw [h2, hV]
  have h3 := (Matrix.detRowAlternating (n := Fin n) (R := R)).toMultilinearMap.map_piecewise_smul (fun _ => x)
    (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) s
  refine Eq.trans h3 ?_
  rw [prod_const, smul_eq_mul]
  rfl

def qk_D {n : ℕ} (v : Fin n → ℝ) : ℝ := ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i)

lemma qk_det_C {n : ℕ} (v : Fin n → ℝ) : (Matrix.vandermonde fun i => (C (v i) : ℝ[X])).det = C (qk_D v) := by
  rw [Matrix.det_vandermonde, qk_D]
  simp only [map_prod, map_sub]

theorem qk_D_shift {n : ℕ} (v : Fin n → ℝ) (b : ℕ) :
    ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (s.piecewise (fun i => v i - 1) v) =
      (n.choose b : ℝ) * qk_D v := by
  have h1 := qk_det_expand (fun i => (C (v i) : ℝ[X])) (fun i => (C (v i) : ℝ[X]) - 1) X
  rw [qk_det_shift, qk_det_C] at h1
  have h2 : ∀ s : Finset (Fin n), (Matrix.vandermonde (s.piecewise (fun i => (C (v i) : ℝ[X]) - 1)
      (fun i => (C (v i) : ℝ[X])))).det = C (qk_D (s.piecewise (fun i => v i - 1) v)) := by
    intro s
    rw [← qk_det_C]
    congr 2
    funext i
    by_cases hi : i ∈ s <;> simp [hi]
  simp only [h2] at h1
  have h3 := congrArg (fun q : ℝ[X] => q.coeff b) h1
  simp only [finsetSum_coeff] at h3
  rw [coeff_C_mul, coeff_one_add_X_pow, mul_comm] at h3
  rw [h3, ← sum_filter_add_sum_filter_not univ (fun s : Finset (Fin n) => s.card = b)]
  have h4 : ∑ s ∈ univ.filter (fun s : Finset (Fin n) => ¬ s.card = b),
      ((X : ℝ[X]) ^ s.card * C (qk_D (s.piecewise (fun i => v i - 1) v))).coeff b = 0 := by
    refine sum_eq_zero fun s hs => ?_
    rw [mul_comm, coeff_C_mul_X_pow, if_neg (fun h => (mem_filter.1 hs).2 h.symm)]
  rw [h4, add_zero]
  have h5 : powersetCard b (univ : Finset (Fin n)) = univ.filter (fun s : Finset (Fin n) => s.card = b) := by
    ext s
    simp [mem_powersetCard]
  rw [h5]
  refine sum_congr rfl fun s hs => ?_
  rw [mul_comm, coeff_C_mul_X_pow, if_pos (mem_filter.1 hs).2.symm]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

lemma qk_prod_conv (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ j ∈ range n, ∏ i ∈ range j, F i j = ∏ i : Fin n, ∏ j ∈ Ioi i, F i j := by
  have h1 : ∀ i : Fin n, ∏ j ∈ Ioi i, F i j = ∏ j : Fin n, if i < j then F i j else 1 := by
    intro i
    rw [← prod_filter]
    congr 1
    ext j
    simp
  simp_rw [h1]
  rw [prod_comm, ← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, F i j) n]
  refine prod_congr rfl fun j _ => ?_
  have h2 : ∏ i : Fin n, (if i < j then F i j else 1) = ∏ i ∈ range n, if i < j.1 then F i j else 1 := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => if i < j.1 then F i j else 1) n]
    refine prod_congr rfl fun i _ => ?_
    simp only [Fin.lt_def]
  rw [h2, ← prod_filter]
  congr 1
  ext i
  have := j.2
  simp only [mem_range, mem_filter]
  omega

def qk_v {n : ℕ} (mu : Fin n → ℤ) : Fin n → ℝ := fun i => (i.1 : ℝ) - (mu i : ℝ)

def vandermondeDenominator (n : ℕ) : ℝ := ∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))

lemma qk_W_ne (n : ℕ) : vandermondeDenominator n ≠ 0 := by
  unfold vandermondeDenominator
  refine prod_ne_zero_iff.2 fun j _ => prod_ne_zero_iff.2 fun i hi => ?_
  have : (i : ℝ) < (j : ℝ) := by exact_mod_cast mem_range.1 hi
  exact sub_ne_zero.2 (ne_of_gt this)

lemma qk_weyl {n : ℕ} (mu : Fin n → ℤ) :
    Formalism.InvariantFactorPaths.BranchingDimensions.weylDim n (Formalism.InvariantFactorPaths.BranchingDimensions.extW mu) * vandermondeDenominator n = qk_D (qk_v mu) := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.weylDim
  simp_rw [prod_div_distrib]
  rw [show (∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))) = vandermondeDenominator n from rfl, div_mul_cancel₀ _ (qk_W_ne n),
    qk_prod_conv n (fun i j => ((Formalism.InvariantFactorPaths.BranchingDimensions.extW mu i - Formalism.InvariantFactorPaths.BranchingDimensions.extW mu j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ)))]
  unfold qk_D qk_v
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  rw [Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val, Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val]
  push_cast
  ring

lemma qk_D_dom {n : ℕ} {mu : Fin n → ℤ} (h : Dominant mu) : qk_D (qk_v mu) = (dGT n mu : ℝ) * vandermondeDenominator n := by
  rw [← qk_weyl, Formalism.InvariantFactorPaths.BranchingDimensions.weyl_dim_eq_gelfand_tsetlin Formalism.InvariantFactorPaths.BranchingDimensions.branchingDimensionFormula n mu h]

lemma qk_D_zero {n : ℕ} {v : Fin n → ℝ} {i j : Fin n} (hij : i < j) (h : v i = v j) : qk_D v = 0 := by
  unfold qk_D
  refine prod_eq_zero (mem_univ i) (prod_eq_zero (mem_Ioi.2 hij) ?_)
  rw [h, sub_self]

def qk_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : Fin n → ℤ := fun a => if a ∈ s then mu a + 1 else mu a

lemma qk_v_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    qk_v (qk_add mu s) = s.piecewise (fun i => qk_v mu i - 1) (qk_v mu) := by
  funext i
  unfold qk_v qk_add
  by_cases hi : i ∈ s
  · simp only [hi, if_true, piecewise_eq_of_mem]
    push_cast
    ring
  · simp only [hi, if_false, piecewise_eq_of_notMem, not_false_eq_true]

lemma qk_D_nondom {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (s : Finset (Fin n))
    (h : ¬ Dominant (qk_add mu s)) : qk_D (qk_v (qk_add mu s)) = 0 := by
  have h1 : ∃ a : Fin n, ∃ ha : a.1 + 1 < n, qk_add mu s a < qk_add mu s ⟨a.1 + 1, ha⟩ := by
    by_contra hc
    push Not at hc
    exact h (qk_antitone_of_step hc)
  obtain ⟨a, ha, hlt⟩ := h1
  have hle : mu ⟨a.1 + 1, ha⟩ ≤ mu a := hmu (by rw [Fin.le_def]; simp)
  have h2 : qk_add mu s ⟨a.1 + 1, ha⟩ = qk_add mu s a + 1 := by
    unfold qk_add at hlt ⊢
    split_ifs at hlt ⊢ <;> omega
  refine qk_D_zero (i := a) (j := ⟨a.1 + 1, ha⟩) (by rw [Fin.lt_def]; simp) ?_
  unfold qk_v
  rw [h2]
  push_cast
  ring

lemma qk_mem_strVert {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} : nu ∈ strVert mu b ↔
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  unfold strVert
  simp only [mem_filter, Fintype.mem_piFinset, mem_Icc]

lemma qk_add_sum {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : ∑ a, (qk_add mu s a - mu a) = (s.card : ℤ) := by
  have : ∀ a, qk_add mu s a - mu a = if a ∈ s then 1 else 0 := by
    intro a
    unfold qk_add
    split_ifs <;> ring
  simp only [this]
  simp

lemma qk_add_sel {n : ℕ} {mu nu : Fin n → ℤ} (h : ∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) :
    qk_add mu (univ.filter fun a => nu a = mu a + 1) = nu := by
  funext a
  unfold qk_add
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h1
  · exact h1.symm
  · have := h a
    omega

lemma qk_sel_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    (univ.filter fun a => qk_add mu s a = mu a + 1) = s := by
  ext a
  by_cases ha : a ∈ s <;> simp [qk_add, ha]

theorem exterior_power_count_holds : CntLam := by
  classical
  intro n _ mu b hmu
  have hcard : Fintype.card (LamIdx n b) = n.choose b := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [hcard]
  have hW := qk_W_ne n
  have key : ((dMu mu * n.choose b : ℕ) : ℝ) * vandermondeDenominator n = ((∑ nu ∈ strVert mu b, dMu nu : ℕ) : ℝ) * vandermondeDenominator n := by
    push_cast
    rw [sum_mul]
    have e1 : ∑ nu ∈ strVert mu b, (dMu nu : ℝ) * vandermondeDenominator n = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_congr rfl fun nu hnu => ?_
      have hd := (qk_mem_strVert.1 hnu).2.1
      rw [qk_D_dom hd, qk_dMu_eq_dGT n nu hd]
    have e2 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_nbij' (qk_add mu) (fun nu => univ.filter fun a => nu a = mu a + 1) ?_ ?_ ?_ ?_ ?_
      · intro s hs
        rw [mem_filter, mem_powersetCard] at hs
        refine qk_mem_strVert.2 ⟨fun a => ?_, hs.2, ?_⟩
        · unfold qk_add
          split_ifs <;> omega
        · rw [qk_add_sum, hs.1.2]
      · intro nu hnu
        have h := qk_mem_strVert.1 hnu
        rw [mem_filter, mem_powersetCard, qk_add_sel h.1]
        refine ⟨⟨subset_univ _, ?_⟩, h.2.1⟩
        have h3 := qk_add_sum mu (univ.filter fun a => nu a = mu a + 1)
        rw [qk_add_sel h.1, h.2.2] at h3
        exact_mod_cast h3.symm
      · intro s _
        exact qk_sel_add mu s
      · intro nu hnu
        exact qk_add_sel (qk_mem_strVert.1 hnu).1
      · intro s _
        rfl
    have e3 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (qk_v (qk_add mu s)) := by
      refine sum_filter_of_ne fun s _ hne => ?_
      by_contra hc
      exact hne (qk_D_nondom hmu s hc)
    rw [e1, ← e2, e3]
    simp only [qk_v_add]
    rw [qk_D_shift, qk_D_dom hmu, qk_dMu_eq_dGT n mu hmu]
    ring
  exact_mod_cast mul_right_cancel₀ hW key

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
