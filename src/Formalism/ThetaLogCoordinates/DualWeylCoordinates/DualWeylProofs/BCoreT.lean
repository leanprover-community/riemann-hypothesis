import Formalism.ThetaLogCoordinates.DualWeylCoordinates.FiltrationTheoremOfClauses

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qb_domLE_refl (mu : Fin n → ℤ) : DomLE mu mu := ⟨fun _ => le_rfl, rfl⟩

lemma qb_domLE_trans {a b c : Fin n → ℤ} (h1 : DomLE a b) (h2 : DomLE b c) : DomLE a c :=
  ⟨fun i => (h1.1 i).trans (h2.1 i), h1.2.trans h2.2⟩

lemma qb_eq_of_psum_eq {f g : Fin n → ℤ}
    (h : ∀ a : Fin n, ∑ b ∈ univ.filter (· ≤ a), f b = ∑ b ∈ univ.filter (· ≤ a), g b) : f = g := by
  funext a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    have h1 := h a
    have e : (univ.filter (· ≤ a) : Finset (Fin n)) = insert a (univ.filter (· < a)) := by
      ext b; simp [le_iff_eq_or_lt]
    rw [e, sum_insert (by simp), sum_insert (by simp)] at h1
    have h2 : ∑ b ∈ univ.filter (· < a), f b = ∑ b ∈ univ.filter (· < a), g b :=
      sum_congr rfl fun b hb => ih b (by simpa using hb)
    linarith

def qb_psi (mu : Fin n → ℤ) : ℤ := ∑ a, ∑ b ∈ univ.filter (· ≤ a), mu b

lemma qb_psi_le {nu mu : Fin n → ℤ} (h : DomLE nu mu) : qb_psi nu ≤ qb_psi mu :=
  sum_le_sum fun a _ => h.1 a

lemma qb_eq_of_psi {nu mu : Fin n → ℤ} (h : DomLE nu mu) (h2 : qb_psi mu ≤ qb_psi nu) : nu = mu := by
  apply qb_eq_of_psum_eq
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  have : qb_psi nu < qb_psi mu :=
    sum_lt_sum (fun i _ => h.1 i) ⟨a, mem_univ _, lt_of_le_of_ne (h.1 a) ha⟩
  linarith

lemma qb_domLE_antisymm {nu mu : Fin n → ℤ} (h1 : DomLE nu mu) (h2 : DomLE mu nu) : nu = mu :=
  qb_eq_of_psi h1 (qb_psi_le h2)

lemma qb_exists_max (s : Finset (Fin n → ℤ)) (hs : s.Nonempty) :
    ∃ nu ∈ s, ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  obtain ⟨nu, hnu, hmax⟩ := s.exists_max_image qb_psi hs
  exact ⟨nu, hnu, fun mu hmu hle => (qb_eq_of_psi hle (hmax mu hmu)).symm⟩

lemma qb_exists_max_above (s : Finset (Fin n → ℤ)) {mu0 : Fin n → ℤ} (h0 : mu0 ∈ s) :
    ∃ nu ∈ s, DomLE mu0 nu ∧ ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  classical
  obtain ⟨nu, hnu, hmax⟩ := qb_exists_max (s.filter fun mu => DomLE mu0 mu)
    ⟨mu0, by simp [h0, qb_domLE_refl]⟩
  rw [mem_filter] at hnu
  exact ⟨nu, hnu.1, hnu.2, fun mu hmu hle =>
    hmax mu (by rw [mem_filter]; exact ⟨hmu, qb_domLE_trans hnu.2 hle⟩) hle⟩

variable [NeZero n]

def qb_wtT (mu : Fin n → ℤ) (I : TIdx mu) : Fin n → ℤ :=
  fun a => mu (lastIdx n) + ((univ.filter fun c : ↥(TCols mu) => a ∈ (I c).1).card : ℤ)

lemma qb_sum_wtT (mu : Fin n → ℤ) (I : TIdx mu) (s : Finset (Fin n)) :
    ∑ b ∈ s, qb_wtT mu I b =
      (s.card : ℤ) * mu (lastIdx n) + ∑ c : ↥(TCols mu), ((s.filter (· ∈ (I c).1)).card : ℤ) := by
  unfold qb_wtT
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  congr 1
  simp only [card_filter, Nat.cast_sum]
  rw [sum_comm]

lemma qb_mem_canT (mu : Fin n → ℤ) (c : ↥(TCols mu)) (b : Fin n) :
    b ∈ (canT mu c).1 ↔ b.val < colH mu c := by
  simp only [canT, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨b.val, h⟩, by ext; rfl⟩

lemma qb_col_le (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c) (a : Fin n) :
    ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card := by
  by_cases h : a.val < colH mu c
  · apply card_le_card
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact ⟨hb.1, (qb_mem_canT mu c b).2 (lt_of_le_of_lt hb.1 h)⟩
  · calc ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ J.card :=
          card_le_card fun b hb => (mem_filter.1 hb).2
      _ = (canT mu c).1.card := by rw [hJ, (canT mu c).2]
      _ ≤ _ := card_le_card fun b hb => by
          simp only [mem_filter, mem_univ, true_and]
          refine ⟨?_, hb⟩
          have := (qb_mem_canT mu c b).1 hb
          exact Fin.le_def.2 (by omega)

lemma qb_col_eq (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c)
    (h : ∀ a : Fin n, ((univ.filter (· ≤ a)).filter (· ∈ J)).card =
      ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card) : J = (canT mu c).1 := by
  rcases Nat.eq_zero_or_pos (colH mu c) with h0 | hpos
  · have h1 : J = ∅ := card_eq_zero.1 (hJ.trans h0)
    have h2 : (canT mu c).1 = ∅ := card_eq_zero.1 ((canT mu c).2.trans h0)
    rw [h1, h2]
  · have hn := colH_le mu c
    let a : Fin n := ⟨colH mu c - 1, by omega⟩
    have hc : (canT mu c).1 ⊆ (univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1) := fun b hb => by
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨?_, hb⟩
      have := (qb_mem_canT mu c b).1 hb
      exact Fin.le_def.2 (by simp only [a]; omega)
    have h3 : J.card ≤ ((univ.filter (· ≤ a)).filter (· ∈ J)).card := by
      rw [h a, hJ]; exact (canT mu c).2.symm.le.trans (card_le_card hc)
    have h4 : (univ.filter (· ≤ a)).filter (· ∈ J) = J :=
      eq_of_subset_of_card_le (fun b hb => (mem_filter.1 hb).2) h3
    apply eq_of_subset_of_card_le
    · intro b hb
      rw [← h4] at hb
      simp only [mem_filter, mem_univ, true_and] at hb
      have := Fin.le_def.1 hb.1
      exact (qb_mem_canT mu c b).2 (by simp only [a] at this; omega)
    · rw [hJ, (canT mu c).2]

lemma qb_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (b : Fin n) :
    b.val < colH mu c ↔ c ≤ mu b := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    have : (univ.filter fun m => c ≤ mu m) ⊆ Finset.Iio b := fun m hm => by
      simp only [mem_filter, mem_univ, true_and] at hm
      rw [mem_Iio]
      by_contra hmb
      exact hc (hm.trans (hmu (not_lt.1 hmb)))
    have := card_le_card this
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have : Finset.Iic b ⊆ (univ.filter fun m => c ≤ mu m) := fun m hm => by
      simp only [mem_filter, mem_univ, true_and]
      exact h.trans (hmu (mem_Iic.1 hm))
    have := card_le_card this
    rw [Fin.card_Iic] at this
    omega

lemma qb_le_lastIdx (b : Fin n) : b ≤ lastIdx n := Fin.le_def.2 (by have := b.2; simp only [lastIdx]; omega)

lemma qb_wtT_can {mu : Fin n → ℤ} (hmu : Dominant mu) : qb_wtT mu (canT mu) = mu := by
  funext b
  unfold qb_wtT
  have e : ((univ.filter fun c : ↥(TCols mu) => b ∈ (canT mu c).1).map (Function.Embedding.subtype _)) =
      Finset.Ioc (mu (lastIdx n)) (mu b) := by
    ext c
    rw [mem_map, mem_Ioc]
    constructor
    · rintro ⟨⟨c', hc'⟩, h1, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu] at h1
      exact ⟨(mem_Ioc.1 hc').1, h1.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨c, mem_Ioc.2 ⟨h1, h2.trans (hmu (Fin.zero_le b))⟩⟩, ?_, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu]
      exact ⟨mem_univ _, h2⟩
  rw [← card_map (Function.Embedding.subtype _), e, Int.card_Ioc]
  have := hmu (qb_le_lastIdx b)
  rw [Int.toNat_of_nonneg (by omega)]
  ring

lemma qb_wtT_le {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : DomLE (qb_wtT mu I) mu := by
  constructor
  · intro a
    conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    have : ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) :=
      sum_le_sum fun c _ => by exact_mod_cast qb_col_le mu c (I c).1 (I c).2 a
    linarith
  · conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    congr 1
    refine sum_congr rfl fun c _ => ?_
    simp only [filter_univ_mem]
    rw [(I c).2, (canT mu c).2]

lemma qb_wtT_eq_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : qb_wtT mu I = mu ↔ I = canT mu := by
  constructor
  · intro h
    funext c
    apply Subtype.ext
    apply qb_col_eq mu c (I c).1 (I c).2
    intro a
    have h1 : ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu I b = ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu (canT mu) b := by
      rw [h, qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT] at h1
    have h2 : ∑ c : ↥(TCols mu), ((((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) -
        (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ)) = 0 := by
      rw [sum_sub_distrib]; linarith
    have h3 := (sum_eq_zero_iff_of_nonneg (fun c _ => by
      have := qb_col_le mu c (I c).1 (I c).2 a
      have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by exact_mod_cast this
      linarith)).1 h2 c (mem_univ c)
    have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) =
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by linarith
    exact_mod_cast this
  · rintro rfl; exact qb_wtT_can hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qb_evGL_algebraMap {R : Type} [CommRing R] (g : GL (Fin n) R) (P : MvPolynomial (Fin n × Fin n) ℤ) :
    evGL g (algebraMap _ (GLCoord ℤ n) P) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P :=
  IsLocalization.Away.lift_eq _ _ _

lemma qb_evGL_minorC {R : Type} [CommRing R] (g : GL (Fin n) R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    evGL g (minorC J I hJ hI) =
      Matrix.det (Matrix.of fun a b : Fin h => g.val (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  unfold minorC
  rw [qb_evGL_algebraMap, RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]

lemma qb_evGL_detU {R : Type} [CommRing R] (g : GL (Fin n) R) : evGL g (detU n : GLCoord ℤ n) = g.val.det := by
  have : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ (GLCoord ℤ n) (genMat ℤ n).det := rfl
  rw [this, qb_evGL_algebraMap, RingHom.map_det, genMat_map_eval]

lemma qb_evGL_detU_zpow {R : Type} [CommRing R] (g : GL (Fin n) R) (u : Rˣ) (hu : (u : R) = g.val.det) (z : ℤ) :
    evGL g ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((u ^ z : Rˣ) : R) := by
  have : Units.map (evGL g : GLCoord ℤ n →* R) (detU n) = u := Units.ext (by
    rw [Units.coe_map, hu]; exact qb_evGL_detU g)
  rw [← this, ← map_zpow, Units.coe_map]
  rfl

lemma qb_minor_diagonal {R : Type} [CommRing R] (d : Fin n → R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    Matrix.det (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) =
      if J = I then ∏ x ∈ J, d x else 0 := by
  split_ifs with hJI
  · subst hJI
    have : (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (J.orderEmbOfFin hI b)) =
        Matrix.diagonal fun a => d (J.orderEmbOfFin hJ a) := by
      ext a b
      simp [Matrix.diagonal_apply]
    rw [this, Matrix.det_diagonal]
    conv_rhs => rw [← map_orderEmbOfFin_univ J hJ]
    rw [prod_map]
    rfl
  · have : ∃ x ∈ J, x ∉ I := by
      by_contra hc
      push Not at hc
      exact hJI (eq_of_subset_of_card_le hc (by rw [hJ, hI]))
    obtain ⟨x, hxJ, hxI⟩ := this
    rw [← map_orderEmbOfFin_univ J hJ, mem_map] at hxJ
    obtain ⟨a, -, rfl⟩ := hxJ
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, Matrix.diagonal_apply_ne]
    intro hab
    apply hxI
    have := orderEmbOfFin_mem I hI b
    rw [← hab] at this
    exact this

lemma qb_prod_single {κ G : Type*} [AddCommMonoid G] (s : Finset κ) (f : κ → G) :
    ∏ x ∈ s, (AddMonoidAlgebra.single (f x) (1 : ℤ)) = AddMonoidAlgebra.single (∑ x ∈ s, f x) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, AddMonoidAlgebra.single_mul_single, one_mul]

def qb_sU (w : Fin n → ℤ) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ :=
  Units.map (AddMonoidAlgebra.of ℤ (Fin n → ℤ)) (toUnits (Multiplicative.ofAdd w))

lemma qb_sU_val (w : Fin n → ℤ) : ((qb_sU w : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) : AddMonoidAlgebra ℤ (Fin n → ℤ)) =
    AddMonoidAlgebra.single w 1 := rfl

lemma qb_sU_zpow (w : Fin n → ℤ) (z : ℤ) : qb_sU w ^ z = qb_sU (z • w) := by
  unfold qb_sU
  rw [← map_zpow, ← map_zpow, ofAdd_zsmul]

variable [NeZero n]

theorem qb_evGL_torus_TMat (mu : Fin n → ℤ) (J I : TIdx mu) :
    evGL (torusPt n) (TMat mu J I) = if J = I then AddMonoidAlgebra.single (qb_wtT mu I) 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod]
  have hdet : ((qb_sU (∑ a : Fin n, Pi.single a (1 : ℤ)) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) :
      AddMonoidAlgebra ℤ (Fin n → ℤ)) = (torusPt n).val.det := by
    rw [qb_sU_val]
    change _ = Matrix.det (Matrix.diagonal _)
    rw [Matrix.det_diagonal, qb_prod_single]
  rw [qb_evGL_detU_zpow (torusPt n) _ hdet, qb_sU_zpow, qb_sU_val]
  have hm : ∀ c : ↥(TCols mu), evGL (torusPt n) (minorC (J c).1 (I c).1 (J c).2 (I c).2) =
      if (J c).1 = (I c).1 then AddMonoidAlgebra.single (∑ x ∈ (J c).1, Pi.single x (1 : ℤ)) 1 else 0 := by
    intro c
    rw [qb_evGL_minorC]
    change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
    rw [qb_minor_diagonal, qb_prod_single]
  simp only [hm]
  split_ifs with hJI
  · subst hJI
    simp only [if_true]
    rw [qb_prod_single, AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    funext a
    simp only [qb_wtT, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, card_filter,
      Nat.cast_sum, smul_eq_mul]
    simp
  · have : ∃ c, (J c).1 ≠ (I c).1 := by
      by_contra hc
      push Not at hc
      exact hJI (funext fun c => Subtype.ext (hc c))
    obtain ⟨c, hc⟩ := this
    rw [prod_eq_zero (mem_univ c) (if_neg hc), mul_zero]

lemma qb_equiv_apply {M : GLMod n} (CF : ColFam M) (j : CF.J) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, M.A i k * (CF.ph j k K : GLCoord ℤ n) = ∑ K', (CF.ph j i K' : GLCoord ℤ n) * TMat (CF.mu j) K' K :=
  congrFun (congrFun (CF.equiv j) i) K

theorem qb_prMu_ph {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, prMu M nu i k * CF.ph j k K = if qb_wtT (CF.mu j) K = nu then CF.ph j i K else 0 := by
  have h := congrArg (evGL (torusPt n)) (qb_equiv_apply CF j i K)
  simp only [map_sum, map_mul, Int.coe_castRingHom, map_intCast,
    qb_evGL_torus_TMat, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true] at h
  have h2 := congrArg (fun x => x.coeff nu) h
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul] at h2
  have hp : ∀ i k, prMu M nu i k = (evGL (torusPt n) (M.A i k)).coeff nu := fun _ _ => rfl
  simp only [hp]
  rw [mul_ite, mul_one, mul_zero] at h2
  rw [← h2]
  exact sum_congr rfl fun k _ => mul_comm _ _

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
