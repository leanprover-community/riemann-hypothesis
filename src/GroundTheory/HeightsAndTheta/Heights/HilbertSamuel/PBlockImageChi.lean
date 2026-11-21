import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageChi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiIndex

noncomputable section

open Module

variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem basis_det_eq {N : Type*} [AddCommGroup N] [Module ℤ N] {r : ℕ} (b : Basis (Fin r) ℤ N)
    (A : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → N) (hv : ∀ k, v k = ∑ l, A k l • b l) : b.det v = A.det := by
  classical
  rw [Basis.det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  rw [Matrix.transpose_apply, Basis.toMatrix_apply, hv i, map_sum]
  simp only [map_zsmul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem log_relIndex_sub {r : ℕ} {e e' : Fin r → Ω} (he : LinearIndependent ℤ e) (he' : LinearIndependent ℤ e')
    (T : Matrix (Fin r) (Fin r) ℚ) (hT : ∀ k, e' k = ∑ l, (T k l : Ω) * e l) (hdet : T.det ≠ 0) :
    Real.log ((Submodule.span ℤ (Set.range e)).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e')).toAddSubgroup) -
      Real.log ((Submodule.span ℤ (Set.range e')).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e)).toAddSubgroup) =
      -Real.log |(T.det : ℝ)| := by
  classical
  obtain ⟨c, hc0, hc⟩ := ChangeOfLattice.exists_clear_den T
  choose A hA using hc
  set L := Submodule.span ℤ (Set.range e) with hLdef
  set L' := Submodule.span ℤ (Set.range e') with hL'def
  set f : Fin r → Ω := fun k => (c : Ω) * e' k with hfdef
  have hAΩ : ∀ k l, (c : Ω) * (T k l : Ω) = (A k l : Ω) := fun k l => by
    have h := congrArg (fun q : ℚ => (q : Ω)) (hA k l)
    push_cast at h
    exact h
  have hf : ∀ k, f k = ∑ l, A k l • e l := by
    intro k
    simp only [hfdef, hT k, Finset.mul_sum, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, hAΩ]
  have hc0' : (c : Ω) ≠ 0 := by exact_mod_cast hc0
  have hfli : LinearIndependent ℤ f := ChangeOfLattice.linearIndependent_const_mul hc0' he'
  have hfc : ∀ k, f k = ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l • e' l := by
    intro k
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp [hfdef, zsmul_eq_mul]
  set M := Submodule.span ℤ (Set.range f) with hMdef
  have hML : M ≤ L := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hf k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML' : M ≤ L' := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hfc k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML₀ : M.toAddSubgroup ≤ L.toAddSubgroup := hML
  have hML'₀ : M.toAddSubgroup ≤ L'.toAddSubgroup := hML'

  have i1 : M.toAddSubgroup.relIndex L'.toAddSubgroup = (c ^ r : ℕ) := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L'.toAddSubgroup hML'₀ (Basis.span hfli)
      (Basis.span he')]
    refine (congrArg Int.natAbs (basis_det_eq _ ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) _ ?_)).trans ?_
    · intro k
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [AddSubgroupClass.coe_zsmul]
      show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
        ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l •
          ((Basis.span he' l : Submodule.span ℤ (Set.range e')) : Ω)
      simp only [Basis.coe_span_apply]
      exact hfc k
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast]
  have i2 : M.toAddSubgroup.relIndex L.toAddSubgroup = (Matrix.of A).det.natAbs := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L.toAddSubgroup hML₀ (Basis.span hfli)
      (Basis.span he)]
    refine congrArg Int.natAbs (basis_det_eq _ (Matrix.of A) _ fun k => ?_)
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [AddSubgroupClass.coe_zsmul, Matrix.of_apply]
    show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
      ∑ l, A k l • ((Basis.span he l : Submodule.span ℤ (Set.range e)) : Ω)
    simp only [Basis.coe_span_apply]
    exact hf k
  have hAdet : (((Matrix.of A).det : ℤ) : ℝ) = (c : ℝ) ^ r * (T.det : ℝ) := by
    have hmap : (Int.castRingHom ℚ).mapMatrix (Matrix.of A) = (c : ℚ) • T := by
      ext i j
      simp [← hA i j]
    have h1 : (((Matrix.of A).det : ℤ) : ℚ) = (c : ℚ) ^ r * T.det := by
      rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, hmap, Matrix.det_smul, Fintype.card_fin]
    rw [← Rat.cast_intCast, h1, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  have hcr : (c : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc0)
  have hTr : (T.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have h1 : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [i2]
    intro h0
    have : (((Matrix.of A).det : ℤ) : ℝ) = 0 := by
      rw [Int.natAbs_eq_zero.1 h0, Int.cast_zero]
    rw [hAdet] at this
    exact mul_ne_zero hcr hTr this
  have h2 : M.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 := by
    rw [i1]
    exact pow_ne_zero _ hc0
  rw [ChangeOfLattice.log_relIndex_cocycle hML₀ hML'₀ h1 h2, i1, i2, Nat.cast_natAbs, Int.cast_abs, hAdet, Nat.cast_pow]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ r), Real.log_mul hcr (abs_ne_zero.2 hTr)]
  ring

end

end ResChiIndex

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiIndex

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Forms

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem exists_int_mul (f : MvPolynomial J ℚ) :
    ∃ (N : ℕ) (g : MvPolynomial J ℤ), N ≠ 0 ∧ map (Int.castRingHom ℚ) g = C (N : ℚ) * f := by
  refine MvPolynomial.induction_on' f (fun u a => ?_) (fun p q hp hq => ?_)
  · refine ⟨a.den, monomial u a.num, a.den_nz, ?_⟩
    rw [map_monomial, C_mul_monomial, Rat.den_mul_eq_num]
    simp
  · obtain ⟨N₁, g₁, h₁, e₁⟩ := hp
    obtain ⟨N₂, g₂, h₂, e₂⟩ := hq
    refine ⟨N₁ * N₂, C (N₂ : ℤ) * g₁ + C (N₁ : ℤ) * g₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_C, map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring

theorem isHomogeneous_of_map {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n) {N : ℕ}
    {g : MvPolynomial J ℤ} (hg : map (Int.castRingHom ℚ) g = C (N : ℚ) * f) : g.IsHomogeneous n := by
  intro s hs
  apply hf
  intro h0
  apply hs
  have h := congrArg (coeff s) hg
  rw [coeff_map, coeff_C_mul, h0, mul_zero] at h
  simpa using h

theorem secFun_eq_zero {x : J → Ω} {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n)
    (hx : aeval x f = 0) {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) : secFun f z = 0 := by
  obtain ⟨N, g, hN, hg⟩ := exists_int_mul f
  have hgx : aeval x g = 0 := by
    rw [← aeval_map_int, hg, map_mul, hx, mul_zero]
  have h0 := hz.2 g (mem_coordIdeal_of_isHomogeneous ℤ x (isHomogeneous_of_map hf hg) hgx)
  have e : eval z (map (Int.castRingHom ℂ) g) = (N : ℂ) * secFun f z := by
    rw [show Int.castRingHom ℂ = (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) from RingHom.ext_int _ _,
      ← MvPolynomial.map_map, hg, secFun]
    simp
  rw [e] at h0
  exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hN)

theorem aeval_matSubst (B : Matrix J J ℚ) (x : J → Ω) (b : MvPolynomial J ℚ) :
    aeval x (matSubst B b) = aeval (matAct B x) b := by
  rw [matSubst, ← AlgHom.comp_apply, comp_aeval]
  refine congrArg (fun y => aeval y b) (funext fun i => ?_)
  simp [matAct]

theorem isHomogeneous_matSubst (B : Matrix J J ℚ) {b : MvPolynomial J ℚ} {n : ℕ} (hb : b.IsHomogeneous n) :
    (matSubst B b).IsHomogeneous n := by
  have hg : ∀ i, (∑ j, C (B i j) * X j : MvPolynomial J ℚ).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℚ j).C_mul _
  simpa [matSubst] using hb.aeval _ hg

theorem mem_span_rat_sec (A : Matrix J J ℚ) (x : J → Ω) (n : ℕ) :
    ∀ s ∈ sec ℤ (matAct A x) n, s ∈ Submodule.span ℚ (sec ℤ x n : Set Ω) := by
  intro s hs
  obtain ⟨c, hc0, hc⟩ := ChangeOfLattice.exists_clear_den A
  have hi : ∀ i, (c : ℤ) • matAct A x i ∈ Submodule.span ℤ (Set.range x) := by
    intro i
    have e : (c : ℤ) • matAct A x i = matAct ((c : ℚ) • A) x i := by
      simp [matAct, Finset.mul_sum, zsmul_eq_mul, mul_assoc]
    rw [e]
    refine ChangeOfLattice.matAct_mem_span (fun i j => ?_) x i
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, by rw [Matrix.smul_apply, smul_eq_mul, hk]⟩
  have hy : ∀ l ∈ Submodule.span ℤ (Set.range (matAct A x)), (c : ℤ) • l ∈ Submodule.span ℤ (Set.range x) := by
    intro l hl
    have hle : Submodule.span ℤ (Set.range (matAct A x)) ≤
        (Submodule.span ℤ (Set.range x)).comap ((c : ℤ) • LinearMap.id) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun i => by simpa using hi i)
    simpa using hle hl
  rw [ChangeOfLattice.sec_eq_pow] at hs
  have hcs := ChangeOfLattice.smul_pow_mem hy n s hs
  rw [← ChangeOfLattice.sec_eq_pow] at hcs
  have hc' : ((c : ℚ) ^ n : Ω) ≠ 0 := by exact_mod_cast pow_ne_zero n hc0
  have e2 : s = (((c : ℚ) ^ n)⁻¹ : ℚ) • ((c : ℤ) ^ n • s) := by
    rw [Rat.smul_def, zsmul_eq_mul]
    push_cast
    field_simp
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hcs)

end Forms

section Gram

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resGram_change (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → MvPolynomial (Ix κ) ℚ) (T : Matrix (Fin r) (Fin r) ℚ)
    (hc : ∀ k, ∀ z ∈ pts (coordIdeal ℤ d.x), secFun (c k) z = ∑ l, (T k l : ℂ) * secFun (b l) z) :
    resGram d n c = T.map (Rat.cast : ℚ → ℝ) * resGram d n b * (T.map (Rat.cast : ℚ → ℝ)).transpose := by

  have hpt : ∀ z ∈ pts (coordIdeal ℤ d.x), ∀ k l, pairVal d.m n (c k) (c l) z =
      ∑ i, ∑ j, ((T k i * T l j : ℚ) : ℂ) * pairVal d.m n (b i) (b j) z := by
    intro z hz k l
    have e1 : ∀ p q : MvPolynomial (Ix κ) ℚ, pairVal d.m n p q z =
        secFun p z * starRingEnd ℂ (secFun q z) / ((d.m.ρ z ^ (2 * n) : ℝ) : ℂ) := fun p q => rfl
    simp only [e1, hc k z hz, hc l z hz, map_sum, map_mul, map_ratCast, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_div]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring

  have hprob := d.vol.1
  have hpv : ∀ i j, pairVal d.m n (b i) (b j) = fun z =>
      starRingEnd ℂ (starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ)) :=
    fun i j => funext (ResSym.pairVal_eq_conj d.m n (b i) (b j))
  have hcont : ∀ i j, ContinuousOn (pairVal d.m n (b i) (b j)) {0}ᶜ := fun i j => by
    rw [hpv]
    exact Complex.continuous_conj.comp_continuousOn (ResSym.continuousOn_gramFun d.smooth n (b i) (b j))
  have hdeg : ∀ i j, ∀ (a : ℂ) z, a ≠ 0 → pairVal d.m n (b i) (b j) (a • z) = pairVal d.m n (b i) (b j) z :=
    fun i j a z ha => by
      rw [hpv]
      simp only
      rw [ResSym.gramFun_smul (hb i) (hb j) a z ha]
  have hint1 : ∀ i j, Integrable (fun y => pairVal d.m n (b i) (b j) (resPt d y)) d.dV := fun i j =>
    integrableOn_univ.1 ((ResSym.continuous_degZero_resPt d (hcont i j) (hdeg i j)).continuousOn.integrableOn_compact
      isCompact_univ)
  have hint2 : ∀ i j, Integrable (fun y => pairVal d.m n (b i) (b j) (conjPt (resPt d y))) d.dV := fun i j =>
    integrableOn_univ.1
      ((ResSym.continuous_degZero_conj_resPt d (hcont i j) (hdeg i j)).continuousOn.integrableOn_compact
        isCompact_univ)
  have hsum : ∀ (g : d.R.X → Ix κ → ℂ), (∀ y, g y ∈ pts (coordIdeal ℤ d.x)) →
      (∀ i j, Integrable (fun y => pairVal d.m n (b i) (b j) (g y)) d.dV) → ∀ k l,
      ∫ y, pairVal d.m n (c k) (c l) (g y) ∂d.dV =
        ∑ i, ∑ j, ((T k i * T l j : ℚ) : ℂ) * ∫ y, pairVal d.m n (b i) (b j) (g y) ∂d.dV := by
    intro g hg hgi k l
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hpt _ (hg y) k l),
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hgi i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hgi i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  ext k l
  rw [show resGram d n c k l = (1 / 2) * ((∫ y, pairVal d.m n (c k) (c l) (resPt d y) ∂d.dV).re +
      (∫ y, pairVal d.m n (c k) (c l) (conjPt (resPt d y)) ∂d.dV).re) from rfl,
    hsum (resPt d) (ResSym.resPt_mem_pts d) hint1,
    hsum (fun y => conjPt (resPt d y)) (fun y => ResSym.conjPt_mem_pts (ResSym.resPt_mem_pts d y)) hint2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [resGram, Complex.re_sum, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero,
    Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem resChi_sub_of_bases (d d' : HSMDatum D Ω κ) (B : Matrix (Ix κ) (Ix κ) ℚ) (hB : IsInvMat B)
    (hx : d'.x = matAct B d.x)
    (hG : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), resGram d' n b = resGram d n fun k => matSubst B (b k))
    (n : ℕ) {r r' : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} {b' : Fin r' → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis d.x n b) (hb' : IsSecBasis d'.x n b') :
    -(1 / 2) * Real.log (resGram d' n b').det - -(1 / 2) * Real.log (resGram d n b).det =
      latLogIndex d.x d'.x n := by
  classical
  have hli := linIndep_rat_of_isSecBasis hb
  have hli' := linIndep_rat_of_isSecBasis hb'
  obtain ⟨B', hB'B, -⟩ := ChangeOfLattice.exists_inv_of_isInvMat hB
  have hx' : d.x = matAct B' d'.x := by rw [hx, ChangeOfLattice.matAct_mul, hB'B, matAct_one]

  have hspan : ∀ {y : Ix κ → Ω} {s : ℕ} {c : Fin s → MvPolynomial (Ix κ) ℚ}, IsSecBasis y n c →
      Submodule.span ℚ (sec ℤ y n : Set Ω) = Submodule.span ℚ (Set.range fun i => aeval y (c i)) := by
    intro y s c hc
    rw [← hc.2.2, Submodule.span_span_of_tower]
  have hV : Submodule.span ℚ (Set.range fun k => aeval d'.x (b' k)) =
      Submodule.span ℚ (Set.range fun i => aeval d.x (b i)) := by
    apply le_antisymm
    · rw [← hspan hb, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine mem_span_rat_sec B d.x n _ ?_
      rw [← hx, ← hb'.2.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    · rw [← hspan hb', Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine mem_span_rat_sec B' d'.x n _ ?_
      rw [← hx', ← hb.2.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  have hrr : r' = r := by
    have h1 := finrank_span_eq_card hli
    have h2 := finrank_span_eq_card hli'
    rw [hV, h1] at h2
    simpa using h2.symm
  subst hrr

  have hmem : ∀ k, aeval d'.x (b' k) ∈ Submodule.span ℚ (Set.range fun i => aeval d.x (b i)) :=
    fun k => hV ▸ Submodule.subset_span ⟨k, rfl⟩
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun ℚ).1 (hmem k)
  have hTΩ : ∀ k, aeval d'.x (b' k) = ∑ l, ((Matrix.of T) k l : Ω) * aeval d.x (b l) := fun k => by
    rw [← hT k]
    simp only [Rat.smul_def, Matrix.of_apply]
  have hdet : (Matrix.of T).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv0
    have hrel : ∑ k, v k • aeval d'.x (b' k) = 0 := by
      calc ∑ k, v k • aeval d'.x (b' k)
          = ∑ l, (Matrix.vecMul v (Matrix.of T)) l • aeval d.x (b l) := by
            simp only [← hT, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul,
              Matrix.of_apply]
            exact Finset.sum_comm
        _ = 0 := by rw [hv]; simp
    funext k
    exact linearIndependent_iff'.1 hli' Finset.univ v hrel k (Finset.mem_univ k)

  have hidx : latLogIndex d.x d'.x n = -Real.log |((Matrix.of T).det : ℝ)| := by
    unfold latLogIndex
    rw [← hb.2.2, ← hb'.2.2]
    exact log_relIndex_sub hb.2.1 hb'.2.1 (Matrix.of T) hTΩ hdet

  have hpt : ∀ k, ∀ z ∈ pts (coordIdeal ℤ d.x), secFun (matSubst B (b' k)) z =
      ∑ l, ((Matrix.of T) k l : ℂ) * secFun (b l) z := by
    intro k z hz
    obtain ⟨f, hf, hfb⟩ := hb'.1 k
    have hh : (matSubst B (b' k) - ∑ l, C ((Matrix.of T) k l) * b l).IsHomogeneous n := by
      refine (isHomogeneous_matSubst B (hfb ▸ hf.map _)).sub
        (IsHomogeneous.sum _ _ _ fun l _ => ?_)
      obtain ⟨g, hg, hgb⟩ := hb.1 l
      rw [hgb]
      exact (hg.map _).C_mul _
    have hx0 : aeval d.x (matSubst B (b' k) - ∑ l, C ((Matrix.of T) k l) * b l) = 0 := by
      rw [map_sub, aeval_matSubst, ← hx, hTΩ k]
      simp
    have h0 := secFun_eq_zero hh hx0 hz
    simp only [secFun, map_sub, map_sum, map_mul, map_C, eval_C, eq_ratCast]
      at h0 ⊢
    exact sub_eq_zero.1 h0
  have hchange : resGram d' n b' =
      (Matrix.of T).map (Rat.cast : ℚ → ℝ) * resGram d n b * ((Matrix.of T).map (Rat.cast : ℚ → ℝ)).transpose := by
    rw [hG n _ b']
    exact resGram_change d hb.1 _ (Matrix.of T) hpt

  have hGpos : 0 < (resGram d n b).det := by
    rw [ResSym.det_resGram d hb.1]
    exact (Complex.pos_iff.1 (ResSym.posDef_gram d hb).det_pos).1
  have hTd : ((Matrix.of T).map (Rat.cast : ℚ → ℝ)).det = ((Matrix.of T).det : ℝ) :=
    (RingHom.map_det (Rat.castHom ℝ) (Matrix.of T)).symm
  have hTr : ((Matrix.of T).det : ℝ) ≠ 0 := by exact_mod_cast hdet
  rw [hidx, hchange, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hTd,
    show ((Matrix.of T).det : ℝ) * (resGram d n b).det * ((Matrix.of T).det : ℝ) =
      ((Matrix.of T).det : ℝ) ^ 2 * (resGram d n b).det by ring,
    Real.log_mul (pow_ne_zero 2 hTr) hGpos.ne', Real.log_pow, ← Real.log_abs ((Matrix.of T).det : ℝ)]
  push_cast
  ring

end Gram

theorem proof : ResChiIndex.Statement := by
  intro D Ω _ _ κ _ d d' B hB hx hG n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 :=
    ⟨⟨_, _⟩, (exists_isSecBasis d.x n).choose_spec⟩
  have h' : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d'.x n p.2 :=
    ⟨⟨_, _⟩, (exists_isSecBasis d'.x n).choose_spec⟩
  unfold resChi
  rw [dif_pos h, dif_pos h']
  exact resChi_sub_of_bases d d' B hB hx hG n h.choose_spec h'.choose_spec

end

end ResChiIndex

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockImageChi

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}

def blockSubst (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) : (Σ k, ι k) → MvPolynomial (Ix (Fin r)) ℤ :=
  fun p => if h : p.1 = k₀ then ∑ j, C (N (h ▸ p.2) j) * X j else 0

theorem blockSubst_block (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (i : ι k₀) :
    blockSubst k₀ N ⟨k₀, i⟩ = ∑ j, C (N i j) * X j := by
  simp [blockSubst]

theorem isHomogeneous_blockSubst (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (p : Σ k, ι k) :
    (blockSubst k₀ N p).IsHomogeneous 1 := by
  unfold blockSubst
  split_ifs
  · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℤ j).C_mul _
  · exact isHomogeneous_zero _ _ _

def fwd (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) : MRing ι →ₐ[ℤ] MvPolynomial (Ix (Fin r)) ℤ :=
  bind₁ (blockSubst k₀ N)

def fwdQ (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) :
    MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial (Ix (Fin r)) ℚ :=
  bind₁ fun p => map (Int.castRingHom ℚ) (blockSubst k₀ N p)

theorem fwdQ_map (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (f : MRing ι) :
    fwdQ k₀ N (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (fwd k₀ N f) := by
  rw [fwd, fwdQ, map_bind₁]

def back (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) : MvPolynomial (Ix (Fin r)) ℤ →ₐ[ℤ] MRing ι :=
  bind₁ (blockForms k₀ M)

def backQ (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) :
    MvPolynomial (Ix (Fin r)) ℚ →ₐ[ℚ] MvPolynomial (Σ k, ι k) ℚ :=
  bind₁ fun j => map (Int.castRingHom ℚ) (blockForms k₀ M j)

theorem backQ_map (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) (g : MvPolynomial (Ix (Fin r)) ℤ) :
    backQ k₀ M (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℚ) (back k₀ M g) := by
  rw [back, backQ, map_bind₁]

theorem fst_eq_of_mem_support {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    {c : (Σ k, ι k) →₀ ℕ} (hc : coeff c f ≠ 0) {p : Σ k, ι k} (hp : p ∈ c.support) : p.1 = k₀ := by
  by_contra hne
  have h := hf c (mem_support_iff.mpr hc) p.1
  rw [blockDeg, if_neg hne, Finset.sum_eq_zero_iff] at h
  exact (Finsupp.mem_support_iff.mp hp) (h p.2 (Finset.mem_univ _))

theorem isHomogeneous_of_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) :
    f.IsHomogeneous n := by
  intro c hc
  have h := hf c (mem_support_iff.mpr hc)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  simp only [Pi.one_apply, smul_eq_mul, mul_one, h, blockDeg, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem isHomogeneous_fwd (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) {f : MRing ι} {n : ℕ}
    (hf : IsMultiHomog f (blockDeg k₀ n)) : (fwd k₀ N f).IsHomogeneous n := by
  have := (isHomogeneous_of_blockDeg hf).aeval (blockSubst k₀ N) (isHomogeneous_blockSubst k₀ N)
  rw [one_mul, aeval_eq_bind₁] at this
  exact this

def wB : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_wB (c : (Σ k, ι k) →₀ ℕ) : Finsupp.weight wB c = fun k => ∑ i, c ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k (fun k' _ hk' => ?_) (by simp)]
  · simp [wB]
  · simp [wB, Ne.symm hk']

theorem isMultiHomog_iff_wB (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous wB f a := by
  constructor
  · intro h c hc
    rw [weight_wB]
    funext k
    exact h c (mem_support_iff.mpr hc) k
  · intro h c hc k
    have := h (mem_support_iff.mp hc)
    rw [weight_wB] at this
    exact congrFun this k

theorem isMultiHomog_back (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) {g : MvPolynomial (Ix (Fin r)) ℤ} {n : ℕ}
    (hg : g.IsHomogeneous n) : IsMultiHomog (back k₀ M g) (blockDeg k₀ n) := by
  have hbf : ∀ j, IsWeightedHomogeneous wB (blockForms k₀ M j) (Pi.single k₀ 1) := fun j =>
    IsWeightedHomogeneous.sum _ _ _ fun i _ => (isWeightedHomogeneous_X ℤ wB (⟨k₀, i⟩ : Σ k, ι k)).C_mul _
  rw [isMultiHomog_iff_wB, show blockDeg k₀ n = n • Pi.single k₀ 1 by
    funext k; by_cases hk : k = k₀ <;> simp [blockDeg, hk]]
  rw [back, ← aeval_eq_bind₁, aeval_def]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [← zero_add (n • Pi.single k₀ 1)]
  apply IsWeightedHomogeneous.mul (by rw [MvPolynomial.algebraMap_eq]; exact isWeightedHomogeneous_C _ _)
  rw [Finsupp.mem_support_iff] at hd
  have hn : ∑ j ∈ d.support, d j = n := by
    have := hg hd
    rw [Finsupp.weight_apply] at this
    simpa [Finsupp.sum] using this
  have hp := IsWeightedHomogeneous.prod d.support (fun j => blockForms k₀ M j ^ d j)
    (fun j => d j • Pi.single k₀ 1) fun j _ => (hbf j).pow (d j)
  rw [← Finset.sum_smul, hn] at hp
  exact hp

end Forms

section Values

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem aeval_mapQ {J : Type} (v : J → Ω) (f : MvPolynomial J ℤ) :
    aeval v (map (Int.castRingHom ℚ) f) = aeval v f := by
  have : Int.castRingHom ℚ = algebraMap ℤ ℚ := RingHom.ext_int _ _
  rw [this, aeval_map_algebraMap]

theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) : aeval y g = 0 := by
  have e : ∀ g : MRing ι, eval (fun _ : K => (1 : Ω)) (mConeMap y g) = aeval y g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  rw [mCoordIdeal, RingHom.mem_ker] at hg
  rw [← e, hg, map_zero]

variable {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix (Fin r)) (ι k₀) ℤ} {N : Matrix (ι k₀) (Ix (Fin r)) ℤ}
  {x : Ix (Fin r) → Ω}

theorem back_fwd_sub_mem (h : IsBlockImage y k₀ M N x) {f : MRing ι} {n : ℕ}
    (hf : IsMultiHomog f (blockDeg k₀ n)) : back k₀ M (fwd k₀ N f) - f ∈ mCoordIdeal y := by
  rw [← Ideal.Quotient.eq]
  have e1 : back k₀ M (fwd k₀ N f) = bind₁ (fun p => back k₀ M (blockSubst k₀ N p)) f := by
    simp only [back, fwd, bind₁_bind₁]
  have e2 : f = bind₁ X f := by rw [bind₁_X_left]; rfl
  rw [e1]
  conv_rhs => rw [e2]
  rw [hom_bind₁, hom_bind₁, coe_eval₂Hom, coe_eval₂Hom]
  refine eval₂_congr _ _ _ fun {p} {c} hp hc => ?_
  obtain ⟨k, i⟩ := p
  have hk : k = k₀ := fst_eq_of_mem_support hf hc hp
  subst hk
  have e3 : back k M (∑ j, C (N i j) * X j) = ∑ j, C (N i j) * blockForms k M j := by
    simp [back]
  rw [blockSubst_block, e3]
  exact (Ideal.Quotient.eq.mpr (BlockImageTop.sub_mem_mCoordIdeal h i)).symm

theorem aeval_back (h : IsBlockImage y k₀ M N x) (g : MvPolynomial (Ix (Fin r)) ℤ) :
    aeval y (back k₀ M g) = aeval x g := by
  have hx : (fun j => aeval y (blockForms k₀ M j)) = x := funext fun j => by simp [blockForms, h.1 j]
  rw [back, aeval_bind₁, hx]

theorem aeval_fwd (h : IsBlockImage y k₀ M N x) {f : MRing ι} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) :
    aeval x (fwd k₀ N f) = aeval y f := by
  have h0 := aeval_eq_zero_of_mem (back_fwd_sub_mem h hf)
  rw [map_sub, sub_eq_zero, aeval_back h] at h0
  exact h0

theorem eval_fwd (h : IsBlockImage y k₀ M N x) {f : MRing ι} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) (fwd k₀ N f)) = eval z (map (Int.castRingHom ℂ) f) := by
  have e : ∀ g : MvPolynomial (Ix (Fin r)) ℤ,
      eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) g) = eval z (map (Int.castRingHom ℂ) (back k₀ M g)) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [back]
    | add p q hp hq => rw [map_add, map_add, map_add, map_add, map_add, hp, hq]
    | mul_X p j hp =>
      rw [map_mul, map_mul, map_mul, map_mul, map_mul, hp]
      simp [back, blockForms, blockMapC]
  rw [e]
  have h0 := hz.2 _ (back_fwd_sub_mem h hf)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

theorem secM_eq (h : IsBlockImage y k₀ M N x) (n : ℕ) :
    secM y (blockDeg k₀ n) = (sec ℤ x n).toAddSubgroup := by
  unfold secM
  congr 1
  have hset : {s | ∃ g : MRing ι, IsMultiHomog g (blockDeg k₀ n) ∧ aeval y g = s} =
      ((sec ℤ x n : Submodule ℤ Ω) : Set Ω) := by
    ext s
    simp only [Set.mem_ofPred_eq, sec, Submodule.map_coe, Set.mem_image, SetLike.mem_coe,
      mem_homogeneousSubmodule, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨fwd k₀ N g, isHomogeneous_fwd k₀ N hg, aeval_fwd h hg⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨back k₀ M g, isMultiHomog_back k₀ M hg, aeval_back h g⟩
  rw [hset, Submodule.span_eq]

theorem isSecBasis_fwd (h : IsBlockImage y k₀ M N x) {n s : ℕ} {b : Fin s → MvPolynomial (Σ k, ι k) ℚ}
    (hb : IsSecBasisM y k₀ n b) : IsSecBasis x n fun j => fwdQ k₀ N (b j) := by
  have hv : (fun j => aeval x (fwdQ k₀ N (b j))) = fun j => aeval y (b j) := by
    funext j
    obtain ⟨f, hf, hbf⟩ := hb.1 j
    rw [hbf, fwdQ_map, aeval_mapQ, aeval_mapQ, aeval_fwd h hf]
  refine ⟨fun j => ?_, ?_, ?_⟩
  · obtain ⟨f, hf, hbf⟩ := hb.1 j
    exact ⟨fwd k₀ N f, isHomogeneous_fwd k₀ N hf, by show fwdQ k₀ N (b j) = _; rw [hbf, fwdQ_map]⟩
  · show LinearIndependent ℤ fun j => aeval x (fwdQ k₀ N (b j))
    rw [hv]
    exact hb.2.1
  · show Submodule.span ℤ (Set.range fun j => aeval x (fwdQ k₀ N (b j))) = sec ℤ x n
    rw [hv]
    apply Submodule.toAddSubgroup_injective
    rw [hb.2.2, secM_eq h]

theorem isSecBasisM_back (h : IsBlockImage y k₀ M N x) {n s : ℕ} {b : Fin s → MvPolynomial (Ix (Fin r)) ℚ}
    (hb : IsSecBasis x n b) : IsSecBasisM y k₀ n fun j => backQ k₀ M (b j) := by
  have hv : (fun j => aeval y (backQ k₀ M (b j))) = fun j => aeval x (b j) := by
    funext j
    obtain ⟨f, hf, hbf⟩ := hb.1 j
    rw [hbf, backQ_map, aeval_mapQ, aeval_mapQ, aeval_back h]
  refine ⟨fun j => ?_, ?_, ?_⟩
  · obtain ⟨f, hf, hbf⟩ := hb.1 j
    exact ⟨back k₀ M f, isMultiHomog_back k₀ M hf, by show backQ k₀ M (b j) = _; rw [hbf, backQ_map]⟩
  · show LinearIndependent ℤ fun j => aeval y (backQ k₀ M (b j))
    rw [hv]
    exact hb.2.1
  · show (Submodule.span ℤ (Set.range fun j => aeval y (backQ k₀ M (b j)))).toAddSubgroup = _
    rw [hv, hb.2.2, secM_eq h]

end Values

section Points

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem conjPt_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : conjPt z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa [conjPt] using hi⟩
  · rw [ResSym.eval_conjPt_map_int, hz.2 f hf, map_zero]

theorem blockMapC_conjPt (k₀ : K) {J : Type} [Fintype J] (M : Matrix J (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) :
    blockMapC k₀ M (conjPt z) = conjPt (blockMapC k₀ M z) := by
  funext j
  simp [blockMapC, conjPt, map_sum]

end Points

section Gram

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω]

theorem det_resGram_eq {κ : Type} [Fintype κ] (d : HSMDatum D Ω κ) {n s : ℕ}
    {b b' : Fin s → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis d.x n b) (hb' : IsSecBasis d.x n b') :
    (resGram d n b').det = (resGram d n b).det := by
  have hT : ∀ {c c' : Fin s → MvPolynomial (Ix κ) ℚ}, IsSecBasis d.x n c → IsSecBasis d.x n c' →
      ∃ A : Matrix (Fin s) (Fin s) ℤ, resGram d n c' =
        A.map (Int.cast : ℤ → ℝ) * resGram d n c * (A.map (Int.cast : ℤ → ℝ)).transpose := by
    intro c c' hc hc'
    have hmem : ∀ k, ∃ a : Fin s → ℤ, ∑ l, a l • aeval d.x (c l) = aeval d.x (c' k) := by
      intro k
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mp ?_
      rw [hc.2.2, ← hc'.2.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    choose A hA using hmem
    refine ⟨Matrix.of A, ?_⟩
    have e := ResChiIndex.resGram_change d hc.1 c' ((Matrix.of A).map (Int.cast : ℤ → ℚ)) fun k z hz => by
      choose f hf hbf using hc.1
      obtain ⟨f', hf', hbf'⟩ := hc'.1 k
      let q : MvPolynomial (Ix κ) ℤ := f' - ∑ l, C (A k l) * f l
      have hq : q.IsHomogeneous n := by
        refine hf'.sub (IsHomogeneous.sum _ _ _ fun l _ => ?_)
        simpa using (isHomogeneous_C (Ix κ) (A k l)).mul (hf l)
      have hq0 : aeval d.x q = 0 := by
        simp only [q, map_sub, map_sum, map_mul, eq_intCast]
        rw [← aeval_map_int, ← hbf', ← hA k]
        simp [zsmul_eq_mul, hbf, aeval_map_int, map_intCast]
      have h0 := secFun_eq_zero_of_pts hq hq0 hz
      rw [secFun_map_int] at h0
      simp only [Matrix.map_apply, Matrix.of_apply, Rat.cast_intCast, hbf', hbf, secFun_map_int]
      simpa [q, sub_eq_zero] using h0
    have hm : ((Matrix.of A).map (Int.cast : ℤ → ℚ)).map (Rat.cast : ℚ → ℝ) =
        (Matrix.of A).map (Int.cast : ℤ → ℝ) := by
      ext i j
      simp
    rw [e, hm]
  obtain ⟨A, hA⟩ := hT hb hb'
  obtain ⟨B, hB⟩ := hT hb' hb
  have hdA : (A.map (Int.cast : ℤ → ℝ)).det = (A.det : ℝ) := ((Int.castRingHom ℝ).map_det A).symm
  have hdB : (B.map (Int.cast : ℤ → ℝ)).det = (B.det : ℝ) := ((Int.castRingHom ℝ).map_det B).symm
  have d1 : (resGram d n b').det = (A.det : ℝ) ^ 2 * (resGram d n b).det := by
    rw [hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdA]
    ring
  have d2 : (resGram d n b).det = (B.det : ℝ) ^ 2 * (resGram d n b').det := by
    rw [hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdB]
    ring
  have hG : (resGram d n b).det ≠ 0 := by
    rw [ResSym.det_resGram d hb.1]
    exact (Complex.pos_iff.mp (ResSym.posDef_gram d hb).det_pos).1.ne'
  have h3 : ((A.det * B.det : ℤ) : ℝ) ^ 2 = 1 := by
    refine mul_right_cancel₀ hG ?_
    rw [one_mul]
    conv_rhs => rw [d2, d1]
    push_cast
    ring
  have h4 : A.det ^ 2 * B.det ^ 2 = 1 := by
    rw [← mul_pow]
    exact_mod_cast h3
  have h5 : (A.det : ℝ) ^ 2 = 1 := by
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (sq_nonneg _) h4
  rw [d1, h5, one_mul]

theorem resChi_eq_of_basis {κ : Type} [Fintype κ] (d : HSMDatum D Ω κ) {n s : ℕ}
    {b : Fin s → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis d.x n b) :
    resChi d n = -(1 / 2) * Real.log (resGram d n b).det := by
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 := ⟨⟨s, b⟩, hb⟩
  unfold resChi
  rw [dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨s', b'⟩ := p
  have hp' : IsSecBasis d.x n b' := hp
  have hs : s' = s := hp'.card_eq.trans hb.card_eq.symm
  subst hs
  rw [det_resGram_eq d hb hp']

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}

theorem blockGram_eq (d₀ : HSMBlockDatum D K ι Ω) (M : Matrix (Ix (Fin r)) (ι d₀.k₀) ℤ)
    (N : Matrix (ι d₀.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)) (hIm : IsBlockImage d₀.y d₀.k₀ M N d'.x)
    (hmet : ∀ z ∈ mcPts (mCoordIdeal d₀.y), d₀.A.h z = d'.m.ρ (blockMapC d₀.k₀ M z))
    (hint : ∀ g : (Ix (Fin r) → ℂ) → ℂ, ContinuousOn g {0}ᶜ → (∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) →
      ∫ a, g (resPt d' a) ∂d'.dV = ∫ a, g (blockMapC d₀.k₀ M (blockPt d₀ a)) ∂d₀.dV)
    (n : ℕ) {s : ℕ} (b : Fin s → MvPolynomial (Σ k, ι k) ℚ)
    (hb : ∀ j, ∃ f : MRing ι, IsMultiHomog f (blockDeg d₀.k₀ n) ∧ b j = map (Int.castRingHom ℚ) f) :
    blockGram d₀ n b = resGram d' n fun j => fwdQ d₀.k₀ N (b j) := by
  set bt : Fin s → MvPolynomial (Ix (Fin r)) ℚ := fun j => fwdQ d₀.k₀ N (b j) with hbt_def
  have hbt : ∀ j, ∃ f : MvPolynomial (Ix (Fin r)) ℤ, f.IsHomogeneous n ∧ bt j = map (Int.castRingHom ℚ) f := by
    intro j
    obtain ⟨f, hf, hbf⟩ := hb j
    exact ⟨fwd d₀.k₀ N f, isHomogeneous_fwd d₀.k₀ N hf, by rw [hbt_def]; simp only; rw [hbf, fwdQ_map]⟩
  have hval : ∀ j, ∀ z ∈ mcPts (mCoordIdeal d₀.y),
      eval (blockMapC d₀.k₀ M z) (map (algebraMap ℚ ℂ) (bt j)) = eval z (map (algebraMap ℚ ℂ) (b j)) := by
    intro j z hz
    obtain ⟨f, hf, hbf⟩ := hb j
    have e1 := secFun_map_int (fwd d₀.k₀ N f) (blockMapC d₀.k₀ M z)
    have e2 := secFun_map_int f z
    unfold secFun at e1 e2
    rw [hbt_def]
    simp only
    rw [hbf, fwdQ_map, e1, e2]
    exact eval_fwd hIm hf hz
  have hpt : ∀ z ∈ mcPts (mCoordIdeal d₀.y), ∀ k l,
      pairValH d₀.A n (b k) (b l) z = pairVal d'.m n (bt k) (bt l) (blockMapC d₀.k₀ M z) := by
    intro z hz k l
    simp only [pairValH, pairVal]
    rw [hval k z hz, hval l z hz, hmet z hz]
  have hpv : ∀ k l, pairVal d'.m n (bt k) (bt l) = fun w =>
      starRingEnd ℂ (starRingEnd ℂ (secFun (bt k) w) * secFun (bt l) w * (wgt d'.m n w : ℂ)) :=
    fun k l => funext (ResSym.pairVal_eq_conj d'.m n (bt k) (bt l))
  have hcont : ∀ k l, ContinuousOn (pairVal d'.m n (bt k) (bt l)) {0}ᶜ := fun k l => by
    rw [hpv]
    exact Complex.continuous_conj.comp_continuousOn (ResSym.continuousOn_gramFun d'.smooth n (bt k) (bt l))
  have hdeg : ∀ k l, ∀ (c : ℂ) w, c ≠ 0 →
      pairVal d'.m n (bt k) (bt l) (c • w) = pairVal d'.m n (bt k) (bt l) w := fun k l c w hc => by
    rw [hpv]
    simp only
    rw [ResSym.gramFun_smul (hbt k) (hbt l) c w hc]
  have hcont' : ∀ k l, ContinuousOn (fun w => pairVal d'.m n (bt k) (bt l) (conjPt w)) {0}ᶜ := fun k l =>
    (hcont k l).comp continuous_conjPt.continuousOn fun w hw => ResSym.conjPt_ne_zero hw
  have hdeg' : ∀ k l, ∀ (c : ℂ) w, c ≠ 0 →
      pairVal d'.m n (bt k) (bt l) (conjPt (c • w)) = pairVal d'.m n (bt k) (bt l) (conjPt w) :=
    fun k l c w hc => by
      rw [ResSym.conjPt_smul]
      exact hdeg k l _ _ ((map_ne_zero _).mpr hc)
  have hmem : ∀ a, blockPt d₀ a ∈ mcPts (mCoordIdeal d₀.y) := fun a => d₀.R.mem a a (d₀.R.mem_U a)
  ext k l
  have h1 : ∫ a, pairVal d'.m n (bt k) (bt l) (resPt d' a) ∂d'.dV =
      ∫ a, pairValH d₀.A n (b k) (b l) (blockPt d₀ a) ∂d₀.dV := by
    refine (hint _ (hcont k l) (hdeg k l)).trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => (hpt _ (hmem a) k l).symm)
  have h2 : ∫ a, pairVal d'.m n (bt k) (bt l) (conjPt (resPt d' a)) ∂d'.dV =
      ∫ a, pairValH d₀.A n (b k) (b l) (conjPt (blockPt d₀ a)) ∂d₀.dV := by
    refine (hint (fun w => pairVal d'.m n (bt k) (bt l) (conjPt w)) (hcont' k l) (hdeg' k l)).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [← blockMapC_conjPt]
    exact (hpt _ (conjPt_mem_mcPts (hmem a)) k l).symm
  simp only [blockGram, resGram]
  rw [h1, h2]

end Gram

end BlockImageChi

theorem BlockImageChi.proof : BlockImageChi.Statement := by
  intro D K _ _ ι _ Ω _ _ d₀ r M N d' hIm hmet hint n
  by_cases h : ∃ p : (Σ s : ℕ, Fin s → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d₀.y d₀.k₀ n p.2
  · have hb := h.choose_spec
    unfold blockChi
    rw [dif_pos h, BlockImageChi.blockGram_eq d₀ M N d' hIm hmet hint n _ hb.1,
      BlockImageChi.resChi_eq_of_basis d' (BlockImageChi.isSecBasis_fwd hIm hb)]
  · have h' : ¬ ∃ p : (Σ s : ℕ, Fin s → MvPolynomial (Ix (Fin r)) ℚ), IsSecBasis d'.x n p.2 := by
      rintro ⟨p, hp⟩
      exact h ⟨⟨p.1, fun j => BlockImageChi.backQ d₀.k₀ M (p.2 j)⟩, BlockImageChi.isSecBasisM_back hIm hp⟩
    unfold blockChi resChi
    rw [dif_neg h, dif_neg h']

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
