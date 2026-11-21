import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder Matrix

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem IsFrame.ds_spanK_eq {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span K (Set.range v) = Submodule.span K (E : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  · exact Submodule.span_le.mpr hv.2.2

theorem IsFrame.length_eq_latticeRank {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    r = latRank K E := by
  unfold latRank
  rw [← hv.ds_spanK_eq, finrank_span_eq_card hv.2.1, Fintype.card_fin]

theorem exists_isFullRankFamily_of_fg (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ r, ∃ v : Fin r → V, IsFrame K E v := by
  obtain ⟨S, hS⟩ := hE
  obtain ⟨b, hbE, hspan, hli⟩ := exists_linearIndependent K (E : Set V)
  have hEle : ∀ x ∈ E, x ∈ Submodule.span K (S : Set V) := by
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ (S : Set V) ?_
    rintro _ ⟨x, rfl⟩
    exact hEle _ (hbE x.2)
  let _ := Fintype.ofFinite b
  refine ⟨Fintype.card b, fun i => ((Fintype.equivFin b).symm i : V), ?_, ?_, ?_⟩
  · intro i; exact hbE ((Fintype.equivFin b).symm i).2
  · exact hli.comp _ (Fintype.equivFin b).symm.injective
  · intro x hx
    have : x ∈ Submodule.span K (b : Set V) := hspan ▸ Submodule.subset_span hx
    have hr : Set.range (fun i => ((Fintype.equivFin b).symm i : V)) = b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin b).symm i).2
      · intro hy; exact ⟨Fintype.equivFin b ⟨y, hy⟩, by simp⟩
    rw [SetLike.mem_coe, hr]
    exact this

theorem IsFrame.relIndex_span_frame_ne_zero {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  classical
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  set H := S.toAddSubgroup.addSubgroupOf E.toAddSubgroup with hH
  have : Module.Finite (𝓞 K) E := Module.Finite.iff_fg.mpr hE
  have : Module.Finite ℤ E := Module.Finite.trans (𝓞 K) E
  have hfg : AddGroup.FG E := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hfg' : AddGroup.FG E.toAddSubgroup := hfg
  have : Module.Finite ℤ E.toAddSubgroup := Module.Finite.iff_addGroup_fg.mpr hfg'
  have : Module.Finite ℤ (E.toAddSubgroup ⧸ H) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' H).toIntLinearMap
      (QuotientAddGroup.mk'_surjective H)
  have : Finite (E.toAddSubgroup ⧸ H) := by
    apply Module.finite_of_fg_torsion
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hv.2.2 x.2)
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
      have hd : ∀ i, IsIntegral ℤ (y • c i) := fun i => hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i))
      let d : Fin r → 𝓞 K := fun i => ⟨y • c i, hd i⟩
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      have hmem : (y • (x : V)) ∈ S := by
        have : y • (x : V) = ∑ i, d i • v i := by
          rw [← hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← algebraMap_smul K (d i) (v i), ← smul_assoc]
          rfl
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      show (y : ℤ) • (QuotientAddGroup.mk x : E.toAddSubgroup ⧸ H) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact hmem
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.ds_form_zero_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have := h.add_right σ x 0 0
  rw [add_zero] at this
  linear_combination -this

theorem HermFam.ds_form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.ds_form_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, ih]

theorem HermFam.ds_form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by
  rw [← h.conj_symm, h.ds_form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => h.conj_symm σ y (f i)

theorem HermFam.ds_form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.ds_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    h.gram σ (fun j => ∑ i, G i j • v i) = (G.map σ)ᴴ * h.gram σ v * G.map σ := by
  ext a b
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right,
    Finset.sum_mul, Complex.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem HermFam.ds_gram_det_re_pos (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) : 0 < (h.gram σ v).det.re := by
  have := (h.posDef σ r v hv).det_pos
  exact (Complex.pos_iff.mp this).1

theorem HermFam.ds_gram_comb_det_re (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Complex.normSq (σ G.det) * (h.gram σ v).det.re := by
  rw [h.ds_gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, RingHom.map_det]
  have : star (σ.mapMatrix G).det * (h.gram σ v).det * (σ.mapMatrix G).det =
      (Complex.normSq (σ.mapMatrix G).det : ℂ) * (h.gram σ v).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
  rw [RingHom.mapMatrix_apply] at this ⊢
  rw [this, Complex.re_ofReal_mul]

theorem HermFam.ds_log_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (G : Matrix (Fin r) (Fin r) K) (hG : G.det ≠ 0) :
    Real.log (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Real.log (Complex.normSq (σ G.det)) + Real.log (h.gram σ v).det.re := by
  rw [h.ds_gram_comb_det_re, Real.log_mul]
  · exact (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hG)).ne'
  · exact (h.ds_gram_det_re_pos σ hv).ne'

end

section
variable {K : Type*} [Field K] [NumberField K]

theorem ds_prod_embeddings_eq_norm (x : K) :
    ∏ σ : K →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => by simp [RingHom.equivRatAlgHom_apply])

theorem ds_sum_log_normSq_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) = 2 * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)).ne'),
    ← map_prod, ds_prod_embeddings_eq_norm]
  have hn : (Algebra.norm ℚ x : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hn hn,
    Real.log_abs]
  ring

end

end ReciprocityTheory.GeometryOfNumbersTheory
end

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder Matrix

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ds_relIndex_span_comb {r : ℕ} {v : Fin r → V} (hv : LinearIndependent K v)
    (g : Matrix (Fin r) (Fin r) (𝓞 K)) (hg : g.det ≠ 0) :
    (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = (Algebra.norm ℤ g.det).natAbs := by
  classical
  have hvO : LinearIndependent (𝓞 K) v := hv.restrict_scalars' (𝓞 K)
  let Φ : (Fin r → 𝓞 K) →+ V :=
    { toFun := fun c => ∑ i, c i • v i
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have hΦ : ∀ c, Φ c = ∑ i, c i • v i := fun c => rfl
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h0 : ∑ i, (a - b) i • v i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [← hΦ, ← hΦ, hab, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hvO _ h0 i)
  have hrange : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = AddSubgroup.map Φ ⊤ := by
    rw [← AddMonoidHom.range_eq_map]
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_range,
      Submodule.mem_span_range_iff_exists_fun, hΦ]
  have hcomb : ∀ d : Fin r → 𝓞 K, Φ (g.mulVec d) = ∑ j, d j • ∑ i, g i j • v i := by
    intro d
    simp only [hΦ, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hcomap : AddSubgroup.comap Φ
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup =
      (LinearMap.range (Matrix.mulVecLin g)).toAddSubgroup := by
    ext c
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
      Matrix.mulVecLin_apply, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, hΦinj (by rw [hcomb, hd])⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, (hcomb d).symm⟩
  have hTinj : Function.Injective (Matrix.mulVecLin g) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hc0
    exact hg (Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc0, hc⟩)
  let T : (Fin r → 𝓞 K) →ₗ[ℤ] (Fin r → 𝓞 K) := (Matrix.mulVecLin g).restrictScalars ℤ
  let N : Submodule ℤ (Fin r → 𝓞 K) := LinearMap.range T
  let e : (Fin r → 𝓞 K) ≃ₗ[ℤ] N := LinearEquiv.ofInjective T hTinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ ((e : (Fin r → 𝓞 K) →+ N)).toIntLinearMap = T :=
    LinearMap.ext fun c => rfl
  rw [hcomp] at hcard
  have hdetT : LinearMap.det T = Algebra.norm ℤ g.det := by
    rw [LinearMap.det_restrictScalars, ← LinearMap.det_toLin' g]
    rfl
  calc _ = (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup.relIndex
        (AddSubgroup.map Φ ⊤) := by rw [hrange]
    _ = (AddSubgroup.comap Φ (Submodule.span (𝓞 K)
          (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup).relIndex ⊤ :=
        (AddSubgroup.relIndex_comap _ _ _).symm
    _ = (LinearMap.range (Matrix.mulVecLin g)).toAddSubgroup.index := by
        rw [AddSubgroup.relIndex_top_right, hcomap]
    _ = Nat.card ((Fin r → 𝓞 K) ⧸ N) := rfl
    _ = _ := by rw [← hcard, hdetT]

theorem ds_det_ne_zero_of_comb {r : ℕ} {v : Fin r → V} (g : Matrix (Fin r) (Fin r) (𝓞 K))
    (hv' : LinearIndependent K (fun j => ∑ i, g i j • v i)) : g.det ≠ 0 := by
  classical
  intro hdet
  have hG : (g.map (algebraMap (𝓞 K) K)).det = 0 := by
    have h1 := RingHom.map_det (algebraMap (𝓞 K) K) g
    rw [hdet, map_zero] at h1
    exact h1.symm
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG
  apply hc0
  have hconv : (fun j => ∑ i, g i j • v i) =
      fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i := by
    funext j
    simp only [Matrix.map_apply, algebraMap_smul]
  rw [hconv] at hv'
  have hsum : ∑ j, c j • ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i =
      ∑ i, ((g.map (algebraMap (𝓞 K) K)).mulVec c) i • v i := by
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [hc] at hsum
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hsum
  funext j
  exact Fintype.linearIndependent_iff.1 hv' c hsum j

theorem degreeOfFamily_linearCombination (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (g : Matrix (Fin r) (Fin r) (𝓞 K))
    (hv' : LinearIndependent K (fun j => ∑ i, g i j • v i))
    (hvE : Submodule.span (𝓞 K) (Set.range v) ≤ E)
    (hne : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0) :
    degreeOfFamily h E (fun j => ∑ i, g i j • v i) = degreeOfFamily h E v := by
  classical
  have hg := ds_det_ne_zero_of_comb g hv'
  have hle : Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i) ≤
      Submodule.span (𝓞 K) (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hle)
    ((Submodule.toAddSubgroup_le _ _).2 hvE)
  rw [ds_relIndex_span_comb hv g hg] at hmul
  have hconv : (fun j => ∑ i, g i j • v i) =
      fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i := by
    funext j
    simp only [Matrix.map_apply, algebraMap_smul]
  have hdetmap : algebraMap (𝓞 K) K g.det = (g.map (algebraMap (𝓞 K) K)).det :=
    RingHom.map_det (algebraMap (𝓞 K) K) g
  have hGdet : (g.map (algebraMap (𝓞 K) K)).det ≠ 0 := by
    rw [← hdetmap]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hg
  have hsum : ∑ σ : K →+* ℂ, Real.log (h.gram σ (fun j => ∑ i, g i j • v i)).det.re =
      2 * Real.log |(Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ)| +
        ∑ σ : K →+* ℂ, Real.log (h.gram σ v).det.re := by
    rw [hconv, ← ds_sum_log_normSq_embeddings _ hGdet, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => h.ds_log_gram_comb σ hv _ hGdet
  have hnorm : (Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ) =
      ((Algebra.norm ℤ g.det : ℤ) : ℝ) := by
    rw [← hdetmap]
    have h1 := Algebra.coe_norm_int g.det
    have h2 : ((Algebra.norm ℚ (algebraMap (𝓞 K) K g.det) : ℚ) : ℝ) =
        (((Algebra.norm ℤ g.det : ℤ) : ℚ) : ℝ) := by
      rw [h1]
    rw [h2]
    push_cast
    rfl
  have hne1 : (((Algebra.norm ℤ g.det).natAbs : ℕ) : ℝ) ≠ 0 := by
    have : Algebra.norm ℤ g.det ≠ 0 := Algebra.norm_ne_zero_iff.2 hg
    exact_mod_cast Int.natAbs_ne_zero.2 this
  have hne2 : (((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℕ) : ℝ)
      ≠ 0 := by exact_mod_cast hne
  unfold degreeOfFamily
  rw [← hmul, Nat.cast_mul, Real.log_mul hne1 hne2, hsum, hnorm, Nat.cast_natAbs, Int.cast_abs]
  ring

theorem degreeOfFamily_eq_of_isFullRankFamily (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ}
    {v v' : Fin r → V} (hv : IsFrame K E v) (hv' : IsFrame K E v') :
    degreeOfFamily h E v = degreeOfFamily h E v' := by
  classical
  obtain ⟨hvE, hvli, hvsp⟩ := hv
  obtain ⟨hv'E, hv'li, hv'sp⟩ := hv'
  have hneV := IsFrame.relIndex_span_frame_ne_zero hE ⟨hvE, hvli, hvsp⟩
  have hneV' := IsFrame.relIndex_span_frame_ne_zero hE ⟨hv'E, hv'li, hv'sp⟩
  have hc : ∀ j, ∃ c : Fin r → K, ∑ i, c i • v i = v' j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hvsp (hv'E j))
  choose c hc using hc
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin r × Fin r => c p.2 p.1)
  have hint : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (b : 𝓞 K) • c j i := fun i j =>
    hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  choose gm hgm using hint
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  let g : Matrix (Fin r) (Fin r) (𝓞 K) := Matrix.of gm
  let g₂ : Matrix (Fin r) (Fin r) (𝓞 K) := Matrix.diagonal fun _ => (b : 𝓞 K)
  have hu : (fun j => ∑ i, g i j • v i) = fun j => (b : 𝓞 K) • v' j := by
    funext j
    rw [← hc j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show gm i j • v i = (b : 𝓞 K) • (c j i • v i)
    rw [← algebraMap_smul K (gm i j) (v i), hgm, smul_assoc]
  have hu2 : (fun j => ∑ i, g₂ i j • v' i) = fun j => (b : 𝓞 K) • v' j := by
    funext j
    simp [g₂, Matrix.diagonal_apply, ite_smul]
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb0
  have huli : LinearIndependent K fun j => (b : 𝓞 K) • v' j := by
    have e1 : (fun j => (b : 𝓞 K) • v' j) = fun j => ((Units.mk0 _ hbK : Kˣ) : K) • v' j := by
      funext j
      rw [Units.val_mk0, algebraMap_smul]
    rw [e1]
    exact hv'li.units_smul fun _ => Units.mk0 _ hbK
  have e1 := degreeOfFamily_linearCombination h E hvli g (by rw [hu]; exact huli)
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvE i)) hneV
  have e2 := degreeOfFamily_linearCombination h E hv'li g₂ (by rw [hu2]; exact huli)
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hv'E i)) hneV'
  rw [← e1, ← e2, hu, hu2]

end ReciprocityTheory.GeometryOfNumbersTheory
end

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_isFrame (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ v : Fin (latRank K E) → V, IsFrame K E v := by
  obtain ⟨r, v, hv⟩ := exists_isFullRankFamily_of_fg E hE
  obtain rfl := hv.length_eq_latticeRank
  exact ⟨v, hv⟩

theorem IsFrame.card_eq {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    r = latRank K E := by
  exact hv.length_eq_latticeRank

theorem IsFrame.relIndex_ne_zero {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  exact hv.relIndex_span_frame_ne_zero hE

theorem degreeOfFamily_eq_degreeOfFamily (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r r' : ℕ}
    {v : Fin r → V} {v' : Fin r' → V} (hv : IsFrame K E v) (hv' : IsFrame K E v') :
    degreeOfFamily h E v = degreeOfFamily h E v' := by
  obtain rfl : r = r' := hv.length_eq_latticeRank.trans hv'.length_eq_latticeRank.symm
  exact degreeOfFamily_eq_of_isFullRankFamily h hE hv hv'

theorem arakelovDegree_eq_degreeOfFamily (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ}
    {v : Fin r → V} (hv : IsFrame K E v) : deg h E = degreeOfFamily h E v := by
  have hex : ∃ p : (Σ r : ℕ, Fin r → V), IsFrame K E p.2 := ⟨⟨r, v⟩, hv⟩
  unfold deg
  rw [dif_pos hex]
  exact degreeOfFamily_eq_degreeOfFamily h hE hex.choose_spec hv

theorem deg_of_le (h : HermFam K V) {E' E : Submodule (𝓞 K) V} (hE' : E'.FG) (hE : E.FG)
    (hle : E' ≤ E) (hspan : (E : Set V) ⊆ Submodule.span K (E' : Set V)) :
    deg h E' = deg h E -
      Real.log (E'.toAddSubgroup.relIndex E.toAddSubgroup : ℝ) / finrank ℚ K := by
  obtain ⟨v, hv⟩ := exists_isFrame E' hE'
  have hvE : IsFrame K E v := by
    refine ⟨fun i => hle (hv.1 i), hv.2.1, ?_⟩
    intro x hx
    have hx' := hspan hx
    rw [← hv.ds_spanK_eq] at hx'
    exact hx'
  rw [arakelovDegree_eq_degreeOfFamily h hE' hv, arakelovDegree_eq_degreeOfFamily h hE hvE]
  unfold degreeOfFamily
  have hS : Submodule.span (𝓞 K) (Set.range v) ≤ E' :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hv.1)
  have hmul := AddSubgroup.relIndex_mul_relIndex
    (H := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup) (K := E'.toAddSubgroup)
    (L := E.toAddSubgroup) (fun x hx => hS hx) (fun x hx => hle hx)
  have ha := hv.relIndex_span_frame_ne_zero hE'
  have hc := hvE.relIndex_span_frame_ne_zero hE
  have hb : E'.toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := fun h0 =>
    hc (by rw [← hmul, h0, mul_zero])
  have hlog : Real.log
      ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ) =
      Real.log ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E'.toAddSubgroup : ℝ)
        + Real.log (E'.toAddSubgroup.relIndex E.toAddSubgroup : ℝ) := by
    rw [← hmul, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  rw [hlog]
  ring

end ReciprocityTheory.GeometryOfNumbersTheory
end
